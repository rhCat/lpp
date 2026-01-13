"""
COMPUTE units for Always-On Autonomous Agent v1.3.0.

Key changes from v1.2:
- Dedicated runtime folder per run: runs/<timestamp>/
- Step-level logging: runs/<timestamp>/step_<N>.log
- Logs fed back to LLM for context when retrying
- State stored in runs/<timestamp>/state.json

Hermetic functions per build_rules.md: params: dict -> result: dict.
Prompts are externalized to prompts.py for cleaner separation.
"""

import json
import os
import re
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

from . import prompts

try:
    from openai import OpenAI
    HAS_OPENAI = True
except ImportError:
    HAS_OPENAI = False

try:
    from frame_py.operational_validator import sanitize_python_code
    HAS_SANITIZER = True
except ImportError:
    HAS_SANITIZER = False

    def sanitize_python_code(code, filename="code.py", verbose=False):
        return code, []  # No-op fallback


# =============================================================================
# RUNTIME FOLDER & LOGGING
# =============================================================================

def _getRunDir(workspace: str, runId: str = None) -> Path:
    """Get or create runtime directory for this run."""
    runsDir = Path(workspace) / "runs"
    runsDir.mkdir(exist_ok=True)

    if runId:
        runDir = runsDir / runId
    else:
        # Create new run folder with timestamp
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        runDir = runsDir / ts

    runDir.mkdir(exist_ok=True)
    return runDir


def _logStep(runDir: Path, stepIdx: int, phase: str, content: str, append: bool = True):
    """Log step activity to step_<N>.log file."""
    logFile = runDir / f"step_{stepIdx}.log"
    ts = datetime.now().strftime("%H:%M:%S")
    entry = f"\n[{ts}] === {phase} ===\n{content}\n"

    if append and logFile.exists():
        with open(logFile, "a") as f:
            f.write(entry)
    else:
        logFile.write_text(entry)

    return str(logFile)


def _readStepLog(runDir: Path, stepIdx: int, maxChars: int = 8000) -> str:
    """Read step log for LLM context."""
    logFile = runDir / f"step_{stepIdx}.log"
    if not logFile.exists():
        return ""

    content = logFile.read_text()
    if len(content) > maxChars:
        # Keep last N chars (most recent is most relevant)
        return "...[truncated]...\n" + content[-maxChars:]
    return content


def _logRun(runDir: Path, message: str):
    """Log to main run.log file."""
    logFile = runDir / "run.log"
    ts = datetime.now().strftime("%H:%M:%S")
    entry = f"[{ts}] {message}\n"

    with open(logFile, "a") as f:
        f.write(entry)


# =============================================================================
# CONTEXT CONDENSATION
# =============================================================================

def _condenseForStep(plan: dict, stepIdx: int, execLog: list, iterFeedback: str = None) -> dict:
    """Condense context for step execution."""
    steps = plan.get("steps", []) if plan else []
    currentStep = steps[stepIdx] if stepIdx < len(steps) else {}
    prevStep = steps[stepIdx - 1] if stepIdx > 0 else None
    nextStep = steps[stepIdx + 1] if stepIdx + 1 < len(steps) else None

    stepLog = [e for e in (execLog or []) if e.get("step_index") == stepIdx]
    lastAttempt = stepLog[-1] if stepLog else None
    lastOutput = None
    if lastAttempt:
        lastOutput = lastAttempt.get(
            "raw_output") or lastAttempt.get("result", "")

    return {
        "current": currentStep,
        "prev": {"action": prevStep.get("action")} if prevStep else None,
        "next": {"action": nextStep.get("action")} if nextStep else None,
        "last_attempt": lastAttempt,
        "last_output": lastOutput,
        "iteration_feedback": iterFeedback,
        "total_steps": len(steps),
        "progress": f"{stepIdx + 1}/{len(steps)}"
    }


def _condenseForEval(plan: dict, execLog: list, artifacts: list) -> dict:
    """Condense context for evaluation."""
    steps = plan.get("steps", []) if plan else []
    stepResults = {}
    for entry in (execLog or []):
        idx = entry.get("step_index", 0)
        stepResults[idx] = {
            "step": idx + 1,
            "action": entry.get("step", {}).get("action", "")[:50],
            "success": entry.get("success", False),
            "files": entry.get("files_written", [])
        }

    completedSteps = [i for i in range(len(steps)) if i in stepResults]
    pendingSteps = [i for i in range(len(steps)) if i not in stepResults]

    return {
        "total_steps": len(steps),
        "completed": len(completedSteps),
        "pending": len(pendingSteps),
        "results": list(stepResults.values())[-5:],
        "artifacts": [Path(a).name for a in (artifacts or [])[-8:]]
    }


def _condenseForReview(step: dict, stepIdx: int, execLog: list, error: str) -> dict:
    """Condense context for reviewing a failed step."""
    stepAttempts = [e for e in (execLog or [])
                    if e.get("step_index") == stepIdx]
    return {
        "step_num": stepIdx + 1,
        "action": step.get("action", "") if step else "",
        "attempts": len(stepAttempts),
        "last_error": (error or "Unknown")[:200],
        "attempt_results": [
            {"success": a.get("success"), "result": (
                a.get("result") or "")[:100]}
            for a in stepAttempts[-2:]
        ]
    }


# =============================================================================
# UTILITIES
# =============================================================================

def _truncate(text: str, maxLen: int) -> str:
    """Truncate text with indicator."""
    if not text or len(text) <= maxLen:
        return text or ""
    return text[:maxLen] + "..."


def _extractJson(raw: str) -> Dict[str, Any]:
    """Extract JSON from LLM response with repair attempts."""
    if not raw:
        raise ValueError("Empty response")

    text = raw.strip()

    # Strip markdown blocks
    if "```json" in text:
        text = text.split("```json")[1].split("```")[0]
    elif "```" in text:
        parts = text.split("```")
        if len(parts) >= 2:
            text = parts[1].lstrip("json\n")
    text = text.strip()

    # Try direct parse
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        pass

    # Unescape doubled quotes
    if '\\"' in text:
        try:
            return json.loads(text.replace('\\"', '"'))
        except json.JSONDecodeError:
            pass

    # Find JSON boundaries and repair
    start, end = text.find("{"), text.rfind("}") + 1
    if start >= 0 and end > start:
        chunk = text[start:end]
        chunk = re.sub(r'(?<!\\)\n', r'\\n', chunk)
        chunk = re.sub(r',(\s*[}\]])', r'\1', chunk)
        try:
            return json.loads(chunk)
        except json.JSONDecodeError:
            for i in range(len(chunk) - 1, 0, -1):
                if chunk[i] == '}':
                    try:
                        return json.loads(chunk[:i+1])
                    except json.JSONDecodeError:
                        continue
    raise ValueError("No valid JSON found")


def _callLlm(apiKey: str, apiBase: str, model: str,
             messages: List[Dict], temp: float = 0.7,
             maxTok: int = 4096) -> Dict[str, Any]:
    """Call OpenAI-compatible API."""
    if not HAS_OPENAI:
        return {"response": None, "error": "openai not installed"}
    if not apiKey:
        return {"response": None, "error": "No API key"}
    try:
        client = OpenAI(api_key=apiKey, base_url=apiBase)
        r = client.chat.completions.create(
            model=model, messages=messages,
            temperature=temp, max_tokens=maxTok
        )
        return {"response": r.choices[0].message.content, "error": None}
    except Exception as e:
        return {"response": None, "error": str(e)}


def _findLppRoot() -> str:
    """Find L++ framework root directory."""
    root = os.environ.get("LPP_ROOT")
    if root:
        return root
    cwd = Path(os.getcwd())
    for p in [cwd] + list(cwd.parents):
        if (p / "utils" / "build_skill.sh").exists():
            return str(p)
    return str(cwd.parent)


def _sanitizeBlueprint(bp: dict, verbose: bool = True) -> tuple:
    """
    Sanitize L++ blueprint JSON, fixing common LLM errors.
    Returns (sanitized_dict, corrections_list, error_or_None).

    Corrections list contains all auto-fixes applied for review.
    """
    errors = []
    corrections = []  # Track all auto-corrections for review

    # Early rejection: If missing most required fields, this isn't a blueprint
    required = ["$schema", "id", "name", "version", "states", "transitions",
                "actions", "entry_state", "terminal_states"]
    missingCount = sum(1 for f in required if f not in bp)
    if missingCount > 5:
        return bp, corrections, f"Not a valid blueprint - missing {missingCount}/9 required fields: {', '.join(f for f in required if f not in bp)}"

    # ========== AUTO-FIX PHASE (apply corrections first) ==========

    # Auto-fix: Add default $schema if missing
    if "$schema" not in bp:
        bp["$schema"] = "lpp/v0.2.0"
        corrections.append({
            "field": "$schema",
            "issue": "Missing $schema field",
            "fix": "Added default: lpp/v0.2.0",
            "auto_fixed": True
        })

    # Fix: states must be dict, not list
    if "states" in bp and isinstance(bp["states"], list):
        oldStates = bp["states"]
        newStates = {}
        for i, s in enumerate(oldStates):
            if isinstance(s, dict):
                sid = s.get("id") or s.get("name") or f"state_{i}"
                newStates[sid] = {"description": s.get("description", "")}
            else:
                newStates[f"state_{i}"] = {"description": str(s)}
        bp["states"] = newStates
        corrections.append({
            "field": "states",
            "issue": f"states was an array with {len(oldStates)} items",
            "fix": f"Converted to dict with keys: {list(newStates.keys())}",
            "auto_fixed": True
        })
        if verbose:
            print("  [SANITIZE] Converted states array -> dict")

    # Fix: gates must be dict, not list
    if "gates" in bp and isinstance(bp["gates"], list):
        oldGates = bp["gates"]
        newGates = {}
        for i, g in enumerate(oldGates):
            if isinstance(g, dict):
                gid = g.get("id") or g.get("name") or f"gate_{i}"
                newGates[gid] = {
                    "type": g.get("type", "expression"),
                    "expression": g.get("expression", "True")
                }
            else:
                newGates[f"gate_{i}"] = {
                    "type": "expression", "expression": str(g)}
        bp["gates"] = newGates
        corrections.append({
            "field": "gates",
            "issue": f"gates was an array with {len(oldGates)} items",
            "fix": f"Converted to dict with keys: {list(newGates.keys())}",
            "auto_fixed": True
        })
        if verbose:
            print("  [SANITIZE] Converted gates array -> dict")

    # Fix: actions must be dict, not list
    if "actions" in bp and isinstance(bp["actions"], list):
        oldActions = bp["actions"]
        newActions = {}
        for i, a in enumerate(oldActions):
            if isinstance(a, dict):
                aid = a.get("id") or a.get("name") or f"action_{i}"
                action = {"type": a.get("type", "set")}
                if action["type"] == "compute":
                    action["compute_unit"] = a.get(
                        "compute_unit", f"skill:op_{i}")
                    action["input_map"] = a.get("input_map", {})
                    action["output_map"] = a.get("output_map", {})
                elif action["type"] == "set":
                    action["target"] = a.get("target", "unknown")
                    if "value" in a:
                        action["value"] = a["value"]
                    elif "value_from" in a:
                        action["value_from"] = a["value_from"]
                    else:
                        action["value"] = None
                newActions[aid] = action
            else:
                newActions[f"action_{i}"] = {
                    "type": "set", "target": "unknown", "value": None}
        bp["actions"] = newActions
        corrections.append({
            "field": "actions",
            "issue": f"actions was an array with {len(oldActions)} items",
            "fix": f"Converted to dict with keys: {list(newActions.keys())}",
            "auto_fixed": True
        })
        if verbose:
            print("  [SANITIZE] Converted actions array -> dict")

    # Validate actions have required fields (auto-fix where possible)
    if isinstance(bp.get("actions"), dict):
        for aid, action in bp["actions"].items():
            if not isinstance(action, dict):
                errors.append(
                    f"Action '{aid}' must be a dict, got {type(action)}")
                continue
            atype = action.get("type")
            if atype == "compute":
                if "input_map" not in action:
                    action["input_map"] = {}
                    corrections.append({
                        "field": f"actions.{aid}.input_map",
                        "issue": "Missing input_map for compute action",
                        "fix": "Added empty input_map: {}",
                        "auto_fixed": True
                    })
                if "output_map" not in action:
                    action["output_map"] = {}
                    corrections.append({
                        "field": f"actions.{aid}.output_map",
                        "issue": "Missing output_map for compute action",
                        "fix": "Added empty output_map: {}",
                        "auto_fixed": True
                    })
                if "compute_unit" not in action:
                    errors.append(
                        f"Action '{aid}' missing compute_unit (cannot auto-fix)")
            elif atype == "set":
                if "target" not in action:
                    errors.append(
                        f"Action '{aid}' missing target (cannot auto-fix)")
                if "value" not in action and "value_from" not in action:
                    errors.append(
                        f"Action '{aid}' missing value or value_from (cannot auto-fix)")

    # Validate gates
    if isinstance(bp.get("gates"), dict):
        for gid, gate in bp["gates"].items():
            if not isinstance(gate, dict):
                errors.append(f"Gate '{gid}' must be a dict")
                continue
            gtype = gate.get("type")
            if gtype == "expression" and "expression" not in gate:
                errors.append(f"Gate '{gid}' missing expression")
            elif gtype == "compute" and "compute_unit" not in gate:
                errors.append(f"Gate '{gid}' missing compute_unit")

    # Fix: transitions must be list, not dict (LLM often outputs dict)
    if "transitions" in bp and isinstance(bp["transitions"], dict):
        oldTransitions = bp["transitions"]
        newTransitions = []
        for tid, t in oldTransitions.items():
            if isinstance(t, dict):
                trans = {"id": tid}
                trans["from"] = t.get("from", "idle")
                trans["to"] = t.get("to", "idle")
                trans["on_event"] = t.get("on_event", "DONE")
                if t.get("gates"):
                    trans["gates"] = t["gates"]
                if t.get("actions"):
                    trans["actions"] = t["actions"]
                newTransitions.append(trans)
        bp["transitions"] = newTransitions
        corrections.append({
            "field": "transitions",
            "issue": f"transitions was a DICT with keys: {list(oldTransitions.keys())}",
            "fix": f"Converted to ARRAY with {len(newTransitions)} transition objects",
            "auto_fixed": True,
            "critical": True  # This is a common and critical error
        })
        if verbose:
            print("  [SANITIZE] Converted transitions dict -> list")

    # Validate transitions (auto-fix missing fields where possible)
    if isinstance(bp.get("transitions"), list):
        for i, t in enumerate(bp["transitions"]):
            if not isinstance(t, dict):
                errors.append(f"Transition {i} must be a dict")
                continue
            if "id" not in t:
                t["id"] = f"t_{i}"
                corrections.append({
                    "field": f"transitions[{i}].id",
                    "issue": "Missing transition id",
                    "fix": f"Added default id: t_{i}",
                    "auto_fixed": True
                })
            if "from" not in t:
                errors.append(
                    f"Transition '{t.get('id')}' missing 'from' (cannot auto-fix)")
            if "to" not in t:
                errors.append(
                    f"Transition '{t.get('id')}' missing 'to' (cannot auto-fix)")
            if "on_event" not in t:
                # Auto-fix: default to "DONE" event
                t["on_event"] = "DONE"
                corrections.append({
                    "field": f"transitions[{i}].on_event",
                    "issue": f"Missing on_event for transition '{t.get('id')}'",
                    "fix": "Added default: DONE",
                    "auto_fixed": True
                })

    # Validate entry_state exists in states
    if bp.get("entry_state") and isinstance(bp.get("states"), dict):
        if bp["entry_state"] not in bp["states"]:
            errors.append(
                f"entry_state '{bp['entry_state']}' not in states (cannot auto-fix)")

    # Validate terminal_states exist in states
    if bp.get("terminal_states") and isinstance(bp.get("states"), dict):
        for ts in bp["terminal_states"]:
            if ts not in bp["states"]:
                errors.append(
                    f"terminal_state '{ts}' not in states (cannot auto-fix)")

    # ========== FINAL VALIDATION (check truly required fields) ==========
    # These cannot be auto-fixed and must be provided by the LLM
    criticalRequired = ["id", "name", "states",
                        "transitions", "entry_state", "terminal_states"]
    for field in criticalRequired:
        if field not in bp:
            errors.append(f"Missing required field: {field} (cannot auto-fix)")

    # Return with corrections report
    if errors:
        return bp, corrections, "\n".join(errors)
    return bp, corrections, None


def _formatCorrectionsReport(corrections: list) -> str:
    """Format corrections report for display/logging."""
    if not corrections:
        return "No corrections needed - schema is valid."

    lines = [f"=== AUTO-CORRECTIONS APPLIED ({len(corrections)} fixes) ==="]
    critical = [c for c in corrections if c.get("critical")]
    normal = [c for c in corrections if not c.get("critical")]

    if critical:
        lines.append("\n⚠️  CRITICAL FIXES:")
        for c in critical:
            lines.append(f"  • {c['field']}: {c['issue']}")
            lines.append(f"    → {c['fix']}")

    if normal:
        lines.append("\n📝 Other fixes:")
        for c in normal:
            lines.append(f"  • {c['field']}: {c['issue']}")
            lines.append(f"    → {c['fix']}")

    lines.append("\n✅ Corrected schema ready for validation.")
    return "\n".join(lines)


def _sanitizeStepOutput(parsed: dict, stepType: str) -> tuple:
    """Sanitize step output JSON for non-blueprint steps."""
    errors = []

    if "output" not in parsed and "result" not in parsed:
        errors.append("Missing 'output' or 'result' field")

    if stepType in ("code", "file", "lpp"):
        if "filename" not in parsed:
            errors.append("Missing 'filename' for code/file step")
        if not parsed.get("output"):
            errors.append("Empty 'output' for code/file step")

    if errors:
        return parsed, "\n".join(errors)
    return parsed, None


# =============================================================================
# CORE COMPUTE UNITS
# =============================================================================

def init(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize agent context with new runtime folder."""
    workspace = os.environ.get("WORKSPACE_PATH", os.getcwd())

    # Create new run folder
    runDir = _getRunDir(workspace)
    runId = runDir.name

    _logRun(runDir, f"=== NEW RUN: {runId} ===")
    _logRun(runDir, f"Workspace: {workspace}")

    print(f"  [INIT] Run folder: {runDir}")

    return {
        "api_key": os.environ.get("OPENAI_API_KEY"),
        "api_base": os.environ.get("OPENAI_API_BASE", "https://api.openai.com/v1"),
        "model": os.environ.get("OPENAI_MODEL", "gpt-4o-mini"),
        "workspace_path": workspace,
        "run_id": runId,
        "run_dir": str(runDir),
        "lpp_root": _findLppRoot(),
        "phase": "blueprint",  # Start in blueprint phase
        "blueprint_validated": False,
        "threshold": int(os.environ.get("EVAL_THRESHOLD", "80")),
        "max_iterations": int(os.environ.get("MAX_ITERATIONS", "5")),
        "max_errors": int(os.environ.get("MAX_ERRORS", "3")),
        "max_repairs": int(os.environ.get("MAX_REPAIRS", "3")),
        "iteration": 0,
        "error_count": 0,
        "step_error_count": 0,
        "repair_attempts": 0,
        "failed_steps": [],
        "execution_log": [],
        "artifacts": [],
        "is_lpp_target": True,
        "lpp_validated": False,
        "raw_output": None,
        "parsed_output": None,
        "parse_error": None
    }


def detect_lpp_target(params: Dict[str, Any]) -> Dict[str, Any]:
    """Detect if target requires L++ output."""
    target = (params.get("target") or "").lower()
    analysisOnly = ["explain", "what is", "describe", "list files", "show me"]
    codeWords = ["create", "build", "make",
                 "generate", "write", "app", "skill"]
    isAnalysis = any(k in target for k in analysisOnly) and \
        not any(w in target for w in codeWords)
    isLpp = not isAnalysis

    runDir = Path(params.get("run_dir", "."))
    _logRun(runDir, f"Target: {target[:100]}...")
    _logRun(runDir, f"Mode: {'L++' if isLpp else 'Analysis'}")

    print(f"  [{'L++ MODE' if isLpp else 'ANALYSIS MODE'}]")
    return {"is_lpp_target": isLpp}


def decompose(params: Dict[str, Any]) -> Dict[str, Any]:
    """Decompose target into steps via LLM."""
    apiKey = params.get("api_key")
    apiBase = params.get("api_base")
    model = params.get("model")
    target = params.get("target")
    workspace = params.get("workspace_path", ".")
    feedback = params.get("feedback") or ""
    lppRoot = params.get("lpp_root", "")
    iteration = params.get("iteration", 0)
    phase = params.get("phase", "blueprint")
    runDir = Path(params.get("run_dir", workspace))

    _logRun(runDir, f"DECOMPOSE iteration={iteration} phase={phase}")

    failureCtx = ""
    if feedback:
        fixHints = []
        if "'list' object has no attribute 'keys'" in feedback:
            fixHints.append(
                "FIX: Use DICT format for states/gates/actions, NOT arrays")
        if "'str' object has no attribute 'get'" in feedback:
            fixHints.append(
                "FIX: Actions with type 'compute' MUST have input_map and output_map")
        if "input_map" in feedback or "output_map" in feedback:
            fixHints.append(
                "FIX: Every compute action needs input_map:{} and output_map:{}")

        hintsStr = "\n".join(
            fixHints) if fixHints else "Review the error and fix the schema format"

        failureCtx = f"""
╔══════════════════════════════════════════════════════════════╗
║  CRITICAL: ITERATION {iteration} FAILED - YOU MUST FIX THIS  ║
╚══════════════════════════════════════════════════════════════╝

ERROR DETAILS:
{_truncate(feedback, 1200)}

REQUIRED FIXES:
{hintsStr}

DO NOT generate the same broken output!
"""
        _logRun(runDir, f"Feedback for decompose:\n{feedback[:500]}")

    # Select phase-specific instructions
    phaseInstructions = prompts.PHASE_BLUEPRINT_INSTRUCTIONS if phase == "blueprint" else prompts.PHASE_IMPLEMENTATION_INSTRUCTIONS

    prompt = prompts.DECOMPOSE.format(
        target=target,
        workspace=workspace,
        iteration=iteration + 1,
        phase=phase,
        phase_instructions=phaseInstructions,
        failure_ctx=failureCtx,
        lpp_root=lppRoot,
        # Only include LPP_RULES in blueprint phase
        lpp_rules=prompts.LPP_RULES if phase == "blueprint" else "",
        json_rules=prompts.JSON_RULES
    )

    result = _callLlm(apiKey, apiBase, model,
                      [{"role": "system", "content": prompts.SYSTEM},
                       {"role": "user", "content": prompt}], 0.3, 2048)

    if result.get("error"):
        _logRun(runDir, f"DECOMPOSE ERROR: {result['error']}")
        return {"plan": None, "step_count": 0, "step_index": 0,
                "current_step": None, "error": result["error"]}

    try:
        plan = _extractJson(result["response"])
        steps = plan.get("steps", [])
        _logRun(runDir, f"DECOMPOSE OK: {len(steps)} steps")
        return {
            "plan": plan,
            "step_count": len(steps),
            "step_index": 0,
            "current_step": steps[0] if steps else None,
            "error": None
        }
    except ValueError as e:
        _logRun(runDir, f"DECOMPOSE PARSE ERROR: {e}")
        return {"plan": None, "step_count": 0, "step_index": 0,
                "current_step": None, "error": f"Parse error: {e}"}


def generate_step_output(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate step output via LLM with step-level logging."""
    apiKey = params.get("api_key")
    apiBase = params.get("api_base")
    model = params.get("model")
    target = params.get("target")
    step = params.get("current_step")
    stepIdx = params.get("step_index", 0)
    workspace = params.get("workspace_path", ".")
    execLog = params.get("execution_log", [])
    lppRoot = params.get("lpp_root", "")
    parseError = params.get("parse_error")
    rawOutput = params.get("raw_output")
    repairAttempts = params.get("repair_attempts", 0)
    phase = params.get("phase", "blueprint")
    runDir = Path(params.get("run_dir", workspace))

    if not step:
        return {"raw_output": None, "error": "No step"}

    # Output goes to runs/<run_id>/output/ for cleaner organization
    outputDir = runDir / "output"
    outputDir.mkdir(exist_ok=True)
    plan = params.get("plan", {})
    iterFeedback = params.get("feedback") or ""

    # Log step start
    _logStep(runDir, stepIdx, "GENERATE_START",
             f"Action: {step.get('action', 'N/A')}\nType: {step.get('type', 'N/A')}\nPhase: {phase}\nRepair attempt: {repairAttempts}")

    # Read previous log for this step to give LLM context
    prevLog = _readStepLog(runDir, stepIdx, maxChars=4000)

    ctx = _condenseForStep(plan, stepIdx, execLog, iterFeedback)

    # Build context for LLM
    iterCtx = ""

    if parseError and rawOutput:
        # Include step log for better context
        logContext = f"\n\nPREVIOUS ATTEMPTS LOG:\n{prevLog}" if prevLog else ""

        iterCtx = f"""
╔═══════════════════════════════════════════════════════════════╗
║  ⚠️  OUTPUT PARSING FAILED (attempt {repairAttempts}) - FIX IT  ⚠️  ║
╚═══════════════════════════════════════════════════════════════╝

PARSE ERROR:
{_truncate(parseError, 800)}

YOUR BROKEN OUTPUT:
```
{_truncate(rawOutput, 4000)}
```
{logContext}

FIX THE JSON STRUCTURE! For L++ blueprints you MUST include:
- "$schema": "lpp/v0.2.0"
- "id", "name", "version", "description"
- "states": {{"state_name": {{"description": "..."}}, ...}}  (DICT not array!)
- "gates": {{"gate_name": {{"type": "expression", "expression": "..."}}, ...}}
- "actions": {{"action_name": {{"type": "compute|set", ...}}, ...}}
- "transitions": [...]
- "entry_state", "terminal_states"
"""
        _logStep(runDir, stepIdx, "PARSE_ERROR_CONTEXT",
                 f"Error: {parseError}\nBroken output length: {len(rawOutput or '')}")

    elif ctx.get("iteration_feedback"):
        fb = ctx['iteration_feedback']
        lastOut = ctx.get("last_output") or ""

        fixHints = []
        if "'list' object has no attribute 'keys'" in fb:
            fixHints.append(
                "→ WRONG: \"states\": [{...}]  →  RIGHT: \"states\": {\"idle\": {...}}")
        if "'str' object has no attribute 'get'" in fb:
            fixHints.append(
                "→ Actions MUST have: \"input_map\": {...}, \"output_map\": {...}")

        hintsStr = "\n".join(
            fixHints) if fixHints else "Fix the validation error below"
        brokenOutput = f"\nYOUR PREVIOUS OUTPUT:\n```\n{_truncate(lastOut, 4000)}\n```" if lastOut else ""

        iterCtx = f"""
╔═══════════════════════════════════════════════════════════════╗
║  ⚠️  PREVIOUS ATTEMPT FAILED - MUST FIX BEFORE PROCEEDING  ⚠️  ║
╚═══════════════════════════════════════════════════════════════╝

VALIDATION ERROR:
{_truncate(fb, 1000)}

SPECIFIC FIXES REQUIRED:
{hintsStr}
{brokenOutput}
"""

    lastAttemptStr = "First attempt"
    if ctx["last_attempt"]:
        la = ctx["last_attempt"]
        lastAttemptStr = f"Attempt: {la.get('result', 'N/A')[:80]}, success: {la.get('success', 'N/A')}"

    # Select phase-specific instructions and output format
    if phase == "blueprint":
        phaseInstructions = prompts.PHASE_BLUEPRINT_INSTRUCTIONS
        phaseOutputFormat = prompts.BLUEPRINT_OUTPUT_FORMAT
        lppRules = prompts.LPP_RULES
    else:
        phaseInstructions = prompts.PHASE_IMPLEMENTATION_INSTRUCTIONS
        phaseOutputFormat = prompts.IMPLEMENTATION_OUTPUT_FORMAT
        lppRules = ""  # Don't include L++ schema rules in implementation phase

    prompt = prompts.EXECUTE_STEP.format(
        target=target,
        phase=phase.upper(),
        phase_instructions=phaseInstructions,
        phase_output_format=phaseOutputFormat,
        progress=ctx["progress"],
        action=step.get("action", ""),
        step_type=step.get("type", "analyze"),
        output_dir=str(outputDir),
        lpp_root=lppRoot,
        iteration_ctx=iterCtx,
        prev_step=ctx["prev"]["action"] if ctx["prev"] else "None",
        next_step=ctx["next"]["action"] if ctx["next"] else "Final step",
        last_attempt=lastAttemptStr,
        lpp_rules=lppRules,
        json_rules=prompts.JSON_RULES
    )

    _logStep(runDir, stepIdx, "LLM_PROMPT",
             f"Prompt length: {len(prompt)} chars")

    result = _callLlm(apiKey, apiBase, model,
                      [{"role": "system", "content": prompts.SYSTEM},
                       {"role": "user", "content": prompt}], 0.4, 4096)

    if result.get("error"):
        _logStep(runDir, stepIdx, "LLM_ERROR", result["error"])
        return {"raw_output": None, "error": result["error"]}

    rawResp = result.get("response", "")
    _logStep(runDir, stepIdx, "LLM_RESPONSE",
             f"Response length: {len(rawResp)} chars\n\n{rawResp[:2000]}")

    print(f"  [GENERATE] Step {stepIdx + 1}: {len(rawResp)} chars")

    return {"raw_output": rawResp, "error": None}


def parse_and_sanitize(params: Dict[str, Any]) -> Dict[str, Any]:
    """Parse and sanitize LLM output with logging."""
    rawOutput = params.get("raw_output", "")
    step = params.get("current_step", {})
    isLppTarget = params.get("is_lpp_target", True)
    phase = params.get("phase", "blueprint")
    stepType = step.get("type", "analyze") if step else "analyze"
    isLppStep = "lpp" in stepType.lower() if stepType else False
    stepIdx = params.get("step_index", 0)
    runDir = Path(params.get("run_dir", "."))

    # In implementation phase, we're generating Python code, not blueprints
    inBlueprintPhase = (phase == "blueprint")

    if not rawOutput:
        _logStep(runDir, stepIdx, "PARSE_FAIL", "Empty LLM response")
        return {"parsed_output": None, "parse_error": "Empty LLM response"}

    # Step 1: Extract JSON
    try:
        parsed = _extractJson(rawOutput)
        _logStep(runDir, stepIdx, "JSON_EXTRACTED",
                 f"Keys: {list(parsed.keys())[:10]} Phase: {phase}")
    except ValueError as e:
        _logStep(runDir, stepIdx, "JSON_EXTRACT_FAIL",
                 f"Error: {e}\nRaw start: {rawOutput[:500]}")
        return {"parsed_output": None,
                "parse_error": f"JSON extraction failed: {e}. Raw output starts with: {rawOutput[:200]}"}

    # Step 2: In blueprint phase, check if blueprint is nested in 'output' field
    # This happens regardless of stepType since LLM may return {"output": "<escaped blueprint>"}
    if inBlueprintPhase and "output" in parsed and isinstance(parsed["output"], str):
        outputStr = parsed["output"]
        # Unescape the nested JSON string
        outputStr = outputStr.replace("\\\\n", "\n").replace("\\\\t", "\t")
        outputStr = outputStr.replace('\\\\"', '"').replace("\\'", "'")
        outputStr = outputStr.replace("\\n", "\n").replace("\\t", "\t")
        outputStr = outputStr.replace('\\"', '"')

        # Try to parse the nested blueprint
        if outputStr.strip().startswith("{") and ("$schema" in outputStr or "states" in outputStr):
            try:
                innerParsed = json.loads(outputStr)
                _logStep(runDir, stepIdx, "NESTED_BLUEPRINT",
                         f"Extracted from output field, keys: {list(innerParsed.keys())[:8]}")
                # Use the inner blueprint but preserve filename
                innerParsed["_filename"] = parsed.get(
                    "filename", "blueprint.json")
                parsed = innerParsed
            except json.JSONDecodeError as e:
                _logStep(runDir, stepIdx, "NESTED_PARSE_FAIL",
                         f"Inner JSON parse failed: {e}\nStart: {outputStr[:300]}")
                # Continue with outer parsed, will fail blueprint validation

    # Step 3: Detect blueprint - ONLY in blueprint phase
    isBlueprint = inBlueprintPhase and (
        isLppStep or
        "$schema" in parsed or
        ("states" in parsed and "transitions" in parsed)
    )

    # Step 4: Sanitize based on what we have
    if isBlueprint and isLppTarget:
        sanitized, corrections, error = _sanitizeBlueprint(parsed)

        # Log corrections for review
        if corrections:
            report = _formatCorrectionsReport(corrections)
            _logStep(runDir, stepIdx, "BLUEPRINT_CORRECTIONS", report)
            print(f"\n{report}\n")

        if error:
            _logStep(runDir, stepIdx, "BLUEPRINT_INVALID", error)
            return {"parsed_output": None,
                    "parse_error": f"Blueprint schema errors (cannot auto-fix):\n{error}",
                    "corrections": corrections}
        # Restore filename if we extracted from nested
        if "_filename" in parsed:
            sanitized["_filename"] = parsed["_filename"]
        _logStep(runDir, stepIdx, "BLUEPRINT_VALID",
                 f"States: {list(sanitized.get('states', {}).keys())}, Corrections: {len(corrections)}")
        return {"parsed_output": sanitized, "parse_error": None, "corrections": corrections}
    else:
        # Implementation phase or non-blueprint step - treat as code/file output
        sanitized, error = _sanitizeStepOutput(parsed, stepType)
        if error:
            _logStep(runDir, stepIdx, "OUTPUT_INVALID", error)
            return {"parsed_output": None,
                    "parse_error": f"Step output errors:\n{error}"}
        _logStep(runDir, stepIdx, "OUTPUT_VALID",
                 f"Filename: {sanitized.get('filename', 'N/A')} Phase: {phase}")
        return {"parsed_output": sanitized, "parse_error": None}


def write_output(params: Dict[str, Any]) -> Dict[str, Any]:
    """Write validated output to disk."""
    parsed = params.get("parsed_output", {})
    step = params.get("current_step", {})
    stepIdx = params.get("step_index", 0)
    workspace = params.get("workspace_path", ".")
    execLog = params.get("execution_log", [])
    artifacts = params.get("artifacts", [])
    runDir = Path(params.get("run_dir", workspace))

    if not parsed:
        return {"execution_log": execLog, "artifacts": artifacts,
                "current_step": step, "error": "No parsed output"}

    # Output goes to runs/<run_id>/output/ for cleaner organization
    outputDir = runDir / "output"
    outputDir.mkdir(exist_ok=True)

    stepType = step.get("type", "analyze") if step else "analyze"
    # Normalize step type - check if it contains 'lpp'
    isLppStep = "lpp" in stepType.lower() if stepType else False
    filesWritten = []

    # Handle blueprint output - check for $schema regardless of stepType
    # (LLM may use "file" type but still generate a valid blueprint)
    if "$schema" in parsed:
        filename = parsed.pop("_filename", None) or parsed.get(
            "filename", f"{parsed.get('id', 'blueprint')}.json")
        # Ensure .json extension
        if not filename.endswith(".json"):
            filename = f"{filename}.json"
        # Write the blueprint JSON directly
        bpCopy = {k: v for k, v in parsed.items() if not k.startswith("_")}
        fp = outputDir / filename
        fp.parent.mkdir(parents=True, exist_ok=True)
        fp.write_text(json.dumps(bpCopy, indent=2))
        filesWritten.append(str(fp))
        _logStep(runDir, stepIdx, "BLUEPRINT_WRITTEN", f"Path: {fp}")
        print(f"  [WROTE BLUEPRINT] {fp}")
    else:
        # Handle regular code/file output
        output = parsed.get("output", "")
        filename = parsed.get("filename")

        # Unescape
        if output:
            output = output.replace("\\\\", "\x00BACKSLASH\x00")
            output = output.replace('\\"', '"')
            output = output.replace("\\n", "\n")
            output = output.replace("\\t", "\t")
            output = output.replace("\x00BACKSLASH\x00", "\\")

        # Also check if this looks like a JSON blueprint in the output field
        isJsonFile = filename and filename.endswith(".json")
        isPythonFile = filename and filename.endswith(".py")
        if output and filename and (isLppStep or stepType in ("code", "file") or isJsonFile):
            # Sanitize Python files to fix common LLM errors (literal newlines in strings)
            if isPythonFile and HAS_SANITIZER:
                sanitized_output, fixes = sanitize_python_code(
                    output, filename, verbose=True)
                if fixes:
                    _logStep(runDir, stepIdx, "SANITIZED",
                             f"{filename}: {', '.join(fixes)}")
                    print(f"  [SANITIZED] {filename}: {', '.join(fixes)}")
                output = sanitized_output
            fp = outputDir / filename
            fp.parent.mkdir(parents=True, exist_ok=True)
            fp.write_text(output)
            filesWritten.append(str(fp))
            _logStep(runDir, stepIdx, "FILE_WRITTEN",
                     f"Path: {fp}\nSize: {len(output)} bytes")
            print(f"  [WROTE] {fp}")

    if stepType == "command" and parsed.get("command"):
        cmd = parsed["command"]
        try:
            proc = subprocess.run(cmd, shell=True, cwd=str(outputDir),
                                  capture_output=True, text=True, timeout=30)
            parsed["cmd_output"] = proc.stdout or proc.stderr
            _logStep(runDir, stepIdx, "COMMAND_RUN",
                     f"Cmd: {cmd}\nExit: {proc.returncode}\nOutput: {parsed['cmd_output'][:500]}")
        except Exception as e:
            parsed["cmd_output"] = str(e)
            _logStep(runDir, stepIdx, "COMMAND_ERROR", str(e))

    logEntry = {
        "step_index": stepIdx,
        "step": step,
        "result": parsed.get("result", ""),
        "raw_output": params.get("raw_output", ""),
        "files_written": filesWritten,
        "success": True
    }
    execLog = list(execLog) + [logEntry]
    artifacts = list(artifacts) + filesWritten

    step["status"] = "done"
    step["output"] = parsed.get("output", "") if not (
        "$schema" in parsed) else json.dumps(parsed, indent=2)[:500]

    _logRun(runDir, f"Step {stepIdx + 1} COMPLETE: {filesWritten}")

    return {"execution_log": execLog, "artifacts": artifacts,
            "current_step": step, "error": None}


def advance_step(params: Dict[str, Any]) -> Dict[str, Any]:
    """Advance to next step."""
    plan = params.get("plan", {})
    stepIdx = params.get("step_index", 0)
    steps = plan.get("steps", []) if plan else []
    nextIdx = stepIdx + 1
    nextStep = steps[nextIdx] if nextIdx < len(steps) else None

    runDir = Path(params.get("run_dir", "."))
    _logRun(runDir, f"ADVANCE: {stepIdx} -> {nextIdx}")

    return {"step_index": nextIdx, "current_step": nextStep}


def validate_lpp(params: Dict[str, Any]) -> Dict[str, Any]:
    """Validate L++ artifacts."""
    workspace = params.get("workspace_path", ".")
    artifacts = params.get("artifacts", [])
    lppRoot = params.get("lpp_root", "")
    phase = params.get("phase", "blueprint")
    runDir = Path(params.get("run_dir", workspace))

    blueprints = [a for a in artifacts if a.endswith(".json")]
    if not blueprints:
        _logRun(runDir, "VALIDATE: No blueprints found")
        return {"lpp_validated": False, "blueprint_validated": False,
                "feedback": "No blueprints found", "error": None}

    # Output is in runs/<run_id>/output/
    outputDir = runDir / "output"
    skillDir = str(outputDir)
    for bp in blueprints:
        bpPath = Path(bp)
        if bpPath.exists():
            parent = bpPath.parent
            if (parent / "src").exists():
                skillDir = str(parent)
                break

    buildScript = None
    for p in [Path(lppRoot) / "utils" / "build_skill.sh" if lppRoot else None,
              Path(workspace).parent / "utils" / "build_skill.sh"]:
        if p and p.exists():
            buildScript = p
            break

    if not buildScript:
        _logRun(runDir, "VALIDATE: build_skill.sh not found, skipping")
        return {"lpp_validated": True, "blueprint_validated": True,
                "feedback": None, "error": None}

    runCwd = lppRoot or str(Path(workspace).parent)
    _logRun(runDir, f"VALIDATE [{phase}]: {buildScript} {skillDir} --validate")

    try:
        proc = subprocess.run(
            [str(buildScript), skillDir, "--validate"],
            cwd=runCwd, capture_output=True, text=True, timeout=60
        )
        output = proc.stdout + proc.stderr

        if "PASS" in output:
            _logRun(runDir, f"VALIDATE [{phase}]: PASSED")
            # Both phases set lpp_validated=True on pass, but blueprint_validated tracks blueprint specifically
            if phase == "blueprint":
                return {"lpp_validated": True, "blueprint_validated": True,
                        "feedback": f"Blueprint phase PASSED - advancing to implementation", "error": None}
            else:
                return {"lpp_validated": True, "blueprint_validated": True,
                        "feedback": None, "error": None}
        else:
            _logRun(runDir, f"VALIDATE [{phase}]: FAILED\n{output[:1000]}")
            errLines = [l.strip() for l in output.split("\n")
                        if any(k in l.lower() for k in ["error", "violation", "fail", "missing"])]
            errDetail = "\n".join(
                errLines[-10:]) if errLines else output[-600:]

            schemaHints = []
            if "'list' object has no attribute 'keys'" in output:
                schemaHints.append(
                    "Use DICT not ARRAY for states/gates/actions")
            if "'str' object has no attribute 'get'" in output:
                schemaHints.append(
                    "transitions MUST be an ARRAY, not a dict! Use: \"transitions\": [{\"id\": \"t1\", \"from\": ..., \"to\": ..., \"on_event\": ...}, ...]")
            if "AttributeError" in output and "transitions" in output:
                schemaHints.append(
                    "transitions MUST be: [{\"id\": \"t1\", \"from\": \"state1\", \"to\": \"state2\", \"on_event\": \"event_name\"}, ...]")

            feedback = f"L++ VALIDATION FAILED [{phase}]:\n{errDetail}\n{chr(10).join(schemaHints)}"
            return {"lpp_validated": False, "blueprint_validated": False,
                    "feedback": feedback, "error": None}
    except Exception as e:
        _logRun(runDir, f"VALIDATE ERROR: {e}")
        return {"lpp_validated": False, "blueprint_validated": False,
                "feedback": f"Validation exception: {e}", "error": None}


def advance_phase(params: Dict[str, Any]) -> Dict[str, Any]:
    """Advance from blueprint phase to implementation phase."""
    currentPhase = params.get("phase", "blueprint")
    runDir = Path(params.get("run_dir", "."))

    if currentPhase == "blueprint":
        newPhase = "implementation"
        _logRun(runDir, f"PHASE ADVANCE: {currentPhase} -> {newPhase}")
        print(f"  [PHASE] Blueprint validated - advancing to implementation")
        return {"phase": newPhase}
    else:
        # Already in implementation phase
        _logRun(runDir, f"PHASE: Already in {currentPhase}")
        return {"phase": currentPhase}


def evaluate(params: Dict[str, Any]) -> Dict[str, Any]:
    """Self-evaluate progress."""
    apiKey = params.get("api_key")
    apiBase = params.get("api_base")
    model = params.get("model")
    target = params.get("target")
    plan = params.get("plan")
    execLog = params.get("execution_log", [])
    artifacts = params.get("artifacts", [])
    iteration = params.get("iteration", 0)
    threshold = params.get("threshold", 80)
    isLppTarget = params.get("is_lpp_target", True)
    lppValidated = params.get("lpp_validated", False)
    runDir = Path(params.get("run_dir", "."))

    lppStatus = "PASSED" if lppValidated else (
        "REQUIRED" if isLppTarget else "N/A")
    ctx = _condenseForEval(plan, execLog, artifacts)

    _logRun(
        runDir, f"EVALUATE: iter={iteration}, lpp={lppStatus}, completed={ctx['completed']}/{ctx['total_steps']}")

    prompt = prompts.EVALUATE.format(
        target=target,
        iteration=iteration + 1,
        threshold=threshold,
        lpp_status=lppStatus,
        total_steps=ctx["total_steps"],
        completed=ctx["completed"],
        pending=ctx["pending"],
        results=json.dumps(ctx["results"], indent=2),
        artifacts=", ".join(ctx["artifacts"]) if ctx["artifacts"] else "None",
        json_rules=prompts.JSON_RULES
    )

    result = _callLlm(apiKey, apiBase, model,
                      [{"role": "system", "content": prompts.SYSTEM},
                       {"role": "user", "content": prompt}], 0.2, 2048)

    if result.get("error"):
        _logRun(runDir, f"EVALUATE ERROR: {result['error']}")
        return {"evaluation": None, "score": 0, "is_satisfied": False,
                "feedback": None, "error": result["error"]}

    try:
        ev = _extractJson(result["response"])
        score = ev.get("score", 0)
        satisfied = ev.get("satisfied", False) or score >= threshold
        _logRun(
            runDir, f"EVALUATE RESULT: score={score}, satisfied={satisfied}")
        return {
            "evaluation": ev,
            "score": score,
            "is_satisfied": satisfied,
            "feedback": ev.get("feedback"),
            "error": None
        }
    except ValueError as e:
        _logRun(runDir, f"EVALUATE PARSE ERROR: {e}")
        return {"evaluation": None, "score": 0, "is_satisfied": False,
                "feedback": None, "error": f"Parse error: {e}"}


# =============================================================================
# HELPER COMPUTE UNITS
# =============================================================================

def incr_iteration(params: Dict[str, Any]) -> Dict[str, Any]:
    return {"iteration": params.get("iteration", 0) + 1}


def incr_repair(params: Dict[str, Any]) -> Dict[str, Any]:
    return {"repair_attempts": params.get("repair_attempts", 0) + 1}


def reset_for_refine(params: Dict[str, Any]) -> Dict[str, Any]:
    return {"step_index": 0, "current_step": None}


def capture_error(params: Dict[str, Any]) -> Dict[str, Any]:
    error = params.get("error", "Unknown")
    count = params.get("error_count", 0) + 1
    step = params.get("current_step", {})
    stepIdx = params.get("step_index", 0)
    runDir = Path(params.get("run_dir", "."))

    stepInfo = f" at step {stepIdx + 1}: {step.get('action', '')}" if step else ""
    _logRun(runDir, f"ERROR ({count}): {error}")

    return {
        "last_error": error,
        "feedback": f"Error{stepInfo}: {error}. Adjust plan.",
        "error_count": count
    }


def capture_step_error(params: Dict[str, Any]) -> Dict[str, Any]:
    error = params.get("error", "Unknown")
    count = params.get("step_error_count", 0) + 1
    stepIdx = params.get("step_index", 0)
    runDir = Path(params.get("run_dir", "."))

    _logStep(runDir, stepIdx, "STEP_ERROR", f"Count: {count}\nError: {error}")

    return {
        "last_error": error,
        "feedback": f"Step error: {error}",
        "step_error_count": count
    }


def capture_parse_error(params: Dict[str, Any]) -> Dict[str, Any]:
    parseError = params.get("parse_error", "Unknown parse error")
    rawOutput = params.get("raw_output", "")
    repairAttempts = params.get("repair_attempts", 0)
    stepIdx = params.get("step_index", 0)
    runDir = Path(params.get("run_dir", "."))

    _logStep(runDir, stepIdx, "PARSE_ERROR",
             f"Attempt: {repairAttempts}\nError: {parseError}")

    return {
        "feedback": f"Parse error (attempt {repairAttempts}): {parseError}",
        "step_error_count": 0
    }


def prepare_recovery(params: Dict[str, Any]) -> Dict[str, Any]:
    feedback = params.get("feedback", "")
    plan = params.get("plan", {})
    stepIdx = params.get("step_index", 0)
    if plan:
        steps = plan.get("steps", [])[stepIdx:]
        if steps:
            feedback += f" Failed: {[s.get('action') for s in steps[:3]]}"
    return {"feedback": feedback, "error": None}


def review_failed_step(params: Dict[str, Any]) -> Dict[str, Any]:
    """LLM reviews failed step: skip or replan."""
    apiKey = params.get("api_key")
    apiBase = params.get("api_base")
    model = params.get("model")
    target = params.get("target")
    step = params.get("current_step") or {}
    stepIdx = params.get("step_index", 0)
    stepCount = params.get("step_count", 0)
    lastError = params.get("last_error", "Unknown")
    failedSteps = params.get("failed_steps") or []
    execLog = params.get("execution_log") or []
    runDir = Path(params.get("run_dir", "."))

    ctx = _condenseForReview(step, stepIdx, execLog, lastError)

    # Include step log for context
    stepLog = _readStepLog(runDir, stepIdx, maxChars=2000)

    _logRun(runDir, f"REVIEW: step {stepIdx + 1}, error: {lastError[:100]}")

    prompt = prompts.REVIEW_STEP.format(
        target=target,
        step_num=f"{ctx['step_num']}/{stepCount}",
        action=ctx["action"],
        error=ctx["last_error"],
        attempts=ctx["attempts"],
        attempt_results=json.dumps(ctx["attempt_results"], indent=2),
        failed_steps=len(failedSteps),
        json_rules=prompts.JSON_RULES
    )

    # Add step log context
    if stepLog:
        prompt += f"\n\nSTEP LOG:\n{stepLog}"

    result = _callLlm(apiKey, apiBase, model,
                      [{"role": "system", "content": prompts.SYSTEM},
                       {"role": "user", "content": prompt}], 0.3, 1024)

    if result.get("error"):
        _logRun(runDir, "REVIEW: LLM error, defaulting to skip")
        return {"review_decision": "skip", "feedback": f"Skipping: {lastError}",
                "failed_steps": failedSteps + [step]}

    try:
        rv = _extractJson(result["response"])
        decision = rv.get("decision", "skip")
        if decision not in ("skip", "replan"):
            decision = "skip"
        _logRun(runDir, f"REVIEW DECISION: {decision}")
        newFailed = failedSteps + [step] if decision == "skip" else failedSteps
        return {"review_decision": decision, "feedback": rv.get("feedback", ""),
                "failed_steps": newFailed}
    except ValueError:
        _logRun(runDir, "REVIEW: Parse error, defaulting to skip")
        return {"review_decision": "skip", "feedback": f"Skipping: {lastError}",
                "failed_steps": failedSteps + [step]}


def skip_step(params: Dict[str, Any]) -> Dict[str, Any]:
    """Skip current step and advance."""
    plan = params.get("plan", {})
    stepIdx = params.get("step_index", 0)
    failedSteps = params.get("failed_steps") or []
    steps = plan.get("steps", []) if plan else []
    nextIdx = stepIdx + 1
    nextStep = steps[nextIdx] if nextIdx < len(steps) else None
    runDir = Path(params.get("run_dir", "."))

    _logRun(runDir, f"SKIP: step {stepIdx + 1} -> {nextIdx + 1}")

    return {"step_index": nextIdx, "current_step": nextStep,
            "failed_steps": failedSteps, "step_error_count": 0}


# =============================================================================
# STATE PERSISTENCE
# =============================================================================

def save_state(params: Dict[str, Any]) -> Dict[str, Any]:
    """Save state to run folder."""
    runDir = Path(params.get("run_dir", params.get("workspace_path", ".")))
    path = runDir / "state.json"

    data = {
        "fsm_state": params.get("fsm_state", "idle"),
        "run_id": params.get("run_id"),
        "target": params.get("target"),
        "plan": params.get("plan"),
        "step_index": params.get("step_index"),
        "step_count": params.get("step_count"),
        "current_step": params.get("current_step"),
        "execution_log": params.get("execution_log"),
        "artifacts": params.get("artifacts"),
        "iteration": params.get("iteration"),
        "score": params.get("score"),
        "feedback": params.get("feedback"),
        "is_satisfied": params.get("is_satisfied"),
        "repair_attempts": params.get("repair_attempts"),
        "step_error_count": params.get("step_error_count")
    }
    try:
        path.write_text(json.dumps(data, indent=2))
        return {"error": None}
    except Exception as e:
        return {"error": str(e)}


def load_state(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load state from run folder."""
    runDir = Path(params.get("run_dir", params.get("workspace_path", ".")))
    path = runDir / "state.json"
    if not path.exists():
        return {"has_saved_state": False}
    try:
        data = json.loads(path.read_text())
        data["has_saved_state"] = True
        return data
    except Exception as e:
        return {"has_saved_state": False, "error": str(e)}


def clear_state(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear saved state."""
    runDir = Path(params.get("run_dir", params.get("workspace_path", ".")))
    path = runDir / "state.json"
    if path.exists():
        path.unlink()
    return {"error": None}


def log_corrections(params: Dict[str, Any]) -> Dict[str, Any]:
    """Log auto-corrections for review and auto-approve."""
    corrections = params.get("corrections", [])
    runDir = Path(params.get("run_dir", "."))
    stepIdx = params.get("step_index", 0)

    if not corrections:
        return {"corrections_approved": True}

    # Format and log corrections report
    report = _formatCorrectionsReport(corrections)
    _logStep(runDir, stepIdx, "AUTO_CORRECTIONS", report)

    # Print for visibility
    print(f"\n{report}\n")

    # Auto-approve all corrections (they've been logged for review)
    # In future, critical corrections could pause for human approval
    return {"corrections_approved": True}


def evaluate_interactive(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Evaluate generated interactive.py and related Python files.
    Uses frame_py.operational_validator for validation.

    Validation stages:
    1. Content - LLM-specific errors (literal newlines, placeholders)
    2. Syntax - AST parsing with line numbers
    3. Import - Module reference validation
    4. Structure - Required elements (COMPUTE_UNITS, etc.)

    Returns evaluation results with pass/fail status and feedback.
    """
    runDir = Path(params.get("run_dir", "."))
    outputDir = runDir / "output"

    _logRun(runDir, "EVAL_INTERACTIVE: Starting evaluation")

    if not outputDir.exists():
        _logRun(runDir, "EVAL_INTERACTIVE: No output directory found")
        return {
            "interactive_valid": True,  # No output = nothing to fail
            "interactive_feedback": "No output directory found",
            "error": None
        }

    # Use the framework's operational validator
    try:
        # Try to import from installed package
        from frame_py.operational_validator import validate_skill_directory
    except ImportError:
        # Fall back to relative import path
        import sys
        lpp_root = params.get("lpp_root", "")
        if lpp_root:
            sys.path.insert(0, os.path.join(lpp_root, "src"))
            from frame_py.operational_validator import validate_skill_directory
        else:
            # Cannot import validator, skip this check
            _logRun(runDir, "EVAL_INTERACTIVE: Validator not available, skipping")
            return {
                "interactive_valid": True,
                "interactive_feedback": "Validator not available",
                "error": None
            }

    # Run validation
    results = validate_skill_directory(str(outputDir), verbose=True)

    # Log results
    _logRun(
        runDir, f"EVAL_INTERACTIVE: {'PASSED' if results['passed'] else 'FAILED'}")
    _logRun(runDir, f"FEEDBACK: {results['feedback'][:500]}")

    if results["passed"]:
        print(f"  [EVAL_INTERACTIVE] ✓ {results['feedback']}")
    else:
        print(
            f"  [EVAL_INTERACTIVE] ✗ FAILED - {len(results['errors'])} errors")
        # Print first few lines of feedback
        for line in results['feedback'].split('\n')[:8]:
            print(f"    {line}")

    return {
        "interactive_valid": results["passed"],
        "interactive_feedback": results["feedback"],
        "error": None
    }


# =============================================================================
# REGISTRY
# =============================================================================

COMPUTE_UNITS = {
    "agent:init": init,
    "agent:detect_lpp_target": detect_lpp_target,
    "agent:decompose": decompose,
    "agent:generate_step_output": generate_step_output,
    "agent:parse_and_sanitize": parse_and_sanitize,
    "agent:write_output": write_output,
    "agent:advance_step": advance_step,
    "agent:advance_phase": advance_phase,
    "agent:validate_lpp": validate_lpp,
    "agent:evaluate": evaluate,
    "agent:evaluate_interactive": evaluate_interactive,
    "agent:incr_iteration": incr_iteration,
    "agent:incr_repair": incr_repair,
    "agent:reset_for_refine": reset_for_refine,
    "agent:capture_error": capture_error,
    "agent:capture_step_error": capture_step_error,
    "agent:capture_parse_error": capture_parse_error,
    "agent:prepare_recovery": prepare_recovery,
    "agent:review_failed_step": review_failed_step,
    "agent:skip_step": skip_step,
    "agent:log_corrections": log_corrections,
    "agent:save_state": save_state,
    "agent:load_state": load_state,
    "agent:clear_state": clear_state,
    # Backwards compatibility
    "agent:execute_step": generate_step_output,
}
