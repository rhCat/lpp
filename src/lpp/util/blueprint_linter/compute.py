"""
COMPUTE units for the L++ Blueprint Linter

These are the pure computation functions that implement linting rules.
All functions are hermetic: input is params dict, output is result dict.
"""

import json
import re
from pathlib import Path
from typing import Any, Dict, List, Set


# =============================================================================
# Finding Types and Severity
# =============================================================================

class Severity:
    ERROR = "error"
    WARNING = "warning"
    INFO = "info"


class RuleCode:
    UNREACHABLE_STATE = "L001"
    DEAD_END_STATE = "L002"
    UNUSED_GATE = "L003"
    UNUSED_ACTION = "L004"
    UNUSED_CONTEXT = "L005"
    ORPHANED_TRANSITION = "L006"
    MISSING_GATE_REF = "L007"
    MISSING_ACTION_REF = "L008"
    DUPLICATE_TRANSITION_ID = "L009"
    NAMING_CONVENTION = "L010"


def make_finding(
    code: str,
    severity: str,
    message: str,
    location: str = None,
    suggestion: str = None
) -> Dict[str, Any]:
    """Create a standardized finding dict."""
    finding = {
        "code": code,
        "severity": severity,
        "message": message
    }
    if location:
        finding["location"] = location
    if suggestion:
        finding["suggestion"] = suggestion
    return finding


# =============================================================================
# Blueprint Loading
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file for linting."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "path": None, "error": "No path provided"}

    try:
        path = Path(path)
        if not path.exists():
            return {"blueprint": None, "path": None,
                    "error": f"File not found: {path}"}

        with open(path) as f:
            raw = json.load(f)

        # Store raw dict for linting (we need access to all fields)
        bp = {
            "id": raw.get("id", "unknown"),
            "name": raw.get("name", "Unknown"),
            "version": raw.get("version", "0.0.0"),
            "description": raw.get("description", ""),
            "states": raw.get("states", {}),
            "transitions": raw.get("transitions", []),
            "gates": raw.get("gates", {}),
            "actions": raw.get("actions", {}),
            "context_schema": raw.get("context_schema", {}),
            "entry_state": raw.get("entry_state"),
            "terminal_states": raw.get("terminal_states", []),
            "display": raw.get("display", {})
        }

        return {"blueprint": bp, "path": str(path), "error": None}
    except json.JSONDecodeError as e:
        return {"blueprint": None, "path": None,
                "error": f"Invalid JSON: {e}"}
    except Exception as e:
        return {"blueprint": None, "path": None, "error": str(e)}


def init_lint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize linting state with empty findings."""
    return {
        "findings": [],
        "summary": {"error": 0, "warning": 0, "info": 0},
        "metrics": {}
    }


# =============================================================================
# Linting Rules
# =============================================================================

def check_unreachable_states(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L001: Detect states that have no incoming transitions.
    Entry state is exempt from this check.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    states = set(bp.get("states", {}).keys())
    entryState = bp.get("entry_state")
    transitions = bp.get("transitions", [])

    # Collect all states that are targets of transitions
    reachable = set()
    for t in transitions:
        toState = t.get("to")
        if toState and toState != "*":
            reachable.add(toState)

    # Entry state is always reachable (it's the start)
    if entryState:
        reachable.add(entryState)

    # Find unreachable states
    unreachable = states - reachable
    for state in sorted(unreachable):
        findings.append(make_finding(
            code=RuleCode.UNREACHABLE_STATE,
            severity=Severity.WARNING,
            message=f"State '{state}' has no incoming transitions",
            location=f"states.{state}",
            suggestion=f"Add a transition to '{state}' or remove it"
        ))

    return {"findings": findings}


def check_dead_end_states(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L002: Detect non-terminal states with no outgoing transitions.
    Terminal states and wildcard transitions are handled specially.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    states = set(bp.get("states", {}).keys())
    terminalStates = set(bp.get("terminal_states", []))
    transitions = bp.get("transitions", [])

    # Collect states with outgoing transitions
    hasOutgoing = set()
    hasWildcard = False
    for t in transitions:
        fromState = t.get("from")
        if fromState == "*":
            hasWildcard = True
        elif fromState:
            hasOutgoing.add(fromState)

    # If there's a wildcard, all states have "outgoing" via wildcard
    if hasWildcard:
        hasOutgoing = states

    # Non-terminal states without outgoing are dead-ends
    nonTerminal = states - terminalStates
    deadEnds = nonTerminal - hasOutgoing

    for state in sorted(deadEnds):
        findings.append(make_finding(
            code=RuleCode.DEAD_END_STATE,
            severity=Severity.WARNING,
            message=f"Non-terminal state '{state}' has no outgoing transitions",
            location=f"states.{state}",
            suggestion=(f"Add transitions from '{state}', mark as terminal, "
                        "or use wildcard transition")
        ))

    return {"findings": findings}


def check_unused_gates(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L003: Detect gates defined but never referenced in transitions.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    definedGates = set(bp.get("gates", {}).keys())
    transitions = bp.get("transitions", [])

    # Collect all gate references from transitions
    usedGates = set()
    for t in transitions:
        # Handle both 'gate' (singular) and 'gates' (array) fields
        gate = t.get("gate")
        if gate:
            usedGates.add(gate)
        gates = t.get("gates", [])
        for g in gates:
            usedGates.add(g)

    # Also check display rules for gate usage
    display = bp.get("display", {})
    for rule in display.get("rules", []):
        gate = rule.get("gate")
        if gate:
            usedGates.add(gate)

    unused = definedGates - usedGates
    for gate in sorted(unused):
        findings.append(make_finding(
            code=RuleCode.UNUSED_GATE,
            severity=Severity.INFO,
            message=f"Gate '{gate}' is defined but never used",
            location=f"gates.{gate}",
            suggestion=f"Use gate '{gate}' in a transition or remove it"
        ))

    return {"findings": findings}


def check_unused_actions(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L004: Detect actions defined but never referenced in transitions.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    definedActions = set(bp.get("actions", {}).keys())
    transitions = bp.get("transitions", [])

    # Collect all action references from transitions
    usedActions = set()
    for t in transitions:
        actions = t.get("actions", [])
        for a in actions:
            usedActions.add(a)

    unused = definedActions - usedActions
    for action in sorted(unused):
        findings.append(make_finding(
            code=RuleCode.UNUSED_ACTION,
            severity=Severity.INFO,
            message=f"Action '{action}' is defined but never used",
            location=f"actions.{action}",
            suggestion=f"Use action '{action}' in a transition or remove it"
        ))

    return {"findings": findings}


def check_unused_context(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L005: Detect context properties never used in gates/actions.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    ctxSchema = bp.get("context_schema", {})
    props = set(ctxSchema.get("properties", {}).keys())

    if not props:
        return {"findings": findings}

    # Collect all property references from gates and actions
    usedProps = set()

    # Check gate expressions
    for gateId, gate in bp.get("gates", {}).items():
        expr = gate.get("expression", "")
        for prop in props:
            if prop in expr:
                usedProps.add(prop)

    # Check action input_map, output_map, target, value_from
    for actId, action in bp.get("actions", {}).items():
        # Check target
        target = action.get("target")
        if target in props:
            usedProps.add(target)

        # Check value_from
        valueFrom = action.get("value_from", "")
        for prop in props:
            if prop in valueFrom:
                usedProps.add(prop)

        # Check input_map values
        inputMap = action.get("input_map", {})
        for v in inputMap.values():
            if isinstance(v, str):
                for prop in props:
                    if prop in v:
                        usedProps.add(prop)

        # Check output_map keys
        outputMap = action.get("output_map", {})
        for k in outputMap.keys():
            if k in props:
                usedProps.add(k)

    # Check display rules
    display = bp.get("display", {})
    for rule in display.get("rules", []):
        template = rule.get("template", "")
        for prop in props:
            if "{" + prop + "}" in template or "{" + prop + "." in template:
                usedProps.add(prop)

    unused = props - usedProps
    for prop in sorted(unused):
        findings.append(make_finding(
            code=RuleCode.UNUSED_CONTEXT,
            severity=Severity.INFO,
            message=f"Context property '{prop}' is defined but never used",
            location=f"context_schema.properties.{prop}",
            suggestion=f"Use property '{prop}' in gates/actions or remove it"
        ))

    return {"findings": findings}


def check_orphaned_transitions(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L006: Detect transitions referencing non-existent states.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    states = set(bp.get("states", {}).keys())
    transitions = bp.get("transitions", [])

    for i, t in enumerate(transitions):
        tid = t.get("id", f"transitions[{i}]")
        fromState = t.get("from")
        toState = t.get("to")

        # Check from state (skip wildcard)
        if fromState and fromState != "*" and fromState not in states:
            findings.append(make_finding(
                code=RuleCode.ORPHANED_TRANSITION,
                severity=Severity.ERROR,
                message=f"Transition '{tid}' references non-existent "
                f"from state '{fromState}'",
                location=f"transitions.{tid}.from",
                suggestion=f"Create state '{fromState}' or fix the reference"
            ))

        # Check to state (skip wildcard)
        if toState and toState != "*" and toState not in states:
            findings.append(make_finding(
                code=RuleCode.ORPHANED_TRANSITION,
                severity=Severity.ERROR,
                message=f"Transition '{tid}' references non-existent "
                f"to state '{toState}'",
                location=f"transitions.{tid}.to",
                suggestion=f"Create state '{toState}' or fix the reference"
            ))

    return {"findings": findings}


def check_missing_gate_refs(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L007: Detect transitions referencing non-existent gates.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    definedGates = set(bp.get("gates", {}).keys())
    transitions = bp.get("transitions", [])

    for i, t in enumerate(transitions):
        tid = t.get("id", f"transitions[{i}]")

        # Handle both 'gate' and 'gates'
        gate = t.get("gate")
        if gate and gate not in definedGates:
            findings.append(make_finding(
                code=RuleCode.MISSING_GATE_REF,
                severity=Severity.ERROR,
                message=f"Transition '{tid}' references non-existent "
                f"gate '{gate}'",
                location=f"transitions.{tid}.gate",
                suggestion=f"Create gate '{gate}' or fix the reference"
            ))

        gates = t.get("gates", [])
        for g in gates:
            if g not in definedGates:
                findings.append(make_finding(
                    code=RuleCode.MISSING_GATE_REF,
                    severity=Severity.ERROR,
                    message=f"Transition '{tid}' references non-existent "
                    f"gate '{g}'",
                    location=f"transitions.{tid}.gates",
                    suggestion=f"Create gate '{g}' or fix the reference"
                ))

    return {"findings": findings}


def check_missing_action_refs(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L008: Detect transitions referencing non-existent actions.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    definedActions = set(bp.get("actions", {}).keys())
    transitions = bp.get("transitions", [])

    for i, t in enumerate(transitions):
        tid = t.get("id", f"transitions[{i}]")
        actions = t.get("actions", [])

        for a in actions:
            if a not in definedActions:
                findings.append(make_finding(
                    code=RuleCode.MISSING_ACTION_REF,
                    severity=Severity.ERROR,
                    message=f"Transition '{tid}' references non-existent "
                    f"action '{a}'",
                    location=f"transitions.{tid}.actions",
                    suggestion=f"Create action '{a}' or fix the reference"
                ))

    return {"findings": findings}


def check_duplicate_ids(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L009: Detect duplicate transition IDs.
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    transitions = bp.get("transitions", [])
    seenIds: Dict[str, int] = {}

    for i, t in enumerate(transitions):
        tid = t.get("id")
        if tid:
            if tid in seenIds:
                findings.append(make_finding(
                    code=RuleCode.DUPLICATE_TRANSITION_ID,
                    severity=Severity.ERROR,
                    message=f"Duplicate transition ID '{tid}' "
                    f"(first at index {seenIds[tid]}, again at {i})",
                    location=f"transitions[{i}]",
                    suggestion=f"Rename one of the transitions with ID '{tid}'"
                ))
            else:
                seenIds[tid] = i

    return {"findings": findings}


def check_naming_conventions(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rule L010: Check naming conventions.
    - IDs should be snake_case
    - Events should be UPPER_CASE
    """
    bp = params.get("blueprint", {})
    findings = list(params.get("findings", []))

    snakeCasePattern = re.compile(r'^[a-z][a-z0-9_]*$')
    upperCasePattern = re.compile(r'^[A-Z][A-Z0-9_]*$')

    # Check state IDs
    for stateId in bp.get("states", {}).keys():
        if not snakeCasePattern.match(stateId):
            findings.append(make_finding(
                code=RuleCode.NAMING_CONVENTION,
                severity=Severity.INFO,
                message=f"State ID '{stateId}' should be snake_case",
                location=f"states.{stateId}",
                suggestion=f"Rename to '{stateId.lower().replace('-', '_')}'"
            ))

    # Check gate IDs
    for gateId in bp.get("gates", {}).keys():
        if not snakeCasePattern.match(gateId):
            findings.append(make_finding(
                code=RuleCode.NAMING_CONVENTION,
                severity=Severity.INFO,
                message=f"Gate ID '{gateId}' should be snake_case",
                location=f"gates.{gateId}",
                suggestion=f"Rename to '{gateId.lower().replace('-', '_')}'"
            ))

    # Check action IDs
    for actionId in bp.get("actions", {}).keys():
        if not snakeCasePattern.match(actionId):
            findings.append(make_finding(
                code=RuleCode.NAMING_CONVENTION,
                severity=Severity.INFO,
                message=f"Action ID '{actionId}' should be snake_case",
                location=f"actions.{actionId}",
                suggestion=f"Rename to '{actionId.lower().replace('-', '_')}'"
            ))

    # Check transition IDs
    for i, t in enumerate(bp.get("transitions", [])):
        tid = t.get("id")
        if tid and not snakeCasePattern.match(tid):
            findings.append(make_finding(
                code=RuleCode.NAMING_CONVENTION,
                severity=Severity.INFO,
                message=f"Transition ID '{tid}' should be snake_case",
                location=f"transitions.{tid}",
                suggestion=f"Rename to '{tid.lower().replace('-', '_')}'"
            ))

    # Check event names
    seenEvents = set()
    for t in bp.get("transitions", []):
        event = t.get("on_event")
        if event and event not in seenEvents:
            seenEvents.add(event)
            if not upperCasePattern.match(event):
                findings.append(make_finding(
                    code=RuleCode.NAMING_CONVENTION,
                    severity=Severity.INFO,
                    message=f"Event '{event}' should be UPPER_CASE",
                    location=f"on_event: {event}",
                    suggestion=f"Rename to '{event.upper().replace('-', '_')}'"
                ))

    return {"findings": findings}


# =============================================================================
# Metrics and Summary
# =============================================================================

def compute_metrics(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compute complexity metrics for the blueprint."""
    bp = params.get("blueprint", {})

    states = bp.get("states", {})
    transitions = bp.get("transitions", [])
    gates = bp.get("gates", {})
    actions = bp.get("actions", {})
    ctxSchema = bp.get("context_schema", {})
    props = ctxSchema.get("properties", {})

    # Count unique events
    events = set()
    for t in transitions:
        event = t.get("on_event")
        if event:
            events.add(event)

    # Cyclomatic complexity: E - N + 2P
    # E = edges (transitions), N = nodes (states), P = connected components (1)
    numStates = len(states)
    numTransitions = len(transitions)
    cyclomaticComplexity = numTransitions - numStates + 2

    metrics = {
        "state_count": numStates,
        "transition_count": numTransitions,
        "gate_count": len(gates),
        "action_count": len(actions),
        "event_count": len(events),
        "context_property_count": len(props),
        "cyclomatic_complexity": max(1, cyclomaticComplexity)
    }

    return {"metrics": metrics}


def compute_summary(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compute summary counts by severity."""
    findings = params.get("findings", [])

    summary = {"error": 0, "warning": 0, "info": 0}
    for f in findings:
        sev = f.get("severity", "info")
        if sev in summary:
            summary[sev] += 1

    return {"summary": summary}


# =============================================================================
# Report Generation
# =============================================================================

def generate_report(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate a formatted lint report."""
    bp = params.get("blueprint", {})
    bpPath = params.get("blueprint_path", "unknown")
    findings = params.get("findings", [])
    summary = params.get("summary", {})
    metrics = params.get("metrics", {})

    lines = []
    lines.append("=" * 70)
    lines.append(f"  L++ Blueprint Linter Report")
    lines.append("=" * 70)
    lines.append("")
    lines.append(
        f"  Blueprint: {bp.get('name', 'Unknown')} (v{bp.get('version', '?')})")
    lines.append(f"  ID: {bp.get('id', 'unknown')}")
    lines.append(f"  Path: {bpPath}")
    lines.append("")

    # Summary
    lines.append("-" * 70)
    lines.append("  SUMMARY")
    lines.append("-" * 70)
    errCount = summary.get("error", 0)
    warnCount = summary.get("warning", 0)
    infoCount = summary.get("info", 0)
    total = errCount + warnCount + infoCount

    if total == 0:
        lines.append("  No issues found. Blueprint is clean!")
    else:
        lines.append(f"  Errors:   {errCount}")
        lines.append(f"  Warnings: {warnCount}")
        lines.append(f"  Info:     {infoCount}")
        lines.append(f"  Total:    {total}")
    lines.append("")

    # Metrics
    lines.append("-" * 70)
    lines.append("  METRICS")
    lines.append("-" * 70)
    lines.append(f"  States:      {metrics.get('state_count', 0)}")
    lines.append(f"  Transitions: {metrics.get('transition_count', 0)}")
    lines.append(f"  Gates:       {metrics.get('gate_count', 0)}")
    lines.append(f"  Actions:     {metrics.get('action_count', 0)}")
    lines.append(f"  Events:      {metrics.get('event_count', 0)}")
    lines.append(
        f"  Context Props: {metrics.get('context_property_count', 0)}")
    lines.append(
        f"  Cyclomatic Complexity: {metrics.get('cyclomatic_complexity', 1)}")
    lines.append("")

    # Findings
    if findings:
        lines.append("-" * 70)
        lines.append("  FINDINGS")
        lines.append("-" * 70)

        # Group by severity
        for severity in [Severity.ERROR, Severity.WARNING, Severity.INFO]:
            sevFindings = [f for f in findings if f.get(
                "severity") == severity]
            if sevFindings:
                icon = {"error": "[E]", "warning": "[W]", "info": "[I]"}
                lines.append("")
                lines.append(f"  {severity.upper()}S ({len(sevFindings)})")
                for f in sevFindings:
                    code = f.get("code", "?")
                    msg = f.get("message", "")
                    loc = f.get("location", "")
                    sug = f.get("suggestion", "")
                    lines.append(f"    {icon[severity]} {code}: {msg}")
                    if loc:
                        lines.append(f"       Location: {loc}")
                    if sug:
                        lines.append(f"       Suggestion: {sug}")
                    lines.append("")

    lines.append("=" * 70)

    return {"report": "\n".join(lines)}


# =============================================================================
# COMPUTE REGISTRY - Maps compute_unit names to functions
# =============================================================================

COMPUTE_REGISTRY = {
    ("lint", "load_blueprint"): load_blueprint,
    ("lint", "init_lint"): init_lint,
    ("lint", "check_unreachable_states"): check_unreachable_states,
    ("lint", "check_dead_end_states"): check_dead_end_states,
    ("lint", "check_unused_gates"): check_unused_gates,
    ("lint", "check_unused_actions"): check_unused_actions,
    ("lint", "check_unused_context"): check_unused_context,
    ("lint", "check_orphaned_transitions"): check_orphaned_transitions,
    ("lint", "check_missing_gate_refs"): check_missing_gate_refs,
    ("lint", "check_missing_action_refs"): check_missing_action_refs,
    ("lint", "check_duplicate_ids"): check_duplicate_ids,
    ("lint", "check_naming_conventions"): check_naming_conventions,
    ("lint", "compute_metrics"): compute_metrics,
    ("lint", "compute_summary"): compute_summary,
    ("lint", "generate_report"): generate_report,
}
