"""
Policy Generator Compute Functions

Generate L++ policies from decoded blueprints or source repositories.
"""

import json
import os
import subprocess
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Any, Optional


def analyzeSource(params: dict) -> dict:
    """
    Analyze source path and run appropriate decoders.

    Supports:
    - Directory path: Run logic_decoder on all .py files
    - JSON file: Load as decoded blueprint
    - Git URL: Clone and analyze
    """
    source_path = params.get("source_path")
    source_repo = params.get("source_repo")
    source_type = params.get("source_type") or "auto"  # Handle None value

    if not source_path:
        return {"error": "source_path required"}

    path = Path(source_path)
    decoded_blueprints = []
    function_analysis = {}
    provenance = {
        "extracted_date": datetime.now().isoformat()[:10],
        "extracted_by": "lpp util policy_generator"
    }

    # Detect source type
    if source_type == "auto":
        if path.suffix == ".json":
            source_type = "decoded_json"
        elif path.is_dir():
            source_type = "repo"
        elif str(source_path).startswith("http"):
            source_type = "git_url"
        else:
            source_type = "repo"

    if source_type == "decoded_json":
        # Load existing decoded blueprint
        with open(path) as f:
            bp = json.load(f)
        decoded_blueprints.append(bp)
        provenance["source_files"] = [str(path)]

    elif source_type == "repo":
        # Run logic_decoder on Python files
        provenance["source_files"] = []

        for py_file in path.rglob("*.py"):
            # Skip common non-source directories
            if any(p in str(py_file) for p in ["__pycache__", ".git", "venv", "node_modules"]):
                continue

            rel_path = str(py_file.relative_to(path))
            provenance["source_files"].append(rel_path)

            # Run logic_decoder
            try:
                result = subprocess.run(
                    ["lpp", "util", "logic_decoder", str(py_file)],
                    capture_output=True,
                    text=True,
                    timeout=60
                )
                # Parse output for decoded JSON
                # The decoder outputs the blueprint at the end
                if "complete" in result.stdout.lower():
                    # Try to extract JSON from output
                    lines = result.stdout.strip().split("\n")
                    for i, line in enumerate(lines):
                        if line.strip().startswith("{") and '"$schema"' in line:
                            try:
                                json_str = "\n".join(lines[i:])
                                bp = json.loads(json_str)
                                bp["_source_file"] = rel_path
                                decoded_blueprints.append(bp)
                                break
                            except json.JSONDecodeError:
                                pass
            except (subprocess.TimeoutExpired, Exception) as e:
                pass  # Continue with other files

    if source_repo:
        provenance["source_repo"] = source_repo

    return {
        "decoded_blueprints": decoded_blueprints,
        "function_analysis": function_analysis,
        "provenance": provenance,
        "source_type": source_type
    }


def extractStates(params: dict) -> dict:
    """
    Extract unique states from decoded blueprints.

    Combines states from multiple blueprints, deduplicating and
    normalizing names.
    """
    blueprints = params.get("decoded_blueprints", [])

    states = {}
    state_sources = {}

    for bp in blueprints:
        bp_states = bp.get("states", {})
        source_file = bp.get("_source_file", bp.get("id", "unknown"))

        for state_name, state_def in bp_states.items():
            # Normalize state name
            normalized = state_name.lower().replace("-", "_").replace(" ", "_")

            if normalized not in states:
                states[normalized] = {
                    "description": state_def.get("description", f"From {source_file}"),
                    "original_name": state_name
                }
                state_sources[normalized] = [source_file]
            else:
                state_sources[normalized].append(source_file)

    # Identify entry state (usually 'idle' or first state)
    entry_state = "idle" if "idle" in states else list(states.keys())[0] if states else "idle"

    return {
        "extracted_states": list(states.keys()),
        "state_definitions": states,
        "state_sources": state_sources,
        "entry_state": entry_state
    }


def extractSlots(params: dict) -> dict:
    """
    Extract customization slots from decoded blueprints.

    Slots are identified from:
    - Actions with external compute references
    - Functions that call external services
    - Clear input/output boundaries
    """
    blueprints = params.get("decoded_blueprints", [])
    function_analysis = params.get("function_analysis", {})

    slots = {}

    for bp in blueprints:
        actions = bp.get("actions", {})

        for action_name, action_def in actions.items():
            compute_unit = action_def.get("compute_unit", "")

            # Extract slot from compute_unit reference
            if compute_unit.startswith("impl:"):
                func_name = compute_unit.replace("impl:", "")

                # Create slot definition
                slot_name = _normalize_slot_name(func_name)

                if slot_name not in slots:
                    slots[slot_name] = {
                        "description": f"Compute: {func_name}",
                        "input": [],
                        "output": ["result"],
                        "original_function": func_name
                    }

    return {"extracted_slots": slots}


def _normalize_slot_name(func_name: str) -> str:
    """Normalize function name to slot name."""
    # Remove common prefixes
    name = func_name.replace("get_", "").replace("_core", "")
    # Convert to snake_case
    name = name.lower().replace(".", "_")
    return name


def extractTerminals(params: dict) -> dict:
    """
    Extract terminal states with output contracts.

    Terminal states are identified from:
    - Explicit terminal_states in blueprints
    - States with no outgoing transitions
    - Error handling patterns (try/except)
    """
    blueprints = params.get("decoded_blueprints", [])
    states = params.get("extracted_states", [])

    terminals = {}

    # Collect terminals from blueprints
    for bp in blueprints:
        bp_terminals = bp.get("terminal_states", {})

        for term_name, term_def in bp_terminals.items():
            if term_name not in terminals:
                terminals[term_name] = term_def

    # Ensure we have at least complete and error
    if "complete" not in terminals:
        terminals["complete"] = {
            "output_schema": {
                "result": {"type": "object", "non_null": True}
            },
            "invariants_guaranteed": ["result_produced"]
        }

    if "error" not in terminals:
        terminals["error"] = {
            "output_schema": {
                "error": {"type": "string", "non_null": True}
            }
        }

    return {"extracted_terminals": terminals}


def composePolicy(params: dict) -> dict:
    """
    Compose the final policy JSON structure.
    """
    policy_name = params.get("policy_name", "generated_policy")
    states = params.get("state_definitions", {})
    entry_state = params.get("entry_state", "idle")
    terminals = params.get("extracted_terminals", {})
    slots = params.get("extracted_slots", {})
    provenance = params.get("provenance", {})

    # Build policy structure
    policy = {
        "$schema": "lpp/v0.2.0",
        "id": policy_name,
        "name": policy_name.replace("_", " ").title(),
        "version": "1.0.0",
        "description": {
            "summary": f"Policy extracted from source",
            "provenance": provenance,
            "design_philosophy": [
                "Extracted from existing implementation",
                "Formal verification ready"
            ],
            "use_cases": []
        },
        "context_schema": {
            "properties": {}
        },
        "states": {},
        "entry_state": entry_state,
        "terminal_states": terminals,
        "slots": slots,
        "gates": {},
        "actions": {},
        "transitions": []
    }

    # Add states (excluding terminals)
    terminal_names = set(terminals.keys())
    for state_name, state_def in states.items():
        if state_name not in terminal_names:
            policy["states"][state_name] = {
                "description": state_def.get("description", "")
            }

    # Ensure entry state exists
    if entry_state not in policy["states"]:
        policy["states"][entry_state] = {"description": "Initial state"}

    # Generate basic transitions
    state_list = list(policy["states"].keys())
    trans_id = 0

    for i, state in enumerate(state_list):
        next_state = state_list[i + 1] if i + 1 < len(state_list) else "complete"
        policy["transitions"].append({
            "id": f"t_{trans_id}",
            "from": state,
            "to": next_state,
            "on_event": f"{state.upper()}_DONE"
        })
        trans_id += 1

    # Add error transition
    policy["transitions"].append({
        "id": f"t_{trans_id}",
        "from": "*",
        "to": "error",
        "on_event": "ERROR"
    })
    trans_id += 1

    # Add reset transition
    policy["transitions"].append({
        "id": f"t_{trans_id}",
        "from": "*",
        "to": entry_state,
        "on_event": "RESET"
    })

    # Generate actions from slots
    for slot_name in slots:
        policy["actions"][f"do_{slot_name}"] = {
            "type": "slot",
            "slot": slot_name
        }

    return {"policy": policy}


def generateTla(params: dict) -> dict:
    """
    Generate TLA+ specification for the policy.
    """
    policy = params.get("policy", {})

    if not policy:
        return {"error": "No policy to generate TLA+ from"}

    policy_name = policy.get("id", "policy")
    states = list(policy.get("states", {}).keys())
    terminals = list(policy.get("terminal_states", {}).keys())
    all_states = states + terminals

    tla_lines = [
        f"--------------------------- MODULE {policy_name} ---------------------------",
        "(* Auto-generated TLA+ specification for L++ policy *)",
        "",
        "EXTENDS Naturals",
        "",
        "CONSTANTS"
    ]

    # Add state constants
    for state in all_states:
        tla_lines.append(f"    STATE_{state},")
    tla_lines[-1] = tla_lines[-1].rstrip(",")  # Remove trailing comma

    tla_lines.extend([
        "",
        "VARIABLE state",
        "",
        "vars == <<state>>",
        "",
        f"States == {{{', '.join(f'STATE_{s}' for s in all_states)}}}",
        "",
        f"TerminalStates == {{{', '.join(f'STATE_{s}' for s in terminals)}}}",
        "",
        "TypeInvariant == state \\in States",
        "",
        f"Init == state = STATE_{policy.get('entry_state', 'idle')}",
        ""
    ])

    # Add transitions
    for trans in policy.get("transitions", []):
        from_state = trans.get("from")
        to_state = trans.get("to")
        trans_id = trans.get("id", "t")

        if from_state == "*":
            tla_lines.extend([
                f"(* Transition: {trans_id} *)",
                f"{trans_id} ==",
                f"    /\\ state \\notin TerminalStates",
                f"    /\\ state' = STATE_{to_state}",
                ""
            ])
        else:
            tla_lines.extend([
                f"(* Transition: {trans_id} *)",
                f"{trans_id} ==",
                f"    /\\ state = STATE_{from_state}",
                f"    /\\ state' = STATE_{to_state}",
                ""
            ])

    # Add Next and Spec
    trans_names = [t.get("id", f"t{i}") for i, t in enumerate(policy.get("transitions", []))]
    tla_lines.extend([
        "Next ==",
        "    \\/ " + "\n    \\/ ".join(trans_names),
        "",
        "Spec == Init /\\ [][Next]_vars",
        "",
        "(* Safety: Type invariant always holds *)",
        "Safety == TypeInvariant",
        "",
        "(* Liveness: Eventually reach terminal state *)",
        "Liveness == <>( state \\in TerminalStates )",
        "",
        "============================================================================="
    ])

    tla_spec = "\n".join(tla_lines)

    return {"tla_spec": tla_spec}


def validatePolicy(params: dict) -> dict:
    """
    Validate the generated policy structure.
    """
    policy = params.get("policy", {})

    errors = []

    # Check required fields
    required = ["$schema", "id", "states", "entry_state", "terminal_states", "transitions"]
    for field in required:
        if field not in policy:
            errors.append(f"Missing required field: {field}")

    # Check entry state exists
    entry = policy.get("entry_state")
    if entry and entry not in policy.get("states", {}):
        errors.append(f"Entry state '{entry}' not in states")

    # Check all transition targets exist
    all_states = set(policy.get("states", {}).keys())
    all_states.update(policy.get("terminal_states", {}).keys())

    for trans in policy.get("transitions", []):
        from_state = trans.get("from")
        to_state = trans.get("to")

        if from_state != "*" and from_state not in all_states:
            errors.append(f"Transition from unknown state: {from_state}")
        if to_state not in all_states:
            errors.append(f"Transition to unknown state: {to_state}")

    return {
        "validation_errors": errors,
        "valid": len(errors) == 0
    }


def writePolicy(params: dict) -> dict:
    """
    Write policy and TLA+ spec to disk.
    """
    policy = params.get("policy", {})
    tla_spec = params.get("tla_spec", "")
    output_path = params.get("output_path")

    if not output_path:
        # Default to policies directory
        output_path = Path(__file__).parent.parent.parent.parent / "lpp" / "policies"

    output_path = Path(output_path)
    output_path.mkdir(parents=True, exist_ok=True)

    policy_name = policy.get("id", "generated_policy")

    # Write policy JSON
    policy_file = output_path / f"{policy_name}.json"
    with open(policy_file, "w") as f:
        json.dump(policy, f, indent=2)

    # Write TLA+ spec
    if tla_spec:
        tla_dir = output_path / "tla"
        tla_dir.mkdir(exist_ok=True)
        tla_file = tla_dir / f"{policy_name}.tla"
        with open(tla_file, "w") as f:
            f.write(tla_spec)

    return {
        "output_path": str(policy_file),
        "tla_path": str(tla_dir / f"{policy_name}.tla") if tla_spec else None
    }


COMPUTE_REGISTRY = {
    ("policy_gen", "analyzeSource"): analyzeSource,
    ("policy_gen", "extractStates"): extractStates,
    ("policy_gen", "extractSlots"): extractSlots,
    ("policy_gen", "extractTerminals"): extractTerminals,
    ("policy_gen", "composePolicy"): composePolicy,
    ("policy_gen", "generateTla"): generateTla,
    ("policy_gen", "validatePolicy"): validatePolicy,
    ("policy_gen", "writePolicy"): writePolicy,
}

# Alias for operational validator compatibility
COMPUTE_UNITS = {
    "policy_gen:analyzeSource": analyzeSource,
    "policy_gen:extractStates": extractStates,
    "policy_gen:extractSlots": extractSlots,
    "policy_gen:extractTerminals": extractTerminals,
    "policy_gen:composePolicy": composePolicy,
    "policy_gen:generateTla": generateTla,
    "policy_gen:validatePolicy": validatePolicy,
    "policy_gen:writePolicy": writePolicy,
}
