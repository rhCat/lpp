"""
Blueprint Builder - Compute Functions

Builds L++ blueprints from extracted patterns and modules.
"""
import re
import json
from typing import Dict, List, Any, Optional


_state: Dict[str, Any] = {}


def init(params: dict) -> dict:
    """Initialize blueprint builder."""
    global _state
    _state = {"blueprints": [], "current": None}
    return {"initialized": True}


def buildFromClass(params: dict) -> dict:
    """Build blueprint from a class module."""
    module = params.get("module", {})
    name = module.get("name", "unknown")
    bp_id = _to_snake_case(name)

    # Extract states from patterns or methods
    states = _extract_states(module)
    actions = _extract_actions(module)
    transitions = _generate_transitions(states, module)
    gates = _extract_gates(module)

    blueprint = {
        "$schema": "lpp/v0.1.2",
        "id": bp_id,
        "name": name,
        "version": "1.0.0",
        "description": module.get("docstring", f"Blueprint for {name}"),
        "states": states,
        "entry_state": "idle",
        "terminal_states": ["complete", "error"],
        "gates": gates,
        "actions": actions,
        "transitions": transitions,
        "_source": module.get("file", {}).get("relpath", "")
    }

    _state["current"] = blueprint
    _state["blueprints"].append(blueprint)
    return {"blueprint": blueprint, "id": bp_id}


def buildFromPatterns(params: dict) -> dict:
    """Build blueprint from extracted patterns."""
    patterns = params.get("patterns", {})
    name = params.get("name", "unknown")
    bp_id = _to_snake_case(name)

    # Use pattern data to build blueprint
    states = {"idle": {"description": "Awaiting input"}}

    # Add states from pattern
    for s in patterns.get("states", []):
        state_id = _to_snake_case(s) if isinstance(s, str) else s.get("id", s)
        states[state_id] = {"description": f"State: {state_id}"}

    states["complete"] = {"description": "Complete"}
    states["error"] = {"description": "Error"}

    # Build actions from pattern methods/handlers
    actions = {}
    for m in patterns.get("methods", []):
        method_name = m if isinstance(m, str) else m.get("name", "")
        if method_name and not method_name.startswith("_"):
            actions[method_name] = {
                "type": "compute",
                "unit": f"{bp_id}:{method_name}"
            }

    # Build gates from conditions
    gates = {}
    for g in patterns.get("conditions", []):
        gate_id = g if isinstance(g, str) else g.get("id", g.get("name", ""))
        if gate_id:
            gates[gate_id] = {
                "type": "expression",
                "expression": g.get("expression", f"{gate_id}") if isinstance(g, dict) else gate_id
            }

    # Generate transitions
    transitions = _generate_transitions(states, {"patterns": patterns})

    blueprint = {
        "$schema": "lpp/v0.1.2",
        "id": bp_id,
        "name": name,
        "version": "1.0.0",
        "description": params.get("description", f"Blueprint for {name}"),
        "states": states,
        "entry_state": "idle",
        "terminal_states": ["complete", "error"],
        "gates": gates,
        "actions": actions,
        "transitions": transitions,
        "_source": params.get("source", "")
    }

    _state["current"] = blueprint
    _state["blueprints"].append(blueprint)
    return {"blueprint": blueprint, "id": bp_id}


def addStates(params: dict) -> dict:
    """Add states to current blueprint."""
    bp = _state.get("current")
    if not bp:
        return {"error": "No current blueprint"}

    states = params.get("states", {})
    for state_id, state_info in states.items():
        if isinstance(state_info, str):
            bp["states"][state_id] = {"description": state_info}
        else:
            bp["states"][state_id] = state_info

    return {"added": len(states), "total": len(bp["states"])}


def addTransitions(params: dict) -> dict:
    """Add transitions to current blueprint."""
    bp = _state.get("current")
    if not bp:
        return {"error": "No current blueprint"}

    transitions = params.get("transitions", [])
    existing_ids = {t["id"] for t in bp.get("transitions", [])}
    added = 0

    for t in transitions:
        if t.get("id") not in existing_ids:
            bp["transitions"].append(t)
            added += 1

    return {"added": added, "total": len(bp["transitions"])}


def addGates(params: dict) -> dict:
    """Add gates to current blueprint."""
    bp = _state.get("current")
    if not bp:
        return {"error": "No current blueprint"}

    gates = params.get("gates", {})
    bp["gates"].update(gates)
    return {"added": len(gates), "total": len(bp["gates"])}


def addActions(params: dict) -> dict:
    """Add actions to current blueprint."""
    bp = _state.get("current")
    if not bp:
        return {"error": "No current blueprint"}

    actions = params.get("actions", {})
    bp["actions"].update(actions)
    return {"added": len(actions), "total": len(bp["actions"])}


def validate(params: dict) -> dict:
    """Validate current or specified blueprint."""
    bp = params.get("blueprint") or _state.get("current")
    if not bp:
        return {"valid": False, "errors": ["No blueprint to validate"]}

    errors = []
    warnings = []

    # Required fields
    for field in ["id", "name", "states", "entry_state"]:
        if field not in bp:
            errors.append(f"Missing required field: {field}")

    # Entry state must exist
    if bp.get("entry_state") not in bp.get("states", {}):
        errors.append(f"Entry state '{bp.get('entry_state')}' not in states")

    # Terminal states must exist
    for ts in bp.get("terminal_states", []):
        if ts not in bp.get("states", {}):
            warnings.append(f"Terminal state '{ts}' not in states")

    # Transition references
    states = set(bp.get("states", {}).keys())
    for t in bp.get("transitions", []):
        if t.get("from") != "*" and t.get("from") not in states:
            warnings.append(
                f"Transition {t.get('id')}: from state '{t.get('from')}' not found")
        if t.get("to") not in states:
            warnings.append(
                f"Transition {t.get('id')}: to state '{t.get('to')}' not found")

    return {"valid": len(errors) == 0, "errors": errors, "warnings": warnings}


def toJson(params: dict) -> dict:
    """Convert blueprint to JSON string."""
    bp = params.get("blueprint") or _state.get("current")
    if not bp:
        return {"error": "No blueprint"}

    indent = params.get("indent", 2)
    return {"json": json.dumps(bp, indent=indent), "id": bp.get("id")}


def getBlueprint(params: dict) -> dict:
    """Get current or specified blueprint."""
    bp_id = params.get("id")
    if bp_id:
        for bp in _state.get("blueprints", []):
            if bp["id"] == bp_id:
                return {"blueprint": bp}
        return {"error": f"Blueprint '{bp_id}' not found"}
    return {"blueprint": _state.get("current")}


def listBlueprints(params: dict) -> dict:
    """List all built blueprints."""
    blueprints = _state.get("blueprints", [])
    return {
        "blueprints": [{"id": bp["id"], "name": bp["name"]} for bp in blueprints],
        "count": len(blueprints)
    }


# --- Helper functions ---

def _to_snake_case(name: str) -> str:
    """Convert CamelCase to snake_case."""
    s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
    return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()


def _extract_states(module: dict) -> dict:
    """Extract states from module."""
    states = {"idle": {"description": "Awaiting input"}}

    # From explicit states list
    for s in module.get("states", []):
        state_id = _to_snake_case(s) if isinstance(s, str) else s
        states[state_id] = {"description": f"State: {state_id}"}

    # From patterns
    patterns = module.get("patterns", {})
    for s in patterns.get("states", []):
        state_id = _to_snake_case(s) if isinstance(s, str) else s
        if state_id not in states:
            states[state_id] = {"description": f"State: {state_id}"}

    # From methods that look like state handlers
    for m in module.get("methods", []):
        name = m.get("name", "") if isinstance(m, dict) else m
        if name.startswith("on_enter_") or name.startswith("on_exit_"):
            state_id = name.replace("on_enter_", "").replace("on_exit_", "")
            if state_id not in states:
                states[state_id] = {"description": f"State: {state_id}"}

    states["complete"] = {"description": "Complete"}
    states["error"] = {"description": "Error"}
    return states


def _extract_actions(module: dict) -> dict:
    """Extract actions from module methods."""
    actions = {}
    bp_id = _to_snake_case(module.get("name", "unknown"))

    for m in module.get("methods", []):
        if isinstance(m, dict):
            name = m.get("name", "")
            doc = m.get("docstring", "")
        else:
            name, doc = m, ""

        # Skip private and dunder methods
        if name.startswith("_"):
            continue

        # Skip state handlers (they're not actions)
        if name.startswith("on_enter_") or name.startswith("on_exit_"):
            continue

        actions[name] = {
            "type": "compute",
            "unit": f"{bp_id}:{name}",
            "description": doc[:100] if doc else ""
        }

    # If no actions found, add a default
    if not actions:
        actions["execute"] = {"type": "compute", "unit": f"{bp_id}:execute"}

    return actions


def _extract_gates(module: dict) -> dict:
    """Extract gates from module patterns."""
    gates = {}

    patterns = module.get("patterns", {})
    for cond in patterns.get("conditions", []):
        if isinstance(cond, str):
            gates[cond] = {"type": "expression", "expression": cond}
        elif isinstance(cond, dict):
            gate_id = cond.get("id", cond.get("name", ""))
            if gate_id:
                gates[gate_id] = {
                    "type": "expression",
                    "expression": cond.get("expression", gate_id)
                }

    # Add standard gates
    gates["has_error"] = {"type": "expression",
                          "expression": "error is not None"}
    gates["no_error"] = {"type": "expression", "expression": "error is None"}

    return gates


def _generate_transitions(states: dict, module: dict) -> list:
    """Generate transitions based on states and patterns."""
    transitions = []
    t_id = 0

    # Get state list (excluding idle, complete, error)
    processing_states = [s for s in states.keys()
                         if s not in ["idle", "complete", "error"]]

    # Basic flow: idle -> first processing state
    if processing_states:
        transitions.append({
            "id": f"t{t_id}",
            "from": "idle",
            "to": processing_states[0],
            "on_event": "START"
        })
        t_id += 1

        # Chain processing states
        for i, state in enumerate(processing_states[:-1]):
            transitions.append({
                "id": f"t{t_id}",
                "from": state,
                "to": processing_states[i + 1],
                "on_event": "NEXT"
            })
            t_id += 1

        # Last processing state -> complete
        transitions.append({
            "id": f"t{t_id}",
            "from": processing_states[-1],
            "to": "complete",
            "on_event": "DONE"
        })
        t_id += 1
    else:
        # No processing states, simple idle -> complete
        transitions.append({
            "id": f"t{t_id}",
            "from": "idle",
            "to": "complete",
            "on_event": "DONE"
        })
        t_id += 1

    # Error transition from any state
    transitions.append({
        "id": f"t{t_id}",
        "from": "*",
        "to": "error",
        "on_event": "ERROR"
    })
    t_id += 1

    # Reset transitions
    transitions.append({
        "id": f"t{t_id}",
        "from": "error",
        "to": "idle",
        "on_event": "RESET"
    })
    t_id += 1

    transitions.append({
        "id": f"t{t_id}",
        "from": "complete",
        "to": "idle",
        "on_event": "RESET"
    })

    return transitions


COMPUTE_REGISTRY = {
    "blueprint:init": init,
    "blueprint:buildFromClass": buildFromClass,
    "blueprint:buildFromPatterns": buildFromPatterns,
    "blueprint:addStates": addStates,
    "blueprint:addTransitions": addTransitions,
    "blueprint:addGates": addGates,
    "blueprint:addActions": addActions,
    "blueprint:validate": validate,
    "blueprint:toJson": toJson,
    "blueprint:getBlueprint": getBlueprint,
    "blueprint:listBlueprints": listBlueprints,
}
