"""
COMPUTE units for the L++ Blueprint Playground.

These are the pure computation functions that the compiled playground
operator calls. All editing, validation, simulation, and sharing logic.
"""

import json
import copy
import base64
import zlib
from pathlib import Path
from typing import Any, Dict, List, Optional
from datetime import datetime

# Try to import L++ framework components
try:
    from frame_py.loader import BlueprintLoader
    from frame_py.safe_eval import safe_eval_bool
    HAS_FRAMEWORK = True
except ImportError:
    HAS_FRAMEWORK = False


# =============================================================================
# BLUEPRINT LOADING
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load blueprint from JSON string or file path."""
    json_string = params.get("json_string")
    file_path = params.get("file_path")

    if file_path:
        try:
            path = Path(file_path)
            if not path.exists():
                return {
                    "blueprint_json": None,
                    "blueprint": None,
                    "blueprint_name": None,
                    "is_valid_json": False,
                    "error": f"File not found: {file_path}"
                }
            with open(path) as f:
                json_string = f.read()
        except Exception as e:
            return {
                "blueprint_json": None,
                "blueprint": None,
                "blueprint_name": None,
                "is_valid_json": False,
                "error": str(e)
            }

    if not json_string:
        return {
            "blueprint_json": None,
            "blueprint": None,
            "blueprint_name": None,
            "is_valid_json": False,
            "error": "No JSON string or file path provided"
        }

    # Try to parse JSON
    try:
        bp_data = json.loads(json_string)
        return {
            "blueprint_json": json_string,
            "blueprint": bp_data,
            "blueprint_name": bp_data.get("name", bp_data.get("id", "Untitled")),
            "is_valid_json": True,
            "error": None
        }
    except json.JSONDecodeError as e:
        return {
            "blueprint_json": json_string,
            "blueprint": None,
            "blueprint_name": None,
            "is_valid_json": False,
            "error": f"JSON parse error at line {e.lineno}: {e.msg}"
        }


# =============================================================================
# VALIDATION
# =============================================================================

def validate_json(params: Dict[str, Any]) -> Dict[str, Any]:
    """Validate JSON syntax."""
    json_string = params.get("json_string", "")

    if not json_string:
        return {
            "is_valid": False,
            "result": {"errors": ["Empty JSON string"]},
            "error": "Empty JSON string"
        }

    try:
        json.loads(json_string)
        return {
            "is_valid": True,
            "result": {"errors": [], "message": "Valid JSON syntax"},
            "error": None
        }
    except json.JSONDecodeError as e:
        return {
            "is_valid": False,
            "result": {
                "errors": [f"Line {e.lineno}, Column {e.colno}: {e.msg}"],
                "line": e.lineno,
                "column": e.colno
            },
            "error": f"JSON parse error at line {e.lineno}: {e.msg}"
        }


def validate_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Validate blueprint structure against L++ schema."""
    json_string = params.get("blueprint_json", "")

    if not json_string:
        return {
            "is_valid": False,
            "result": {"errors": ["No blueprint JSON provided"]},
            "error": "No blueprint JSON provided"
        }

    try:
        bp = json.loads(json_string)
    except json.JSONDecodeError as e:
        return {
            "is_valid": False,
            "result": {"errors": [f"Invalid JSON: {e.msg}"]},
            "error": f"Invalid JSON: {e.msg}"
        }

    errors = []
    warnings = []

    # Check required fields
    required = ["id", "states", "transitions", "entry_state"]
    for field in required:
        if field not in bp:
            errors.append(f"Missing required field: {field}")

    # Check schema version
    schema = bp.get("$schema", "")
    if not schema:
        warnings.append("Missing $schema field (recommended: lpp/v0.1.2)")
    elif "lpp" not in schema:
        warnings.append(f"Unrecognized schema: {schema}")

    # Check states
    states = bp.get("states", {})
    if not isinstance(states, dict):
        errors.append("'states' must be an object")
    elif len(states) == 0:
        errors.append("At least one state is required")

    # Check entry_state exists
    entry = bp.get("entry_state")
    if entry and entry not in states:
        errors.append(f"entry_state '{entry}' not found in states")

    # Check terminal_states exist
    terminals = bp.get("terminal_states", [])
    for t in terminals:
        if t not in states:
            errors.append(f"terminal_state '{t}' not found in states")

    # Check transitions
    transitions = bp.get("transitions", [])
    if not isinstance(transitions, list):
        errors.append("'transitions' must be an array")
    else:
        trans_ids = set()
        for i, t in enumerate(transitions):
            if not isinstance(t, dict):
                errors.append(f"Transition {i} must be an object")
                continue

            # Check required transition fields
            if "id" not in t:
                errors.append(f"Transition {i} missing 'id'")
            else:
                if t["id"] in trans_ids:
                    errors.append(f"Duplicate transition id: {t['id']}")
                trans_ids.add(t["id"])

            if "from" not in t:
                errors.append(f"Transition {i} missing 'from'")
            elif t["from"] != "*" and t["from"] not in states:
                errors.append(f"Transition {t.get('id', i)}: "
                              f"from state '{t['from']}' not found")

            if "to" not in t:
                errors.append(f"Transition {i} missing 'to'")
            elif t["to"] != "*" and t["to"] not in states:
                errors.append(f"Transition {t.get('id', i)}: "
                              f"to state '{t['to']}' not found")

            if "on_event" not in t:
                errors.append(f"Transition {t.get('id', i)} missing 'on_event'")

            # Check gates reference
            for gate_id in t.get("gates", []):
                if gate_id not in bp.get("gates", {}):
                    errors.append(f"Transition {t.get('id', i)}: "
                                  f"gate '{gate_id}' not found")

            # Check actions reference
            for action_id in t.get("actions", []):
                if action_id not in bp.get("actions", {}):
                    errors.append(f"Transition {t.get('id', i)}: "
                                  f"action '{action_id}' not found")

    # Check gates
    gates = bp.get("gates", {})
    for gate_id, gate in gates.items():
        if not isinstance(gate, dict):
            errors.append(f"Gate '{gate_id}' must be an object")
            continue
        gate_type = gate.get("type")
        if gate_type not in ["expression", "compute"]:
            errors.append(f"Gate '{gate_id}': invalid type '{gate_type}'")
        if gate_type == "expression" and "expression" not in gate:
            errors.append(f"Gate '{gate_id}': missing 'expression'")
        if gate_type == "compute" and "compute_unit" not in gate:
            errors.append(f"Gate '{gate_id}': missing 'compute_unit'")

    # Check actions
    actions = bp.get("actions", {})
    for action_id, action in actions.items():
        if not isinstance(action, dict):
            errors.append(f"Action '{action_id}' must be an object")
            continue
        action_type = action.get("type")
        if action_type not in ["set", "compute", "emit"]:
            errors.append(f"Action '{action_id}': invalid type '{action_type}'")
        if action_type == "set" and "target" not in action:
            errors.append(f"Action '{action_id}': missing 'target'")
        if action_type == "compute" and "compute_unit" not in action:
            errors.append(f"Action '{action_id}': missing 'compute_unit'")

    is_valid = len(errors) == 0

    return {
        "is_valid": is_valid,
        "result": {
            "errors": errors,
            "warnings": warnings,
            "message": "Valid blueprint" if is_valid else f"{len(errors)} error(s)"
        },
        "error": errors[0] if errors else None
    }


# =============================================================================
# FORMATTING
# =============================================================================

def format_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format/prettify JSON with consistent style."""
    json_string = params.get("json_string", "")

    if not json_string:
        return {
            "formatted": "",
            "output": "No JSON to format"
        }

    try:
        bp = json.loads(json_string)
        formatted = json.dumps(bp, indent=2, ensure_ascii=False)
        return {
            "formatted": formatted,
            "output": "Blueprint formatted successfully"
        }
    except json.JSONDecodeError as e:
        return {
            "formatted": json_string,
            "output": f"Cannot format invalid JSON: {e.msg}"
        }


# =============================================================================
# DIAGRAM GENERATION
# =============================================================================

def generate_diagram(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate Mermaid stateDiagram from blueprint."""
    bp = params.get("blueprint")

    if not bp:
        return {"mermaid": ""}

    lines = ["stateDiagram-v2"]

    # Entry state
    entry = bp.get("entry_state")
    if entry:
        lines.append(f"    [*] --> {entry}")

    # State descriptions as notes
    states = bp.get("states", {})
    for sid, state in states.items():
        if isinstance(state, dict) and state.get("description"):
            desc = state["description"][:50].replace('"', "'")
            lines.append(f"    {sid}: {desc}")

    # Transitions
    transitions = bp.get("transitions", [])
    for t in transitions:
        from_state = t.get("from", "?")
        to_state = t.get("to", "?")
        event = t.get("on_event", "?")

        if from_state == "*":
            # Wildcard: show from all non-target states
            for sid in states:
                if sid != to_state:
                    lines.append(f"    {sid} --> {to_state}: {event}")
        else:
            lines.append(f"    {from_state} --> {to_state}: {event}")

    # Terminal states
    terminals = bp.get("terminal_states", [])
    for term in terminals:
        lines.append(f"    {term} --> [*]")

    return {"mermaid": "\n".join(lines)}


# =============================================================================
# SIMULATION
# =============================================================================

def init_simulation(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize simulation state from blueprint."""
    bp = params.get("blueprint")

    if not bp:
        return {
            "sim_state": None,
            "sim_context": {},
            "available_events": [],
            "trace": [],
            "output": "No blueprint provided"
        }

    entry = bp.get("entry_state")
    if not entry:
        return {
            "sim_state": None,
            "sim_context": {},
            "available_events": [],
            "trace": [],
            "output": "Blueprint has no entry_state"
        }

    # Initialize context from schema
    ctx = {"_state": entry}
    schema = bp.get("context_schema", {})
    for prop in schema.get("properties", {}).keys():
        ctx[prop] = None

    # Get available events
    events = _get_available_events(bp, entry, ctx)

    # Create initial trace
    trace = [{
        "step": 0,
        "timestamp": datetime.now().isoformat(),
        "state": entry,
        "context": copy.deepcopy(ctx),
        "event": None
    }]

    return {
        "sim_state": entry,
        "sim_context": ctx,
        "available_events": events,
        "trace": trace,
        "output": f"Simulation initialized at state: {entry}"
    }


def _evaluate_gate(bp: Dict, gate_id: str, ctx: Dict) -> bool:
    """Evaluate a single gate."""
    gates = bp.get("gates", {})
    gate = gates.get(gate_id)

    if not gate:
        return True

    if gate.get("type") == "expression":
        expr = gate.get("expression", "True")
        if HAS_FRAMEWORK:
            result, _ = safe_eval_bool(expr, ctx)
            return result
        else:
            # Simple fallback evaluation
            try:
                return eval(expr, {"__builtins__": {}}, ctx)
            except:
                return True

    # Compute gates default to True in simulation
    return True


def _get_available_events(bp: Dict, state: str, ctx: Dict) -> List[str]:
    """Get events available from current state."""
    events = []
    eval_ctx = copy.deepcopy(ctx)
    eval_ctx["_state"] = state

    for t in bp.get("transitions", []):
        from_state = t.get("from")
        if from_state != "*" and from_state != state:
            continue

        # Check gates
        gates_pass = True
        for gate_id in t.get("gates", []):
            if not _evaluate_gate(bp, gate_id, eval_ctx):
                gates_pass = False
                break

        if gates_pass:
            event = t.get("on_event")
            if event and event not in events:
                events.append(event)

    return events


def get_available_events(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get list of valid events in current simulation state."""
    bp = params.get("blueprint")
    state = params.get("sim_state")
    ctx = params.get("sim_context", {})

    if not bp or not state:
        return {"events": []}

    events = _get_available_events(bp, state, ctx)
    return {"events": events}


def _resolve_path(path: str, data: Dict) -> Any:
    """Resolve a dotted path in a dictionary."""
    parts = path.split(".")
    obj = data
    for part in parts:
        if isinstance(obj, dict):
            obj = obj.get(part)
        else:
            return None
        if obj is None:
            return None
    return obj


def _execute_action(bp: Dict, action_id: str, ctx: Dict,
                    event_payload: Dict) -> Dict:
    """Execute a single action and return updated context."""
    actions = bp.get("actions", {})
    action = actions.get(action_id)

    if not action:
        return ctx

    new_ctx = copy.deepcopy(ctx)
    scope = {"event": {"payload": event_payload or {}}}
    scope.update(ctx)

    action_type = action.get("type")

    if action_type == "set":
        target = action.get("target")
        if target:
            if "value" in action:
                new_ctx[target] = action["value"]
            elif action.get("value_from"):
                new_ctx[target] = _resolve_path(action["value_from"], scope)
            else:
                new_ctx[target] = None

    # Compute and emit actions are skipped in browser simulation
    return new_ctx


def dispatch_event(params: Dict[str, Any]) -> Dict[str, Any]:
    """Dispatch an event and process state transition."""
    bp = params.get("blueprint")
    state = params.get("sim_state")
    ctx = params.get("sim_context", {})
    trace = params.get("sim_trace", [])
    event_name = params.get("event_name")
    event_payload = params.get("event_payload", {})

    if not bp or not state or not event_name:
        return {
            "sim_state": state,
            "sim_context": ctx,
            "available_events": [],
            "trace": trace,
            "output": "Missing required parameters",
            "error": "Missing blueprint, state, or event_name"
        }

    # Find matching transition
    eval_ctx = copy.deepcopy(ctx)
    eval_ctx["_state"] = state

    matched = None
    for t in bp.get("transitions", []):
        if t.get("on_event") != event_name:
            continue
        from_state = t.get("from")
        if from_state != "*" and from_state != state:
            continue

        # Check gates
        gates_pass = True
        for gate_id in t.get("gates", []):
            if not _evaluate_gate(bp, gate_id, eval_ctx):
                gates_pass = False
                break

        if gates_pass:
            matched = t
            break

    if not matched:
        return {
            "sim_state": state,
            "sim_context": ctx,
            "available_events": _get_available_events(bp, state, ctx),
            "trace": trace,
            "output": f"No matching transition for '{event_name}'",
            "error": f"No transition for {event_name} from {state}"
        }

    # Execute actions
    new_ctx = copy.deepcopy(ctx)
    for action_id in matched.get("actions", []):
        new_ctx = _execute_action(bp, action_id, new_ctx, event_payload)

    # Perform transition
    new_state = matched.get("to")
    new_ctx["_state"] = new_state

    # Update trace
    new_trace = copy.deepcopy(trace)
    new_trace.append({
        "step": len(trace),
        "timestamp": datetime.now().isoformat(),
        "state": new_state,
        "prev_state": state,
        "event": event_name,
        "event_payload": event_payload,
        "transition_id": matched.get("id"),
        "context": copy.deepcopy(new_ctx)
    })

    # Get new available events
    events = _get_available_events(bp, new_state, new_ctx)

    output = f"{state} --[{event_name}]--> {new_state}"

    return {
        "sim_state": new_state,
        "sim_context": new_ctx,
        "available_events": events,
        "trace": new_trace,
        "output": output,
        "error": None
    }


# =============================================================================
# SHARING
# =============================================================================

def encode_share_url(params: Dict[str, Any]) -> Dict[str, Any]:
    """Encode blueprint as base64 URL parameter."""
    json_string = params.get("blueprint_json", "")
    base_url = params.get("base_url", "http://localhost:8765")

    if not json_string:
        return {
            "url": "",
            "output": "No blueprint to share"
        }

    try:
        # Compress and encode
        compressed = zlib.compress(json_string.encode("utf-8"))
        encoded = base64.urlsafe_b64encode(compressed).decode("ascii")
        url = f"{base_url}?bp={encoded}"
        return {
            "url": url,
            "output": f"Share URL generated ({len(encoded)} chars)"
        }
    except Exception as e:
        return {
            "url": "",
            "output": f"Failed to encode: {e}"
        }


def decode_share_url(params: Dict[str, Any]) -> Dict[str, Any]:
    """Decode blueprint from base64 URL parameter."""
    url = params.get("url", "")

    if not url:
        return {
            "blueprint_json": None,
            "blueprint": None,
            "blueprint_name": None,
            "is_valid_json": False,
            "output": "No URL provided",
            "error": "No URL provided"
        }

    try:
        # Extract bp parameter
        if "?bp=" in url:
            encoded = url.split("?bp=")[1].split("&")[0]
        elif "bp=" in url:
            encoded = url.split("bp=")[1].split("&")[0]
        else:
            encoded = url

        # Decode and decompress
        compressed = base64.urlsafe_b64decode(encoded)
        json_string = zlib.decompress(compressed).decode("utf-8")

        # Parse
        bp = json.loads(json_string)

        return {
            "blueprint_json": json_string,
            "blueprint": bp,
            "blueprint_name": bp.get("name", bp.get("id", "Imported")),
            "is_valid_json": True,
            "output": "Blueprint imported from URL",
            "error": None
        }
    except Exception as e:
        return {
            "blueprint_json": None,
            "blueprint": None,
            "blueprint_name": None,
            "is_valid_json": False,
            "output": f"Failed to decode URL: {e}",
            "error": str(e)
        }


# =============================================================================
# EXPORT
# =============================================================================

def export_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export blueprint to file."""
    json_string = params.get("blueprint_json", "")
    file_path = params.get("file_path")

    if not json_string:
        return {
            "output": "No blueprint to export",
            "error": "No blueprint"
        }

    if not file_path:
        # Generate default filename
        try:
            bp = json.loads(json_string)
            name = bp.get("id", "blueprint")
            file_path = f"./{name}.json"
        except:
            file_path = "./blueprint.json"

    try:
        # Format before writing
        bp = json.loads(json_string)
        formatted = json.dumps(bp, indent=2, ensure_ascii=False)

        path = Path(file_path)
        path.parent.mkdir(parents=True, exist_ok=True)

        with open(path, "w", encoding="utf-8") as f:
            f.write(formatted)

        return {
            "output": f"Exported to: {file_path}",
            "error": None
        }
    except Exception as e:
        return {
            "output": f"Export failed: {e}",
            "error": str(e)
        }


# =============================================================================
# COMPUTE REGISTRY
# =============================================================================

COMPUTE_REGISTRY = {
    "play:load_blueprint": load_blueprint,
    "play:validate_json": validate_json,
    "play:validate_blueprint": validate_blueprint,
    "play:format_blueprint": format_blueprint,
    "play:generate_diagram": generate_diagram,
    "play:init_simulation": init_simulation,
    "play:dispatch_event": dispatch_event,
    "play:get_available_events": get_available_events,
    "play:encode_share_url": encode_share_url,
    "play:decode_share_url": decode_share_url,
    "play:export_blueprint": export_blueprint,
}
