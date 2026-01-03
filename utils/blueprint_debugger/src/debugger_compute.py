"""
COMPUTE units for the L++ Blueprint Debugger.

These are pure computation functions for step-through debugging of L++
blueprints with breakpoints, inspection, and time-travel capabilities.
"""

import json
import copy
import uuid
from pathlib import Path
from typing import Any, Dict, List, Optional
from datetime import datetime

from frame_py.loader import BlueprintLoader
from frame_py.safe_eval import safe_eval_bool


# =============================================================================
# BLUEPRINT LOADING
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file for debugging."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "error": "No path provided"}

    try:
        path = Path(path)
        if not path.exists():
            return {"blueprint": None, "error": f"File not found: {path}"}

        with open(path) as f:
            raw = json.load(f)

        loader = BlueprintLoader(raw)
        blueprint, load_error = loader.load()

        if load_error:
            return {"blueprint": None, "error": load_error}

        # Convert to dict structure for debugging
        bp_data = {
            "id": blueprint.id,
            "name": blueprint.name,
            "version": blueprint.version,
            "description": blueprint.description,
            "entry_state": blueprint.entry_state,
            "terminal_states": list(blueprint.terminal_states),
            "states": {
                sid: {
                    "description": s.description,
                    "on_enter": list(s.on_enter),
                    "on_exit": list(s.on_exit)
                } for sid, s in blueprint.states.items()
            },
            "transitions": [
                {
                    "id": t.id,
                    "from": t.from_state,
                    "to": t.to_state,
                    "on_event": t.on_event,
                    "gates": list(t.gates),
                    "actions": list(t.actions)
                }
                for t in blueprint.transitions
            ],
            "gates": {
                gid: {
                    "type": g.type.value,
                    "expression": g.expression,
                    "compute_unit": g.compute_unit
                } for gid, g in blueprint.gates.items()
            },
            "actions": {
                aid: {
                    "type": a.type.value,
                    "target": a.target,
                    "value": a.value,
                    "value_from": a.value_from,
                    "compute_unit": a.compute_unit,
                    "input_map": a.input_map,
                    "output_map": a.output_map
                } for aid, a in blueprint.actions.items()
            },
            "context_schema": raw.get("context_schema", {})
        }

        return {
            "blueprint": bp_data,
            "blueprint_path": str(path),
            "blueprint_name": blueprint.name,
            "blueprint_id": blueprint.id,
            "error": None
        }
    except Exception as e:
        return {"blueprint": None, "error": str(e)}


# =============================================================================
# SESSION MANAGEMENT
# =============================================================================

def init_debug_session(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize a debug session from blueprint."""
    bp = params.get("blueprint")
    if not bp:
        return {"error": "No blueprint provided"}

    # Initialize context from schema
    ctx = {"_state": bp["entry_state"]}
    schema = bp.get("context_schema", {})
    for prop in schema.get("properties", {}).keys():
        ctx[prop] = None

    # Get available transitions
    avail = _get_available_transitions(bp, bp["entry_state"], ctx)

    # Create initial history entry
    history = [{
        "step": 0,
        "timestamp": datetime.now().isoformat(),
        "state": bp["entry_state"],
        "context": copy.deepcopy(ctx),
        "event": None,
        "transition_id": None,
        "gate_results": {},
        "action_results": []
    }]

    return {
        "debug_state": bp["entry_state"],
        "debug_context": ctx,
        "history": history,
        "history_index": 0,
        "breakpoints": [],
        "watches": [],
        "watch_values": {},
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "is_paused": False,
        "output": f"Debug session started at state: {bp['entry_state']}"
    }


def reset_session(params: Dict[str, Any]) -> Dict[str, Any]:
    """Reset debug session to initial state, preserving breakpoints."""
    bp = params.get("blueprint")
    breakpoints = params.get("breakpoints", [])
    watches = params.get("watches", [])

    if not bp:
        return {"error": "No blueprint provided"}

    result = init_debug_session({"blueprint": bp})
    result["breakpoints"] = breakpoints
    result["watches"] = watches
    result["output"] = f"Session reset to initial state: {bp['entry_state']}"
    return result


# =============================================================================
# BREAKPOINT MANAGEMENT
# =============================================================================

def set_breakpoint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add a breakpoint."""
    breakpoints = params.get("breakpoints", [])
    bp_type = params.get("bp_type", "state")
    target = params.get("target")
    condition = params.get("condition")

    if not target:
        return {
            "breakpoints": breakpoints,
            "output": "Error: breakpoint target required"
        }

    # Validate breakpoint type
    valid_types = ["state", "transition", "gate", "event", "conditional"]
    if bp_type not in valid_types:
        return {
            "breakpoints": breakpoints,
            "output": f"Error: invalid type. Use: {valid_types}"
        }

    bp_id = f"bp_{len(breakpoints) + 1}_{uuid.uuid4().hex[:6]}"
    new_bp = {
        "id": bp_id,
        "type": bp_type,
        "target": target,
        "condition": condition,
        "enabled": True,
        "hit_count": 0
    }

    new_breakpoints = breakpoints + [new_bp]
    return {
        "breakpoints": new_breakpoints,
        "output": f"Breakpoint {bp_id} set: {bp_type} on '{target}'"
    }


def remove_breakpoint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Remove a breakpoint by ID or index."""
    breakpoints = params.get("breakpoints", [])
    bp_id = params.get("bp_id")

    if not bp_id:
        return {"breakpoints": breakpoints, "output": "Error: bp_id required"}

    # Try by ID first, then by index
    new_breakpoints = []
    removed = False
    for i, bp in enumerate(breakpoints):
        if bp["id"] == bp_id or str(i) == str(bp_id):
            removed = True
        else:
            new_breakpoints.append(bp)

    if removed:
        return {
            "breakpoints": new_breakpoints,
            "output": f"Breakpoint {bp_id} removed"
        }
    else:
        return {
            "breakpoints": breakpoints,
            "output": f"Breakpoint {bp_id} not found"
        }


def list_breakpoints(params: Dict[str, Any]) -> Dict[str, Any]:
    """List all breakpoints."""
    breakpoints = params.get("breakpoints", [])

    if not breakpoints:
        return {"output": "No breakpoints set"}

    lines = ["Breakpoints:", "=" * 50]
    for i, bp in enumerate(breakpoints):
        status = "ON" if bp.get("enabled", True) else "OFF"
        cond = f" when: {bp['condition']}" if bp.get("condition") else ""
        hits = bp.get("hit_count", 0)
        lines.append(
            f"  [{i}] {bp['id']} [{status}] "
            f"{bp['type']}:{bp['target']}{cond} (hits: {hits})"
        )
    lines.append("=" * 50)

    return {"output": "\n".join(lines)}


def _check_breakpoint(
    bp: Dict,
    state: str,
    transition: Optional[Dict],
    event: Optional[str],
    ctx: Dict
) -> bool:
    """Check if a breakpoint should trigger."""
    if not bp.get("enabled", True):
        return False

    bp_type = bp.get("type")
    target = bp.get("target")
    condition = bp.get("condition")

    triggered = False

    if bp_type == "state" and state == target:
        triggered = True
    elif bp_type == "transition" and transition:
        if transition.get("id") == target:
            triggered = True
    elif bp_type == "gate" and transition:
        if target in transition.get("gates", []):
            triggered = True
    elif bp_type == "event" and event == target:
        triggered = True
    elif bp_type == "conditional" and condition:
        result, _ = safe_eval_bool(condition, ctx)
        triggered = result

    # Check additional condition if present and not conditional type
    if triggered and condition and bp_type != "conditional":
        result, _ = safe_eval_bool(condition, ctx)
        triggered = result

    return triggered


# =============================================================================
# GATE AND ACTION HELPERS
# =============================================================================

def _evaluate_gate(bp: Dict, gate_id: str, ctx: Dict) -> tuple:
    """Evaluate a gate and return (result, details)."""
    gate = bp["gates"].get(gate_id)
    if not gate:
        return True, {"gate_id": gate_id, "result": True, "reason": "not found"}

    if gate["type"] == "expression":
        expr = gate.get("expression", "True")
        result, error = safe_eval_bool(expr, ctx)
        return result, {
            "gate_id": gate_id,
            "expression": expr,
            "result": result,
            "error": error
        }
    elif gate["type"] == "compute":
        # Compute gates default to True in debugger
        return True, {
            "gate_id": gate_id,
            "compute_unit": gate.get("compute_unit"),
            "result": True,
            "reason": "compute gate (simulated)"
        }

    return True, {"gate_id": gate_id, "result": True}


def _get_available_transitions(
    bp: Dict, state: str, ctx: Dict
) -> List[Dict]:
    """Get transitions available from current state."""
    available = []
    eval_ctx = copy.deepcopy(ctx)
    eval_ctx["_state"] = state

    for t in bp["transitions"]:
        if t["from"] != "*" and t["from"] != state:
            continue

        gates_pass = True
        for gate_id in t.get("gates", []):
            result, _ = _evaluate_gate(bp, gate_id, eval_ctx)
            if not result:
                gates_pass = False
                break

        if gates_pass:
            available.append({
                "id": t["id"],
                "event": t["on_event"],
                "from": t["from"],
                "to": t["to"],
                "gates": t.get("gates", []),
                "actions": t.get("actions", [])
            })

    return available


def _resolve_path(path: str, data: Dict) -> Any:
    """Resolve dotted path in dictionary."""
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


def _execute_action(
    bp: Dict, action_id: str, ctx: Dict, event_payload: Dict
) -> tuple:
    """Execute action and return (new_ctx, details)."""
    action = bp["actions"].get(action_id)
    if not action:
        return ctx, {"action_id": action_id, "error": "not found"}

    new_ctx = copy.deepcopy(ctx)
    scope = {"event": {"payload": event_payload or {}}}
    scope.update(ctx)

    details = {
        "action_id": action_id,
        "type": action["type"]
    }

    if action["type"] == "set":
        target = action.get("target")
        if target:
            if action.get("value") is not None:
                new_ctx[target] = action["value"]
                details["target"] = target
                details["value"] = action["value"]
            elif action.get("value_from"):
                val = _resolve_path(action["value_from"], scope)
                new_ctx[target] = val
                details["target"] = target
                details["value_from"] = action["value_from"]
                details["resolved_value"] = val
            else:
                new_ctx[target] = None
                details["target"] = target
                details["value"] = None

    elif action["type"] == "compute":
        details["compute_unit"] = action.get("compute_unit")
        details["input_map"] = action.get("input_map")
        details["output_map"] = action.get("output_map")
        details["simulated"] = True

    return new_ctx, details


def _update_watches(watches: List, ctx: Dict) -> Dict:
    """Evaluate all watch expressions."""
    watch_values = {}
    for watch in watches:
        watch_id = watch.get("id", watch.get("name", "unknown"))
        expr = watch.get("expression")
        if expr:
            try:
                result, error = safe_eval_bool(expr, ctx)
                if error:
                    # Try as value expression
                    try:
                        result = eval(expr, {"__builtins__": {}}, ctx)
                    except Exception:
                        result = f"<error: {error}>"
                watch_values[watch_id] = result
            except Exception as e:
                watch_values[watch_id] = f"<error: {e}>"
    return watch_values


# =============================================================================
# STEPPING
# =============================================================================

def step(params: Dict[str, Any]) -> Dict[str, Any]:
    """Execute one step (event/transition) with full details."""
    bp = params.get("blueprint")
    state = params.get("debug_state")
    ctx = params.get("debug_context", {})
    history = params.get("history", [])
    history_index = params.get("history_index", 0)
    breakpoints = params.get("breakpoints", [])
    watches = params.get("watches", [])
    event_name = params.get("event_name")
    event_payload = params.get("event_payload", {})

    if not bp or not state:
        return {"error": "No blueprint or state"}

    if not event_name:
        # Get first available event
        avail = _get_available_transitions(bp, state, ctx)
        if not avail:
            return {
                "debug_state": state,
                "debug_context": ctx,
                "history": history,
                "history_index": history_index,
                "output": "No available transitions from current state",
                "error": "No transitions available"
            }
        event_name = avail[0]["event"]

    # Find matching transition
    eval_ctx = copy.deepcopy(ctx)
    eval_ctx["_state"] = state

    matched = None
    gate_results = {}

    for t in bp["transitions"]:
        if t["on_event"] != event_name:
            continue
        if t["from"] != "*" and t["from"] != state:
            continue

        # Evaluate gates
        gates_pass = True
        for gate_id in t.get("gates", []):
            result, details = _evaluate_gate(bp, gate_id, eval_ctx)
            gate_results[gate_id] = details
            if not result:
                gates_pass = False
                break

        if gates_pass:
            matched = t
            break

    if not matched:
        return {
            "debug_state": state,
            "debug_context": ctx,
            "history": history,
            "history_index": history_index,
            "last_gate_results": gate_results,
            "available_events": [],
            "available_transitions": [],
            "output": f"No matching transition for event '{event_name}'",
            "error": f"No transition for {event_name} from {state}"
        }

    # Execute actions
    new_ctx = copy.deepcopy(ctx)
    action_results = []
    for action_id in matched.get("actions", []):
        new_ctx, details = _execute_action(bp, action_id, new_ctx, event_payload)
        action_results.append(details)

    # Transition to new state
    new_state = matched["to"]
    new_ctx["_state"] = new_state

    # Create history entry
    new_history = history[:history_index + 1]  # Truncate if we stepped back
    step_num = len(new_history)
    new_history.append({
        "step": step_num,
        "timestamp": datetime.now().isoformat(),
        "state": new_state,
        "prev_state": state,
        "context": copy.deepcopy(new_ctx),
        "event": event_name,
        "event_payload": event_payload,
        "transition_id": matched["id"],
        "gate_results": gate_results,
        "action_results": action_results
    })
    new_index = step_num

    # Check breakpoints
    hit_bp = None
    is_paused = False
    for bp_item in breakpoints:
        if _check_breakpoint(bp_item, new_state, matched, event_name, new_ctx):
            bp_item["hit_count"] = bp_item.get("hit_count", 0) + 1
            hit_bp = bp_item
            is_paused = True
            break

    # Get new available transitions
    avail = _get_available_transitions(bp, new_state, new_ctx)

    # Update watches
    watch_values = _update_watches(watches, new_ctx)

    # Build output
    lines = [
        f"Step {step_num}: {state} --[{event_name}]--> {new_state}"
    ]
    if action_results:
        lines.append(f"  Actions: {[a['action_id'] for a in action_results]}")
    if hit_bp:
        lines.append(f"  ** BREAKPOINT HIT: {hit_bp['id']} **")

    return {
        "debug_state": new_state,
        "debug_context": new_ctx,
        "history": new_history,
        "history_index": new_index,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "last_transition": {
            "id": matched["id"],
            "from": state,
            "to": new_state,
            "event": event_name,
            "actions": matched.get("actions", [])
        },
        "last_gate_results": gate_results,
        "last_action_results": action_results,
        "watch_values": watch_values,
        "is_paused": is_paused,
        "hit_breakpoint": hit_bp,
        "output": "\n".join(lines),
        "error": None
    }


def step_over(params: Dict[str, Any]) -> Dict[str, Any]:
    """Step over (execute without action details)."""
    result = step(params)
    # Clear detailed action results for step_over
    result["last_gate_results"] = {}
    result["last_action_results"] = []
    return result


def step_back(params: Dict[str, Any]) -> Dict[str, Any]:
    """Step back to previous history entry."""
    history = params.get("history", [])
    history_index = params.get("history_index", 0)
    bp = params.get("blueprint")
    watches = params.get("watches", [])

    if history_index <= 0:
        return {"output": "Cannot step back - at initial state"}

    new_index = history_index - 1
    prev_entry = history[new_index]

    state = prev_entry["state"]
    ctx = copy.deepcopy(prev_entry["context"])

    avail = _get_available_transitions(bp, state, ctx) if bp else []
    watch_values = _update_watches(watches, ctx)

    return {
        "debug_state": state,
        "debug_context": ctx,
        "history_index": new_index,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "watch_values": watch_values,
        "output": f"Stepped back to step {new_index}: state '{state}'"
    }


# =============================================================================
# RUN AND CONTINUE
# =============================================================================

def run_to_breakpoint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Run until a breakpoint is hit or terminal state reached."""
    bp = params.get("blueprint")
    state = params.get("debug_state")
    ctx = params.get("debug_context", {})
    history = params.get("history", [])
    history_index = params.get("history_index", 0)
    breakpoints = params.get("breakpoints", [])
    watches = params.get("watches", [])
    max_steps = params.get("max_steps", 1000)

    if not bp:
        return {"error": "No blueprint"}

    current_state = state
    current_ctx = copy.deepcopy(ctx)
    current_history = copy.deepcopy(history)
    current_index = history_index
    steps_taken = 0
    hit_bp = None

    while steps_taken < max_steps:
        # Check if at terminal state
        if current_state in bp.get("terminal_states", []):
            break

        # Get available transitions
        avail = _get_available_transitions(bp, current_state, current_ctx)
        if not avail:
            break

        # Take first available transition
        event_name = avail[0]["event"]

        result = step({
            "blueprint": bp,
            "debug_state": current_state,
            "debug_context": current_ctx,
            "history": current_history,
            "history_index": current_index,
            "breakpoints": breakpoints,
            "watches": watches,
            "event_name": event_name,
            "event_payload": {}
        })

        if result.get("error"):
            break

        current_state = result["debug_state"]
        current_ctx = result["debug_context"]
        current_history = result["history"]
        current_index = result["history_index"]
        steps_taken += 1

        if result.get("hit_breakpoint"):
            hit_bp = result["hit_breakpoint"]
            break

    avail = _get_available_transitions(bp, current_state, current_ctx)
    watch_values = _update_watches(watches, current_ctx)

    lines = [f"Ran {steps_taken} steps"]
    if hit_bp:
        lines.append(f"Stopped at breakpoint: {hit_bp['id']}")
    elif current_state in bp.get("terminal_states", []):
        lines.append(f"Reached terminal state: {current_state}")
    elif not avail:
        lines.append(f"No available transitions at: {current_state}")
    lines.append(f"Current state: {current_state}")

    return {
        "debug_state": current_state,
        "debug_context": current_ctx,
        "history": current_history,
        "history_index": current_index,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "watch_values": watch_values,
        "is_paused": hit_bp is not None,
        "hit_breakpoint": hit_bp,
        "output": "\n".join(lines),
        "error": None
    }


def continue_execution(params: Dict[str, Any]) -> Dict[str, Any]:
    """Continue execution after a breakpoint."""
    # First step past current position, then run to next breakpoint
    bp = params.get("blueprint")
    state = params.get("debug_state")
    ctx = params.get("debug_context", {})
    history = params.get("history", [])
    history_index = params.get("history_index", 0)
    breakpoints = params.get("breakpoints", [])
    watches = params.get("watches", [])

    # Get available transitions
    avail = _get_available_transitions(bp, state, ctx)
    if not avail:
        return {
            "debug_state": state,
            "debug_context": ctx,
            "history": history,
            "history_index": history_index,
            "output": "No transitions available to continue",
            "error": "Cannot continue - no available transitions"
        }

    # Take one step without checking breakpoints
    event_name = avail[0]["event"]
    step_result = step({
        "blueprint": bp,
        "debug_state": state,
        "debug_context": ctx,
        "history": history,
        "history_index": history_index,
        "breakpoints": [],  # Skip breakpoint check for first step
        "watches": watches,
        "event_name": event_name,
        "event_payload": {}
    })

    if step_result.get("error"):
        return step_result

    # Now run to next breakpoint
    return run_to_breakpoint({
        "blueprint": bp,
        "debug_state": step_result["debug_state"],
        "debug_context": step_result["debug_context"],
        "history": step_result["history"],
        "history_index": step_result["history_index"],
        "breakpoints": breakpoints,
        "watches": watches,
        "max_steps": 1000
    })


# =============================================================================
# INSPECTION
# =============================================================================

def inspect_state(params: Dict[str, Any]) -> Dict[str, Any]:
    """Inspect current state details."""
    bp = params.get("blueprint")
    state = params.get("debug_state")
    avail_trans = params.get("available_transitions", [])

    if not bp or not state:
        return {"output": "No state to inspect"}

    state_info = bp["states"].get(state, {})

    lines = [
        "State Inspection:",
        "=" * 50,
        f"  State: {state}",
        f"  Description: {state_info.get('description', 'N/A')}",
    ]

    if state in bp.get("terminal_states", []):
        lines.append("  [TERMINAL STATE]")

    if state == bp.get("entry_state"):
        lines.append("  [ENTRY STATE]")

    lines.append("")
    lines.append(f"  Available Transitions ({len(avail_trans)}):")
    for t in avail_trans:
        gates = t.get("gates", [])
        gate_str = f" [gates: {gates}]" if gates else ""
        lines.append(f"    {t['event']}: -> {t['to']}{gate_str}")

    lines.append("=" * 50)

    return {"output": "\n".join(lines)}


def inspect_context(params: Dict[str, Any]) -> Dict[str, Any]:
    """Inspect context values."""
    ctx = params.get("debug_context", {})
    key = params.get("key")

    if key:
        value = ctx.get(key, "<not found>")
        return {"output": f"{key} = {json.dumps(value, default=str)}"}

    lines = ["Context:", "=" * 50]
    for k, v in ctx.items():
        if k != "_state":
            val_str = json.dumps(v, default=str)
            if len(val_str) > 60:
                val_str = val_str[:57] + "..."
            lines.append(f"  {k}: {val_str}")
    lines.append("=" * 50)

    return {"output": "\n".join(lines)}


def evaluate_expression(params: Dict[str, Any]) -> Dict[str, Any]:
    """Evaluate an expression in current context."""
    ctx = params.get("debug_context", {})
    expression = params.get("expression")

    if not expression:
        return {"output": "No expression provided"}

    try:
        # Try as boolean expression first
        result, error = safe_eval_bool(expression, ctx)
        if error:
            # Try as value expression
            try:
                result = eval(expression, {"__builtins__": {}}, ctx)
            except Exception as e:
                return {"output": f"Error: {e}"}
        return {"output": f"{expression} = {result}"}
    except Exception as e:
        return {"output": f"Error evaluating: {e}"}


# =============================================================================
# WATCH EXPRESSIONS
# =============================================================================

def add_watch(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add a watch expression."""
    watches = params.get("watches", [])
    expression = params.get("expression")
    name = params.get("name")

    if not expression:
        return {"watches": watches, "output": "Error: expression required"}

    watch_id = name or f"watch_{len(watches) + 1}"
    new_watch = {
        "id": watch_id,
        "name": name or expression[:20],
        "expression": expression
    }

    new_watches = watches + [new_watch]
    return {
        "watches": new_watches,
        "output": f"Watch added: {watch_id} = {expression}"
    }


def remove_watch(params: Dict[str, Any]) -> Dict[str, Any]:
    """Remove a watch expression."""
    watches = params.get("watches", [])
    watch_id = params.get("watch_id")

    if not watch_id:
        return {"watches": watches, "output": "Error: watch_id required"}

    new_watches = [w for w in watches if w["id"] != watch_id]
    if len(new_watches) == len(watches):
        return {"watches": watches, "output": f"Watch {watch_id} not found"}

    return {"watches": new_watches, "output": f"Watch {watch_id} removed"}


def get_watches(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get current watch values."""
    watches = params.get("watches", [])
    ctx = params.get("debug_context", {})

    if not watches:
        return {"watch_values": {}, "output": "No watches set"}

    watch_values = _update_watches(watches, ctx)

    lines = ["Watches:", "=" * 50]
    for watch in watches:
        wid = watch["id"]
        val = watch_values.get(wid, "<unknown>")
        lines.append(f"  {wid}: {watch['expression']} = {val}")
    lines.append("=" * 50)

    return {"watch_values": watch_values, "output": "\n".join(lines)}


# =============================================================================
# HISTORY AND TIME-TRAVEL
# =============================================================================

def get_history(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get execution history."""
    history = params.get("history", [])
    history_index = params.get("history_index", 0)

    if not history:
        return {"output": "No history recorded"}

    lines = ["Execution History:", "=" * 50]
    for entry in history:
        step_num = entry.get("step", 0)
        state = entry.get("state", "?")
        event = entry.get("event")
        prev = entry.get("prev_state")

        marker = " <--" if step_num == history_index else ""

        if event:
            lines.append(f"  [{step_num}] {prev} --[{event}]--> {state}{marker}")
        else:
            lines.append(f"  [{step_num}] Initial: {state}{marker}")

    lines.append("=" * 50)
    lines.append(f"Current position: step {history_index}")

    return {"output": "\n".join(lines)}


def goto_step(params: Dict[str, Any]) -> Dict[str, Any]:
    """Jump to a specific step in history."""
    history = params.get("history", [])
    target_step = params.get("target_step")
    bp = params.get("blueprint")
    watches = params.get("watches", [])

    if target_step is None:
        return {"output": "Error: step number required"}

    target_step = int(target_step)
    if target_step < 0 or target_step >= len(history):
        return {"output": f"Error: step {target_step} out of range (0-{len(history)-1})"}

    entry = history[target_step]
    state = entry["state"]
    ctx = copy.deepcopy(entry["context"])

    avail = _get_available_transitions(bp, state, ctx) if bp else []
    watch_values = _update_watches(watches, ctx)

    return {
        "debug_state": state,
        "debug_context": ctx,
        "history_index": target_step,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "watch_values": watch_values,
        "output": f"Jumped to step {target_step}: state '{state}'"
    }


def compare_states(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compare context at two different history points."""
    history = params.get("history", [])
    step1 = params.get("step1", 0)
    step2 = params.get("step2")

    if step2 is None:
        step2 = len(history) - 1

    step1 = int(step1)
    step2 = int(step2)

    if step1 < 0 or step1 >= len(history):
        return {"output": f"Error: step1 {step1} out of range"}
    if step2 < 0 or step2 >= len(history):
        return {"output": f"Error: step2 {step2} out of range"}

    ctx1 = history[step1].get("context", {})
    ctx2 = history[step2].get("context", {})

    lines = [
        f"Comparing step {step1} vs step {step2}:",
        "=" * 50
    ]

    all_keys = set(ctx1.keys()) | set(ctx2.keys())
    all_keys.discard("_state")

    for key in sorted(all_keys):
        v1 = ctx1.get(key)
        v2 = ctx2.get(key)
        if v1 != v2:
            lines.append(f"  {key}:")
            lines.append(f"    step {step1}: {json.dumps(v1, default=str)}")
            lines.append(f"    step {step2}: {json.dumps(v2, default=str)}")

    state1 = history[step1].get("state", "?")
    state2 = history[step2].get("state", "?")
    if state1 != state2:
        lines.append(f"  State: {state1} -> {state2}")

    if len(lines) == 2:
        lines.append("  No differences found")

    lines.append("=" * 50)

    return {"output": "\n".join(lines)}


# =============================================================================
# RENDERING
# =============================================================================

def render_status(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render current debug status."""
    bp_name = params.get("blueprint_name", "Unknown")
    state = params.get("debug_state", "?")
    ctx = params.get("debug_context", {})
    history_index = params.get("history_index", 0)
    avail_events = params.get("available_events", [])
    breakpoints = params.get("breakpoints", [])
    is_paused = params.get("is_paused", False)
    hit_bp = params.get("hit_breakpoint")

    lines = [
        "=" * 60,
        f"  L++ Debugger: {bp_name}",
        "=" * 60,
    ]

    if is_paused and hit_bp:
        lines.append(f"  ** PAUSED at breakpoint: {hit_bp['id']} **")

    lines.extend([
        f"  State: {state}",
        f"  Step: {history_index}",
        f"  Breakpoints: {len(breakpoints)}",
        "",
        "  Context (non-null):"
    ])

    for k, v in ctx.items():
        if k != "_state" and v is not None:
            val_str = str(v)
            if len(val_str) > 40:
                val_str = val_str[:37] + "..."
            lines.append(f"    {k}: {val_str}")

    lines.append("")
    lines.append(f"  Available Events ({len(avail_events)}):")
    for e in avail_events[:8]:
        lines.append(f"    - {e}")
    if len(avail_events) > 8:
        lines.append(f"    ... and {len(avail_events) - 8} more")

    lines.append("=" * 60)

    return {"output": "\n".join(lines)}


# =============================================================================
# COMPUTE REGISTRY
# =============================================================================

COMPUTE_REGISTRY = {
    "debug:load_blueprint": load_blueprint,
    "debug:init_debug_session": init_debug_session,
    "debug:reset_session": reset_session,
    "debug:set_breakpoint": set_breakpoint,
    "debug:remove_breakpoint": remove_breakpoint,
    "debug:list_breakpoints": list_breakpoints,
    "debug:step": step,
    "debug:step_over": step_over,
    "debug:step_back": step_back,
    "debug:run_to_breakpoint": run_to_breakpoint,
    "debug:continue_execution": continue_execution,
    "debug:inspect_state": inspect_state,
    "debug:inspect_context": inspect_context,
    "debug:evaluate_expression": evaluate_expression,
    "debug:add_watch": add_watch,
    "debug:remove_watch": remove_watch,
    "debug:get_watches": get_watches,
    "debug:get_history": get_history,
    "debug:goto_step": goto_step,
    "debug:compare_states": compare_states,
    "debug:render_status": render_status,
}
