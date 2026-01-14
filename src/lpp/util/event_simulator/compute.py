"""
COMPUTE units for the L++ Event Sequence Simulator.

These are the pure computation functions that the compiled simulator
operator calls. All simulation logic for what-if analysis, state space
exploration, and trace management.
"""

import json
import copy
import random
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from collections import deque
from datetime import datetime

from frame_py.loader import BlueprintLoader
from frame_py.safe_eval import safe_eval_bool


# =============================================================================
# BLUEPRINT LOADING
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file for simulation."""
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

        # Convert to a dict-like structure for simulation
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
# SIMULATION INITIALIZATION
# =============================================================================

def init_simulation(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize simulation state from blueprint."""
    bp = params.get("blueprint")
    if not bp:
        return {"error": "No blueprint provided"}

    # Initialize context from schema defaults
    ctx = {"_state": bp["entry_state"]}
    schema = bp.get("context_schema", {})
    for prop in schema.get("properties", {}).keys():
        ctx[prop] = None

    # Get available events in entry state
    avail = _get_available_transitions(bp, bp["entry_state"], ctx)

    # Create initial trace entry
    trace = [{
        "step": 0,
        "timestamp": datetime.now().isoformat(),
        "state": bp["entry_state"],
        "context": copy.deepcopy(ctx),
        "event": None,
        "transition_id": None
    }]

    return {
        "sim_state": bp["entry_state"],
        "sim_context": ctx,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "trace": trace,
        "forks": {},
        "current_fork": None,
        "mode": "manual"
    }


def reset_simulation(params: Dict[str, Any]) -> Dict[str, Any]:
    """Reset simulation to initial state."""
    bp = params.get("blueprint")
    if not bp:
        return {"error": "No blueprint provided"}

    result = init_simulation({"blueprint": bp})
    result["output"] = f"Reset to initial state: {bp['entry_state']}"
    return result


# =============================================================================
# CONTEXT MANAGEMENT
# =============================================================================

def set_context(params: Dict[str, Any]) -> Dict[str, Any]:
    """Set a context value for simulation."""
    ctx = params.get("sim_context", {})
    key = params.get("key")
    value = params.get("value")

    if not key:
        return {"sim_context": ctx, "error": "No key provided"}

    new_ctx = copy.deepcopy(ctx)
    new_ctx[key] = value

    return {"sim_context": new_ctx}


# =============================================================================
# EVENT DISPATCH AND GATE EVALUATION
# =============================================================================

def _evaluate_gate(bp: Dict, gate_id: str, ctx: Dict) -> bool:
    """Evaluate a single gate."""
    gate = bp["gates"].get(gate_id)
    if not gate:
        return True

    if gate["type"] == "expression":
        expr = gate.get("expression", "True")
        result, _ = safe_eval_bool(expr, ctx)
        return result
    elif gate["type"] == "compute":
        # For simulation, compute gates default to True
        return True

    return True


def _get_available_transitions(
    bp: Dict, state: str, ctx: Dict
) -> List[Dict]:
    """Get all transitions available from current state with passing gates."""
    available = []
    eval_ctx = copy.deepcopy(ctx)
    eval_ctx["_state"] = state

    for t in bp["transitions"]:
        # Check from state
        if t["from"] != "*" and t["from"] != state:
            continue

        # Check all gates
        gates_pass = True
        for gate_id in t.get("gates", []):
            if not _evaluate_gate(bp, gate_id, eval_ctx):
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


def get_available_events(params: Dict[str, Any]) -> Dict[str, Any]:
    """List valid events in current state."""
    bp = params.get("blueprint")
    state = params.get("sim_state")
    ctx = params.get("sim_context", {})

    if not bp or not state:
        return {"available_events": [], "available_transitions": []}

    avail = _get_available_transitions(bp, state, ctx)
    events = list(set(t["event"] for t in avail))

    return {
        "available_events": events,
        "available_transitions": avail
    }


def evaluate_gates(params: Dict[str, Any]) -> Dict[str, Any]:
    """Evaluate all gates with current context."""
    bp = params.get("blueprint")
    ctx = params.get("sim_context", {})

    if not bp:
        return {"output": "No blueprint"}

    lines = ["Gate Evaluation Results:", "=" * 40]
    for gate_id, gate in bp.get("gates", {}).items():
        if gate["type"] == "expression":
            result, _ = safe_eval_bool(gate["expression"], ctx)
            status = "PASS" if result else "FAIL"
            lines.append(f"  [{status}] {gate_id}: {gate['expression']}")
        else:
            lines.append(f"  [SKIP] {gate_id}: compute gate")

    return {"output": "\n".join(lines)}


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


def _execute_action(
    bp: Dict, action_id: str, ctx: Dict, event_payload: Dict
) -> Dict:
    """Execute a single action and return updated context."""
    action = bp["actions"].get(action_id)
    if not action:
        return ctx

    new_ctx = copy.deepcopy(ctx)
    scope = {"event": {"payload": event_payload or {}}}
    scope.update(ctx)

    if action["type"] == "set":
        target = action.get("target")
        if target:
            if action.get("value") is not None:
                new_ctx[target] = action["value"]
            elif action.get("value_from"):
                new_ctx[target] = _resolve_path(action["value_from"], scope)
            else:
                new_ctx[target] = None

    elif action["type"] == "compute":
        # For simulation, we skip actual compute execution
        # but can update context based on output_map if needed
        pass

    return new_ctx


def dispatch_event(params: Dict[str, Any]) -> Dict[str, Any]:
    """Dispatch an event and process state transition."""
    bp = params.get("blueprint")
    state = params.get("sim_state")
    ctx = params.get("sim_context", {})
    trace = params.get("trace", [])
    event_name = params.get("event_name")
    event_payload = params.get("event_payload", {})

    if not bp or not state or not event_name:
        return {"error": "Missing required parameters"}

    # Find matching transition
    eval_ctx = copy.deepcopy(ctx)
    eval_ctx["_state"] = state

    matched = None
    for t in bp["transitions"]:
        if t["on_event"] != event_name:
            continue
        if t["from"] != "*" and t["from"] != state:
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
            "trace": trace,
            "available_events": [],
            "available_transitions": [],
            "output": f"No matching transition for event '{event_name}'",
            "error": f"No transition for {event_name} from {state}"
        }

    # Execute actions
    new_ctx = copy.deepcopy(ctx)
    for action_id in matched.get("actions", []):
        new_ctx = _execute_action(bp, action_id, new_ctx, event_payload)

    # Perform transition
    new_state = matched["to"]
    new_ctx["_state"] = new_state

    # Record in trace
    new_trace = copy.deepcopy(trace)
    new_trace.append({
        "step": len(trace),
        "timestamp": datetime.now().isoformat(),
        "state": new_state,
        "prev_state": state,
        "context": copy.deepcopy(new_ctx),
        "event": event_name,
        "event_payload": event_payload,
        "transition_id": matched["id"]
    })

    # Get new available transitions
    avail = _get_available_transitions(bp, new_state, new_ctx)

    output = f"{state} --[{event_name}]--> {new_state}"
    if matched.get("actions"):
        output += f" (actions: {', '.join(matched['actions'])})"

    return {
        "sim_state": new_state,
        "sim_context": new_ctx,
        "trace": new_trace,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "output": output,
        "error": None
    }


# =============================================================================
# FORKING AND WHAT-IF ANALYSIS
# =============================================================================

def fork_simulation(params: Dict[str, Any]) -> Dict[str, Any]:
    """Create a fork of current simulation state for what-if analysis."""
    forks = params.get("forks", {})
    fork_name = params.get("fork_name")
    state = params.get("sim_state")
    ctx = params.get("sim_context", {})
    trace = params.get("trace", [])

    if not fork_name:
        fork_name = f"fork_{len(forks) + 1}"

    new_forks = copy.deepcopy(forks)
    new_forks[fork_name] = {
        "sim_state": state,
        "sim_context": copy.deepcopy(ctx),
        "trace": copy.deepcopy(trace),
        "created_at": datetime.now().isoformat()
    }

    return {
        "forks": new_forks,
        "current_fork": fork_name,
        "output": f"Created fork '{fork_name}' at state {state}"
    }


def switch_fork(params: Dict[str, Any]) -> Dict[str, Any]:
    """Switch to a different simulation fork."""
    forks = params.get("forks", {})
    fork_name = params.get("fork_name")

    if not fork_name or fork_name not in forks:
        return {
            "error": f"Fork '{fork_name}' not found",
            "output": f"Available forks: {list(forks.keys())}"
        }

    fork = forks[fork_name]
    return {
        "sim_state": fork["sim_state"],
        "sim_context": copy.deepcopy(fork["sim_context"]),
        "trace": copy.deepcopy(fork["trace"]),
        "current_fork": fork_name,
        "available_events": [],
        "available_transitions": [],
        "output": f"Switched to fork '{fork_name}' at state {fork['sim_state']}",
        "error": None
    }


# =============================================================================
# STEP BACK / UNDO
# =============================================================================

def step_back(params: Dict[str, Any]) -> Dict[str, Any]:
    """Step back to previous state from trace."""
    trace = params.get("trace", [])
    bp = params.get("blueprint")

    if len(trace) < 2:
        return {"output": "Cannot step back - at initial state"}

    # Go to previous step
    new_trace = trace[:-1]
    prev_step = new_trace[-1]

    state = prev_step["state"]
    ctx = copy.deepcopy(prev_step["context"])

    avail = _get_available_transitions(bp, state, ctx) if bp else []

    return {
        "sim_state": state,
        "sim_context": ctx,
        "trace": new_trace,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "output": f"Stepped back to state: {state} (step {len(new_trace) - 1})"
    }


# =============================================================================
# SEQUENCE EXECUTION
# =============================================================================

def set_sequence(params: Dict[str, Any]) -> Dict[str, Any]:
    """Set an event sequence for execution."""
    events = params.get("events", [])

    if isinstance(events, str):
        # Parse comma-separated string
        events = [e.strip() for e in events.split(",") if e.strip()]

    return {
        "sequence": events,
        "sequence_index": 0,
        "mode": "sequence"
    }


def run_sequence(params: Dict[str, Any]) -> Dict[str, Any]:
    """Execute a pre-defined event sequence."""
    bp = params.get("blueprint")
    state = params.get("sim_state")
    ctx = params.get("sim_context", {})
    trace = params.get("trace", [])
    sequence = params.get("sequence", [])

    if not sequence:
        return {"output": "No sequence defined", "error": "Empty sequence"}

    results = []
    current_state = state
    current_ctx = copy.deepcopy(ctx)
    current_trace = copy.deepcopy(trace)

    for i, event in enumerate(sequence):
        result = dispatch_event({
            "blueprint": bp,
            "sim_state": current_state,
            "sim_context": current_ctx,
            "trace": current_trace,
            "event_name": event,
            "event_payload": {}
        })

        if result.get("error"):
            results.append(f"Step {i+1}: FAILED - {event} ({result['error']})")
            break
        else:
            results.append(f"Step {i+1}: {result['output']}")
            current_state = result["sim_state"]
            current_ctx = result["sim_context"]
            current_trace = result["trace"]

    avail = _get_available_transitions(bp, current_state, current_ctx)

    return {
        "sim_state": current_state,
        "sim_context": current_ctx,
        "trace": current_trace,
        "sequence_index": len(sequence),
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "output": "\n".join(["Sequence Execution:", "-" * 40] + results),
        "error": None
    }


# =============================================================================
# FUZZING
# =============================================================================

def fuzz_run(params: Dict[str, Any]) -> Dict[str, Any]:
    """Random event exploration to discover state space."""
    bp = params.get("blueprint")
    state = params.get("sim_state")
    ctx = params.get("sim_context", {})
    trace = params.get("trace", [])
    steps = params.get("steps", 10)
    seed = params.get("seed")

    if seed is not None:
        random.seed(seed)

    current_state = state
    current_ctx = copy.deepcopy(ctx)
    current_trace = copy.deepcopy(trace)
    visited_states = {state}
    transitions_taken = []
    deadends = 0

    for i in range(steps):
        avail = _get_available_transitions(bp, current_state, current_ctx)
        if not avail:
            deadends += 1
            transitions_taken.append(f"Step {i+1}: DEADEND at {current_state}")
            break

        # Pick random available transition
        chosen = random.choice(avail)
        event = chosen["event"]

        result = dispatch_event({
            "blueprint": bp,
            "sim_state": current_state,
            "sim_context": current_ctx,
            "trace": current_trace,
            "event_name": event,
            "event_payload": {}
        })

        if not result.get("error"):
            transitions_taken.append(
                f"Step {i+1}: {current_state} --[{event}]--> "
                f"{result['sim_state']}"
            )
            current_state = result["sim_state"]
            current_ctx = result["sim_context"]
            current_trace = result["trace"]
            visited_states.add(current_state)
        else:
            transitions_taken.append(
                f"Step {i+1}: FAILED {event} - {result['error']}"
            )

    avail = _get_available_transitions(bp, current_state, current_ctx)

    fuzz_result = {
        "steps_executed": len(transitions_taken),
        "states_visited": list(visited_states),
        "unique_states": len(visited_states),
        "deadends": deadends,
        "final_state": current_state
    }

    output_lines = [
        f"Fuzz Run ({steps} steps requested):",
        "=" * 50
    ] + transitions_taken + [
        "=" * 50,
        f"Visited {len(visited_states)} unique states: "
        f"{', '.join(visited_states)}",
        f"Final state: {current_state}"
    ]

    return {
        "sim_state": current_state,
        "sim_context": current_ctx,
        "trace": current_trace,
        "fuzz_result": fuzz_result,
        "available_events": [t["event"] for t in avail],
        "available_transitions": avail,
        "output": "\n".join(output_lines)
    }


# =============================================================================
# STATE SPACE EXPLORATION
# =============================================================================

def explore_state_space(params: Dict[str, Any]) -> Dict[str, Any]:
    """Enumerate all reachable states using BFS."""
    bp = params.get("blueprint")
    start_state = params.get("sim_state")
    start_ctx = params.get("sim_context", {})
    max_depth = params.get("max_depth", 10)

    if not bp:
        return {"output": "No blueprint", "state_space": None}

    # BFS exploration
    visited = set()
    edges = []
    queue = deque([(start_state, copy.deepcopy(start_ctx), 0)])
    state_info = {}

    while queue:
        state, ctx, depth = queue.popleft()

        state_key = state
        if state_key in visited:
            continue
        visited.add(state_key)

        if depth >= max_depth:
            continue

        avail = _get_available_transitions(bp, state, ctx)
        state_info[state] = {
            "available_events": [t["event"] for t in avail],
            "is_terminal": state in bp.get("terminal_states", [])
        }

        for trans in avail:
            target = trans["to"]
            edges.append({
                "from": state,
                "to": target,
                "event": trans["event"],
                "transition_id": trans["id"]
            })

            if target not in visited:
                # Simple context propagation (no action execution)
                new_ctx = copy.deepcopy(ctx)
                new_ctx["_state"] = target
                queue.append((target, new_ctx, depth + 1))

    state_space = {
        "states": list(visited),
        "edges": edges,
        "state_info": state_info,
        "start_state": start_state,
        "total_states": len(visited),
        "total_edges": len(edges)
    }

    lines = [
        "State Space Exploration:",
        "=" * 50,
        f"Reachable states ({len(visited)}):"
    ]
    for s in sorted(visited):
        info = state_info.get(s, {})
        terminal = " [TERMINAL]" if info.get("is_terminal") else ""
        events = info.get("available_events", [])
        lines.append(f"  - {s}{terminal} -> events: {events}")

    lines.append(f"\nEdges ({len(edges)}):")
    for e in edges:
        lines.append(f"  {e['from']} --[{e['event']}]--> {e['to']}")

    return {
        "state_space": state_space,
        "output": "\n".join(lines)
    }


# =============================================================================
# PATH FINDING
# =============================================================================

def find_path(params: Dict[str, Any]) -> Dict[str, Any]:
    """Find event sequence to reach target state using BFS."""
    bp = params.get("blueprint")
    start_state = params.get("sim_state")
    start_ctx = params.get("sim_context", {})
    target = params.get("target_state")

    if not bp or not target:
        return {"output": "Missing blueprint or target", "path_result": None}

    if start_state == target:
        return {
            "path_result": {"path": [], "found": True},
            "output": f"Already at target state: {target}"
        }

    # BFS for shortest path
    visited = set()
    queue = deque([(start_state, copy.deepcopy(start_ctx), [])])

    while queue:
        state, ctx, path = queue.popleft()

        if state in visited:
            continue
        visited.add(state)

        avail = _get_available_transitions(bp, state, ctx)

        for trans in avail:
            new_path = path + [{
                "from": state,
                "event": trans["event"],
                "to": trans["to"],
                "transition_id": trans["id"]
            }]

            if trans["to"] == target:
                # Found path
                events = [p["event"] for p in new_path]
                lines = [
                    f"Path to '{target}' found!",
                    "=" * 50,
                    f"Steps: {len(new_path)}",
                    f"Events: {' -> '.join(events)}",
                    "",
                    "Detailed path:"
                ]
                for i, p in enumerate(new_path):
                    lines.append(
                        f"  {i+1}. {p['from']} --[{p['event']}]--> {p['to']}"
                    )

                return {
                    "path_result": {
                        "found": True,
                        "path": new_path,
                        "events": events
                    },
                    "output": "\n".join(lines)
                }

            if trans["to"] not in visited:
                new_ctx = copy.deepcopy(ctx)
                new_ctx["_state"] = trans["to"]
                queue.append((trans["to"], new_ctx, new_path))

    return {
        "path_result": {"found": False, "path": []},
        "output": f"No path found from '{start_state}' to '{target}'"
    }


# =============================================================================
# TRACE EXPORT/IMPORT
# =============================================================================

def export_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export simulation trace to JSON file."""
    trace = params.get("trace", [])
    blueprint_id = params.get("blueprint_id", "unknown")
    path = params.get("path")

    if not trace:
        return {"output": "No trace to export"}

    if not path:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        path = f"./traces/{blueprint_id}_{timestamp}.json"

    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)

    # Extract events for replay
    events = []
    for step in trace[1:]:  # Skip initial state
        if step.get("event"):
            events.append({
                "event": step["event"],
                "payload": step.get("event_payload", {})
            })

    export_data = {
        "blueprint_id": blueprint_id,
        "exported_at": datetime.now().isoformat(),
        "trace": trace,
        "events": events,
        "final_state": trace[-1]["state"] if trace else None
    }

    with open(path, "w") as f:
        json.dump(export_data, f, indent=2)

    return {"output": f"Trace exported to: {path}"}


def import_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Import and prepare trace for replay."""
    path = params.get("path")

    if not path:
        return {"error": "No path provided"}

    path = Path(path)
    if not path.exists():
        return {"error": f"File not found: {path}"}

    try:
        with open(path) as f:
            data = json.load(f)

        events = data.get("events", [])
        sequence = [e["event"] for e in events]

        return {
            "trace": data.get("trace", []),
            "sequence": sequence,
            "mode": "replay",
            "output": (
                f"Imported trace with {len(events)} events. "
                f"Use RUN_SEQUENCE to replay."
            ),
            "error": None
        }
    except Exception as e:
        return {"error": str(e)}


# =============================================================================
# RENDERING
# =============================================================================

def render_status(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render current simulation status."""
    bp_name = params.get("blueprint_name", "Unknown")
    state = params.get("sim_state", "?")
    ctx = params.get("sim_context", {})
    avail_events = params.get("available_events", [])
    trace = params.get("trace", [])
    mode = params.get("mode", "manual")
    fork = params.get("current_fork")

    lines = [
        "=" * 60,
        f"  L++ Simulator: {bp_name}",
        "=" * 60,
        f"  Mode: {mode}" + (f" (fork: {fork})" if fork else ""),
        f"  State: {state}",
        f"  Steps: {len(trace) - 1}",
        "",
        "  Context:",
    ]

    for k, v in ctx.items():
        if k != "_state" and v is not None:
            lines.append(f"    {k}: {v}")

    lines.append("")
    lines.append(f"  Available Events ({len(avail_events)}):")
    for e in avail_events[:10]:
        lines.append(f"    - {e}")
    if len(avail_events) > 10:
        lines.append(f"    ... and {len(avail_events) - 10} more")

    lines.append("=" * 60)

    return {"output": "\n".join(lines)}


def render_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render execution trace."""
    trace = params.get("trace", [])

    if not trace:
        return {"output": "No trace recorded"}

    lines = [
        "Execution Trace:",
        "=" * 50
    ]

    for step in trace:
        step_num = step.get("step", 0)
        state = step.get("state", "?")
        event = step.get("event")
        prev = step.get("prev_state")

        if event:
            lines.append(f"  [{step_num}] {prev} --[{event}]--> {state}")
        else:
            lines.append(f"  [{step_num}] Initial: {state}")

    lines.append("=" * 50)
    lines.append(f"Total steps: {len(trace) - 1}")

    return {"output": "\n".join(lines)}


def render_state_space(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render explored state space."""
    space = params.get("state_space")

    if not space:
        return {"output": "No state space explored"}

    lines = [
        "State Space Graph:",
        "=" * 50,
        f"States: {space.get('total_states', 0)}",
        f"Edges: {space.get('total_edges', 0)}",
        "",
        "Mermaid Diagram:",
        "```mermaid",
        "stateDiagram-v2"
    ]

    start = space.get("start_state")
    if start:
        lines.append(f"    [*] --> {start}")

    for edge in space.get("edges", []):
        lines.append(
            f"    {edge['from']} --> {edge['to']}: {edge['event']}"
        )

    lines.append("```")

    return {"output": "\n".join(lines)}


# =============================================================================
# COMPUTE REGISTRY
# =============================================================================

COMPUTE_REGISTRY = {
    ("sim", "load_blueprint"): load_blueprint,
    ("sim", "init_simulation"): init_simulation,
    ("sim", "reset_simulation"): reset_simulation,
    ("sim", "set_context"): set_context,
    ("sim", "dispatch_event"): dispatch_event,
    ("sim", "get_available_events"): get_available_events,
    ("sim", "evaluate_gates"): evaluate_gates,
    ("sim", "fork_simulation"): fork_simulation,
    ("sim", "switch_fork"): switch_fork,
    ("sim", "step_back"): step_back,
    ("sim", "set_sequence"): set_sequence,
    ("sim", "run_sequence"): run_sequence,
    ("sim", "fuzz_run"): fuzz_run,
    ("sim", "find_path"): find_path,
    ("sim", "explore_state_space"): explore_state_space,
    ("sim", "export_trace"): export_trace,
    ("sim", "import_trace"): import_trace,
    ("sim", "render_status"): render_status,
    ("sim", "render_trace"): render_trace,
    ("sim", "render_state_space"): render_state_space,
}
