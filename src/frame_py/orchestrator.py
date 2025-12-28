"""
L++ Orchestrator - The Thin Conductor

Minimal orchestrator that runs the execution loop by calling the
four atomic operations in sequence. No business logic here -
just conducts the symphony.
"""

from typing import Any, Optional

from .lpp_core import (
    atom_EVALUATE,
    atom_TRANSITION,
    atom_MUTATE,
    atom_DISPATCH,
    ComputeUnitFunc,
    TransitionTrace,
)
from .schema import Blueprint


def run_frame(
    blueprint: Blueprint,
    context: dict,
    event_name: str,
    event_payload: dict,
    compute_registry: dict[tuple, ComputeUnitFunc]
) -> tuple[str, dict, list[TransitionTrace], Optional[str]]:
    """
    Execute one event dispatch cycle through the frame.

    Args:
        blueprint: The workflow blueprint
        context: Current context data
        event_name: Name of the incoming event
        event_payload: Event payload data
        compute_registry: Dict mapping (system_id, op_id) to callables

    Returns:
        Tuple of (new_state, new_context, traces, error)
        - new_state: The resulting state pointer
        - new_context: The updated context dict
        - traces: List of TransitionTrace records
        - error: Error message if failed, None if success
    """
    current_state = context.get("_state", blueprint.entry_state)
    traces: list[TransitionTrace] = []

    # Check if already terminal
    if current_state in blueprint.terminal_states:
        return current_state, context, traces, "Already in terminal state"

    # Find matching transition
    transition = _find_transition(blueprint, current_state, event_name)
    if not transition:
        return current_state, context, traces, f"No transition: '{event_name}'"

    # Build evaluation scope (context + event)
    eval_scope = dict(context)
    eval_scope["event"] = {"name": event_name, "payload": event_payload}

    # EVALUATE: Check gates
    for gate_id in transition.gates:
        gate = blueprint.get_gate(gate_id)
        if gate and gate.expression:
            if not atom_EVALUATE(gate.expression, eval_scope):
                return current_state, context, \
                    traces, f"Gate '{gate_id}' blocked"

    # Execute actions
    new_context = dict(context)
    for action_id in transition.actions:
        action = blueprint.get_action(action_id)
        if not action:
            continue

        # SET action
        if action.type.value == "set" and action.target:
            value = action.value
            if action.value_from:
                value = _resolve_path(action.value_from, eval_scope)
            new_context = atom_MUTATE(new_context, action.target, value)

        # COMPUTE action
        elif action.type.value == "compute" and action.compute_unit:
            # Parse system_id:operation from compute_unit string
            parts = action.compute_unit.split(":")
            if len(parts) == 2:
                sys_id, op_id = parts
                payload = {
                    k: _resolve_path(v, eval_scope)
                    for k, v in action.input_map.items()
                }
                result = atom_DISPATCH(
                    sys_id, op_id, payload, compute_registry
                )
                # Apply output mapping
                for ctx_path, result_key in action.output_map.items():
                    if result_key in result:
                        new_context = atom_MUTATE(
                            new_context, ctx_path, result[result_key]
                        )

    # TRANSITION: Move to next state
    new_state, trace = atom_TRANSITION(current_state, transition.to_state)
    traces.append(trace)

    # Store state in context
    new_context = atom_MUTATE(new_context, "_state", new_state)

    return new_state, new_context, traces, None


def _find_transition(
    blueprint: Blueprint,
    current_state: str,
    event_name: str
):
    """Find a matching transition for the event."""
    for trans in blueprint.transitions.values():
        if trans.on_event != event_name:
            continue
        if trans.from_state == "*" or trans.from_state == current_state:
            return trans
    return None


def _resolve_path(path: str, data: dict) -> Any:
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


__all__ = [
    'run_frame',
]
