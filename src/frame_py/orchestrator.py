"""
L++ Orchestrator - The Thin Conductor

Minimal orchestrator that runs the execution loop by calling the
four atomic operations in sequence. No business logic here -
just conducts the symphony.

State Machine (from orchestrator_blueprint.json):
    idle → finding_transition → evaluating_gates →
            ↓                    ↓
          error               error              
    executing_actions → transitioning → complete
        ↓
    error
Transitions:
    DISPATCH_EVENT: idle → finding_transition
    TRANSITION_FOUND: finding_transition → evaluating_gates
    NO_TRANSITION: finding_transition → error
    GATES_PASSED: evaluating_gates → executing_actions
    GATES_FAILED: evaluating_gates → error
    ACTIONS_DONE: executing_actions → transitioning
    ACTION_ERROR: executing_actions → error
    TRANSITION_DONE: transitioning → complete
    RESET: * → idle
"""

from typing import Any, Optional
from enum import Enum

from .lpp_core import (
    atom_EVALUATE,
    atom_TRANSITION,
    atom_MUTATE,
    atom_DISPATCH,
    ComputeUnitFunc,
    TransitionTrace,
)
from .schema import Blueprint


class OrchestratorState(Enum):
    """Orchestrator state machine states."""
    IDLE = "idle"
    FINDING_TRANSITION = "finding_transition"
    EVALUATING_GATES = "evaluating_gates"
    EXECUTING_ACTIONS = "executing_actions"
    TRANSITIONING = "transitioning"
    COMPLETE = "complete"
    ERROR = "error"


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

    State machine:
        idle → finding_transition → evaluating_gates →
        executing_actions → transitioning → complete | error
    """
    orch_state = OrchestratorState.IDLE
    current_state = context.get("_state", blueprint.entry_state)
    traces: list[TransitionTrace] = []
    error_msg: Optional[str] = None

    # Gate: g_not_terminal - Check if already terminal
    if current_state in blueprint.terminal_states:
        return current_state, context, traces, "Already in terminal state"

    # =========================================================================
    # DISPATCH_EVENT: idle → finding_transition
    # =========================================================================
    orch_state = OrchestratorState.FINDING_TRANSITION

    transition = _find_transition(blueprint, current_state, event_name)

    if not transition:
        # NO_TRANSITION: finding_transition → error
        orch_state = OrchestratorState.ERROR
        return current_state, context, traces, f"NO_TRANSITION: '{event_name}'"

    # =========================================================================
    # TRANSITION_FOUND: finding_transition → evaluating_gates
    # =========================================================================
    orch_state = OrchestratorState.EVALUATING_GATES

    # Build evaluation scope (context + event)
    eval_scope = dict(context)
    eval_scope["event"] = {"name": event_name, "payload": event_payload}

    # EVALUATE: Check gates
    for gate_id in transition.gates:
        gate = blueprint.get_gate(gate_id)
        if gate and gate.expression:
            result, eval_error = atom_EVALUATE(gate.expression, eval_scope)
            if eval_error:
                # GATES_FAILED: evaluating_gates → error
                orch_state = OrchestratorState.ERROR
                return current_state,context, traces, f"GATES_FAILED: {eval_error}"
            if not result:
                # GATES_FAILED: evaluating_gates → error
                orch_state = OrchestratorState.ERROR
                return current_state, context, traces, f"GATES_FAILED: '{gate_id}' blocked"

    # =========================================================================
    # GATES_PASSED: evaluating_gates → executing_actions
    # =========================================================================
    orch_state = OrchestratorState.EXECUTING_ACTIONS

    # Execute actions
    new_context = dict(context)
    for action_id in transition.actions:
        action = blueprint.get_action(action_id)
        if not action:
            continue

        try:
            # SET action
            if action.type.value == "set" and action.target:
                value = action.value
                if action.value_from:
                    value = _resolve_path(action.value_from, eval_scope)
                new_context, mutate_error = atom_MUTATE(new_context, action.target, value)
                if mutate_error:
                    # ACTION_ERROR: executing_actions → error
                    orch_state = OrchestratorState.ERROR
                    return current_state, context, traces, f"ACTION_ERROR: {mutate_error}"

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
                    result, dispatch_error = atom_DISPATCH(
                        sys_id, op_id, payload, compute_registry
                    )
                    if dispatch_error:
                        # ACTION_ERROR: executing_actions → error
                        orch_state = OrchestratorState.ERROR
                        return current_state, context, traces, f"ACTION_ERROR: {dispatch_error}"

                    # Apply output mapping
                    for ctx_path, result_key in action.output_map.items():
                        if result_key in result:
                            new_context, mutate_error = atom_MUTATE(
                                new_context, ctx_path, result[result_key]
                            )
                            if mutate_error:
                                orch_state = OrchestratorState.ERROR
                                return current_state, context, traces, f"ACTION_ERROR: {mutate_error}"

        except Exception as e:
            # ACTION_ERROR: executing_actions → error
            orch_state = OrchestratorState.ERROR
            return current_state, context, traces, f"ACTION_ERROR: {str(e)}"

    # =========================================================================
    # ACTIONS_DONE: executing_actions → transitioning
    # =========================================================================
    orch_state = OrchestratorState.TRANSITIONING

    # TRANSITION: Move to next state
    (new_state, trace), trans_error = atom_TRANSITION(current_state, transition.to_state)
    traces.append(trace)

    if trans_error:
        # Note: We still completed the transition but log the error
        pass

    # Store state in context
    new_context, _ = atom_MUTATE(new_context, "_state", new_state)

    # =========================================================================
    # TRANSITION_DONE: transitioning → complete
    # =========================================================================
    orch_state = OrchestratorState.COMPLETE

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
    'OrchestratorState',
]
