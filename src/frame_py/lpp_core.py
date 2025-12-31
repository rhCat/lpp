"""
L++ Atomic Core - Pure Python Primitives

The "assembly language" of the L++ logic engine.
Four atomic operations using only built-in Python primitives.
No classes, no objects, no external libraries.

    atom_EVALUATE   - The Judge
    atom_TRANSITION - The Navigator
    atom_MUTATE     - The Scribe
    atom_DISPATCH   - The Messenger

This is the absolute bedrock. The entire L++ universe, no matter how
complex, will be built by an orchestrator loop just calling these
four functions in different sequences.

State Machine (from lpp_core_blueprint.json):
    idle → evaluating|transitioning|mutating|dispatching → complete|error

Error Handling:
    Each atom returns (result, error) tuple where error is None on success.
    This enables the orchestrator to trigger EVAL_ERROR, TRANS_ERROR, etc.
"""

import datetime
from typing import Any, Callable, Dict, NamedTuple, Optional, Tuple


# Type alias for hermetic compute unit function signature
ComputeUnitFunc = Callable[[Dict[str, Any]], Dict[str, Any]]


class AtomError(Exception):
    """Base exception for atomic operation failures."""
    pass


class EvaluateError(AtomError):
    """Error during atom_EVALUATE execution."""
    pass


class TransitionError(AtomError):
    """Error during atom_TRANSITION execution."""
    pass


class MutateError(AtomError):
    """Error during atom_MUTATE execution."""
    pass


class DispatchError(AtomError):
    """Error during atom_DISPATCH execution."""
    pass


# A structured record of what happened, for the engine's internal history
class TransitionTrace(NamedTuple):
    """Kernel-level trace record for state transitions."""
    timestamp: datetime.datetime
    from_id: str
    to_id: str
    error: Optional[str] = None  # Error message if transition failed


# =========================================================================
# ATOM: EVALUATE (The Judge)
# =========================================================================

def atom_EVALUATE(
    expression: str,
    context_data: dict
) -> Tuple[bool, Optional[str]]:
    """
    Atomic unit to evaluate a boolean expression against a data context.
    Uses the safe expression evaluator for deterministic, secure execution.

    Args:
        expression: A Python boolean expression (e.g., "amount > 1000")
        context_data: The data dictionary for variable resolution

    Returns:
        Tuple of (result, error):
        - result: True/False if successful, False on error
        - error: None on success, error message string on failure

    Transitions (blueprint):
        idle → evaluating (EVALUATE)
        evaluating → complete (EVAL_DONE) | error (EVAL_ERROR)

    Security:
        Uses safe_eval which only allows:
        - Boolean logic: and, or, not
        - Comparisons: ==, !=, <, >, <=, >=
        - Membership: in, not in
        - Null checks: is None, is not None
        - Context variable access
        - Literals: numbers, strings, True, False, None

        Blocked: imports, builtins, time, random, file access, etc.
    """
    # Gate: g_has_expression
    if expression is None:
        return False, "EVAL_ERROR: expression is None"

    try:
        from .safe_eval import safe_eval_bool
        result, eval_error = safe_eval_bool(expression, context_data)
        if eval_error:
            return False, eval_error
        return result, None  # EVAL_DONE
    except Exception as e:
        return False, f"EVAL_ERROR: {str(e)}"  # → error state


# =========================================================================
# ATOM: TRANSITION (The Navigator)
# =========================================================================

def atom_TRANSITION(
    current_id: str,
    target_id: str,
    valid_states: Optional[set] = None
) -> Tuple[Tuple[str, TransitionTrace], Optional[str]]:
    """
    Atomic unit to update the execution pointer.
    Performs the move and generates a kernel-level trace record.

    Args:
        current_id: The current state identifier
        target_id: The target state identifier
        valid_states: Optional set of valid state IDs for validation

    Returns:
        Tuple of ((new_pointer, trace_record), error):
        - new_pointer: The target_id (the new state)
        - trace_record: TransitionTrace for the engine's verifiable history
        - error: None on success, error message on failure

    Transitions (blueprint):
        idle → transitioning (TRANSITION)
        transitioning → complete (TRANS_DONE) | error (TRANS_ERROR)

    Note:
        The trace is for the engine's own internal history stack, NOT an
        external action log. The orchestrator decides what to do with it.
    """
    error_msg = None

    # Validate states if valid_states provided
    if valid_states is not None:
        if current_id not in valid_states:
            error_msg = f"TRANS_ERROR: invalid current_id '{current_id}'"
        elif target_id not in valid_states:
            error_msg = f"TRANS_ERROR: invalid target_id '{target_id}'"

    # 1. Perform the core function: Define the new state pointer
    new_pointer = target_id

    # 2. Generate the internal trace record
    trace = TransitionTrace(
        timestamp=datetime.datetime.now(datetime.timezone.utc),
        from_id=current_id,
        to_id=target_id,
        error=error_msg
    )

    # Return the new state AND the trace of the operation
    return (new_pointer, trace), error_msg


# =========================================================================
# ATOM: MUTATE (The Scribe)
# =========================================================================

def atom_MUTATE(
    context_data: dict,
    path: str,
    value: Any
) -> Tuple[dict, Optional[str]]:
    """
    Atomic unit to update the data context at a specific path.
    Returns a SHALLOW COPY of the newly updated context.

    Args:
        context_data: The current context dictionary
        path: Dot-notation path (e.g., "user.profile.email")
        value: The value to set at the path

    Returns:
        Tuple of (new_context, error):
        - new_context: New dictionary with the value updated at path
        - error: None on success, error message on failure

    Transitions (blueprint):
        idle → mutating (MUTATE)
        mutating → complete (MUTATE_DONE) | error (MUTATE_ERROR)

    Note:
        Uses shallow copy for efficiency. For absolute purity with nested
        shared references, deep copy could be used at the cost of performance.
    """
    # Gate: g_valid_path
    if path is None or len(path) == 0:
        return context_data, "MUTATE_ERROR: path is None or empty"

    try:
        # Create a shallow copy to ensure the input dictionary is not modified
        new_context = context_data.copy()

        keys = path.split('.')
        current_level = new_context

        # Navigate down to the second-to-last key
        for key in keys[:-1]:
            if key not in current_level or not isinstance(
                current_level[key], dict
            ):
                # If the path doesn't exist, create intermediate dictionaries
                current_level[key] = {}
            else:
                # Copy the nested dict to avoid mutating the original
                current_level[key] = current_level[key].copy()
            current_level = current_level[key]

        # Set the value at the final key
        final_key = keys[-1]
        current_level[final_key] = value

        return new_context, None  # MUTATE_DONE

    except Exception as e:
        return context_data, f"MUTATE_ERROR: {str(e)}"  # → error state


# =========================================================================
# ATOM: DISPATCH (The Messenger)
# =========================================================================

def atom_DISPATCH(
    system_id: str,
    operation_id: str,
    payload: dict,
    compute_registry: Dict[tuple, ComputeUnitFunc]
) -> Tuple[dict, Optional[str]]:
    """
    Atomic unit to pass a payload across the boundary to a compute unit.
    Handles the lookup and standard I/O execution.

    Args:
        system_id: The system namespace (e.g., "pricing", "risk")
        operation_id: The operation name (e.g., "calculate", "assess")
        payload: The input payload dictionary
        compute_registry: Dict mapping (system_id, operation_id) to callables

    Returns:
        Tuple of (result_payload, error):
        - result_payload: The result from compute unit, or error dict
        - error: None on success, error message on failure

    Transitions (blueprint):
        idle → dispatching (DISPATCH)
        dispatching → complete (DISPATCH_DONE) | error (DISPATCH_ERROR)

    Note:
        The Frame must never crash. All compute unit failures are caught
        and returned as standardized error payloads.
    """
    registry_key = (system_id, operation_id)
    compute_func = compute_registry.get(registry_key)

    if not compute_func:
        # Deterministic error handling: return a standard error payload
        error_msg = "DISPATCH_ERROR: No compute unit for " \
            f"{system_id}:{operation_id}"
        print(f"[L++ CORE ERROR] {error_msg}")
        return {
            "error": "COMPUTE_UNIT_NOT_FOUND", "status": "failed"
        }, error_msg

    try:
        # Execute the hermetic unit with standard I/O
        print(
            f"[L++ CORE] Dispatching to {system_id}:{operation_id} "
            f"with payload: {payload}"
        )
        result_payload = compute_func(payload)

        # Enforce the output contract: must be a dictionary
        if not isinstance(result_payload, dict):
            error_msg = "DISPATCH_ERROR: Invalid compute output type"
            return {
                "error": "INVALID_COMPUTE_OUTPUT_TYPE", "status": "failed"
            }, error_msg

        # Check if compute returned an error
        if result_payload.get("status") == "failed":
            error_msg = "DISPATCH_ERROR: " + \
                f"{result_payload.get('error', 'unknown')}"
            return result_payload, error_msg

        return result_payload, None  # DISPATCH_DONE

    except Exception as e:
        # Catch any crashes in the volatile compute layer
        error_msg = f"DISPATCH_ERROR: {str(e)}"
        print(f"[L++ CORE ERROR] Compute unit failed: {e}")
        return {"error": str(e), "status": "failed"}, error_msg


# =========================================================================
# EXPORTS
# =========================================================================

__all__ = [
    'atom_EVALUATE',
    'atom_TRANSITION',
    'atom_MUTATE',
    'atom_DISPATCH',
    'ComputeUnitFunc',
    'TransitionTrace',
    'AtomError',
    'EvaluateError',
    'TransitionError',
    'MutateError',
    'DispatchError',
]
