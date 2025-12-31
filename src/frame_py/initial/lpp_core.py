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
"""

import datetime
from typing import Any, Callable, Dict, NamedTuple

# Type alias for hermetic compute unit function signature
ComputeUnitFunc = Callable[[Dict[str, Any]], Dict[str, Any]]


# A structured record of what happened, for the engine's internal history
class TransitionTrace(NamedTuple):
    """Kernel-level trace record for state transitions."""
    timestamp: datetime.datetime
    from_id: str
    to_id: str


# =========================================================================
# ATOM: EVALUATE (The Judge)
# =========================================================================

def atom_EVALUATE(expression: str, context_data: dict) -> bool:
    """
    Atomic unit to evaluate a boolean expression against a data context.
    Uses the safe expression evaluator for deterministic, secure execution.

    Args:
        expression: A Python boolean expression (e.g., "amount > 1000")
        context_data: The data dictionary for variable resolution

    Returns:
        True if expression evaluates truthy, False otherwise

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
    from .safe_eval import safe_eval_bool
    return safe_eval_bool(expression, context_data)


# =========================================================================
# ATOM: TRANSITION (The Navigator)
# =========================================================================

def atom_TRANSITION(
    current_id: str,
    target_id: str
) -> tuple[str, TransitionTrace]:
    """
    Atomic unit to update the execution pointer.
    Performs the move and generates a kernel-level trace record.

    Args:
        current_id: The current state identifier
        target_id: The target state identifier

    Returns:
        Tuple of (new_pointer, trace_record)
        - new_pointer: The target_id (the new state)
        - trace_record: TransitionTrace for the engine's verifiable history

    Note:
        The trace is for the engine's own internal history stack, NOT an
        external action log. The orchestrator decides what to do with it.
    """
    # 1. Perform the core function: Define the new state pointer
    new_pointer = target_id

    # 2. Generate the internal trace record
    trace = TransitionTrace(
        timestamp=datetime.datetime.now(datetime.timezone.utc),
        from_id=current_id,
        to_id=target_id
    )

    # Return the new state AND the trace of the operation
    return new_pointer, trace


# =========================================================================
# ATOM: MUTATE (The Scribe)
# =========================================================================

def atom_MUTATE(context_data: dict, path: str, value: Any) -> dict:
    """
    Atomic unit to update the data context at a specific path.
    Returns a SHALLOW COPY of the newly updated context.

    Args:
        context_data: The current context dictionary
        path: Dot-notation path (e.g., "user.profile.email")
        value: The value to set at the path

    Returns:
        A new dictionary with the value updated at path.
        The original context_data is NOT modified.

    Note:
        Uses shallow copy for efficiency. For absolute purity with nested
        shared references, deep copy could be used at the cost of performance.
    """
    # Create a shallow copy to ensure the input dictionary is not modified
    new_context = context_data.copy()

    keys = path.split('.')
    current_level = new_context

    # Navigate down to the second-to-last key
    for key in keys[:-1]:
        if key not in current_level or not isinstance(
            current_level[key], dict
        ):
            # If the path doesn't exist, create the intermediate dictionaries
            current_level[key] = {}
        else:
            # Copy the nested dict to avoid mutating the original
            current_level[key] = current_level[key].copy()
        current_level = current_level[key]

    # Set the value at the final key
    final_key = keys[-1]
    current_level[final_key] = value

    return new_context


# =========================================================================
# ATOM: DISPATCH (The Messenger)
# =========================================================================

def atom_DISPATCH(
    system_id: str,
    operation_id: str,
    payload: dict,
    compute_registry: Dict[tuple, ComputeUnitFunc]
) -> dict:
    """
    Atomic unit to pass a payload across the boundary to a compute unit.
    Handles the lookup and standard I/O execution.

    Args:
        system_id: The system namespace (e.g., "pricing", "risk")
        operation_id: The operation name (e.g., "calculate", "assess")
        payload: The input payload dictionary
        compute_registry: Dict mapping (system_id, operation_id) to callables

    Returns:
        The result payload from the compute unit, or an error dict

    Note:
        The Frame must never crash. All compute unit failures are caught
        and returned as standardized error payloads.
    """
    registry_key = (system_id, operation_id)
    compute_func = compute_registry.get(registry_key)

    if not compute_func:
        # Deterministic error handling: return a standard error payload
        print(
            f"[L++ CORE ERROR] No compute unit registered for "
            f"{system_id}:{operation_id}"
        )
        return {"error": "COMPUTE_UNIT_NOT_FOUND", "status": "failed"}

    try:
        # Execute the hermetic unit with standard I/O
        print(
            f"[L++ CORE] Dispatching to {system_id}:{operation_id} "
            f"with payload: {payload}"
        )
        result_payload = compute_func(payload)

        # Enforce the output contract: must be a dictionary
        if not isinstance(result_payload, dict):
            return {"error": "INVALID_COMPUTE_OUTPUT_TYPE", "status": "failed"}

        return result_payload

    except Exception as e:
        # Catch any crashes in the volatile compute layer
        print(f"[L++ CORE ERROR] Compute unit failed: {e}")
        return {"error": str(e), "status": "failed"}


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
]
