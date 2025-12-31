"""
L++ Blueprint Validator

Validates JSON blueprints against the L++ schema requirements.
Ensures blueprints have all required fields for audit trails and determinism.
"""

from typing import List


class BlueprintValidationError(Exception):
    """Raised when blueprint fails schema validation."""
    pass


def validate_blueprint(bp: dict) -> None:
    """
    Validate blueprint against schema requirements.
    Raises BlueprintValidationError on failure.

    Required fields:
        - Root: $schema, id, name, version,
            entry_state, states, transitions, actions, terminal_states
        - transitions[]: id, on_event, from, to
        - gates[]: type (expression | compute)
    """
    errors: List[str] = []

    # Required root fields
    for field in [
        "$schema",
        "id",
        "name",
        "version",
        "entry_state",
        "states",
        "transitions",
        "actions"
    ]:
        if field not in bp:
            errors.append(f"Missing required root field: {field}")

    # terminal_states must be present (can be empty array)
    if "terminal_states" not in bp:
        errors.append(
            "Missing required root field: terminal_states (can be empty [])")

    # Validate transitions - id is required
    for i, trans in enumerate(bp.get("transitions", [])):
        if not trans.get("id"):
            errors.append(f"transitions[{i}]: Missing required field 'id'")
        if not trans.get("on_event"):
            errors.append(
                f"transitions[{i}]: Missing required field 'on_event'")
        if "from" not in trans:
            errors.append(f"transitions[{i}]: Missing required field 'from'")
        if "to" not in trans:
            errors.append(f"transitions[{i}]: Missing required field 'to'")

    # Validate gates - type is required
    for gate_id, gate in bp.get("gates", {}).items():
        if not gate.get("type"):
            errors.append(
                f"gates[{gate_id}]: Missing required "
                "field 'type' (must be 'expression' or 'compute')")
        elif gate["type"] not in ("expression", "compute"):
            errors.append(
                f"gates[{gate_id}]: Invalid type '{gate['type']}' "
                "(must be 'expression' or 'compute')")

        if gate.get("type") == "expression" and not gate.get("expression"):
            errors.append(
                f"gates[{gate_id}]: "
                "type='expression' requires 'expression' field")
        if gate.get("type") == "compute" and not gate.get("compute_unit"):
            errors.append(
                f"gates[{gate_id}]: "
                "type='compute' requires 'compute_unit' field")

    if errors:
        raise BlueprintValidationError("\n".join(errors))
