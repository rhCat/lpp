"""
L++ Blueprint Loader

Parser and validator that ingests raw JSON, validates it against
logic rules, and hydrates the schema objects.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Union

from .schema import (
    Blueprint,
    State,
    Transition,
    Gate,
    GateType,
    Action,
    ActionType,
    ForkBranch,
    JoinStrategy,
    ContextSchema,
)


class BlueprintValidationError(Exception):
    """Error during blueprint validation."""

    def __init__(self, message: str, path: str = ""):
        self.path = path
        full_msg = f"[{path}] {message}" if path else message
        super().__init__(full_msg)


class BlueprintLoader:
    """
    Loads and validates L++ blueprints from JSON.
    """

    REQUIRED_FIELDS = [
        "$schema", "id", "name", "version",
        "states", "transitions", "entry_state", "terminal_states"
    ]

    def __init__(self, raw: dict[str, Any]):
        """
        Initialize loader with raw JSON dict.

        Args:
            raw: The raw JSON dictionary
        """
        self.raw = raw
        self._errors: list[str] = []

    def load(self) -> Blueprint:
        """
        Load and validate the blueprint.

        Returns:
            Validated Blueprint object

        Raises:
            BlueprintValidationError: If validation fails
        """
        self._validate_required_fields()
        self._validate_references()

        return Blueprint(
            schema_version=self.raw["$schema"],
            id=self.raw["id"],
            name=self.raw["name"],
            version=self.raw["version"],
            description=self.raw.get("description"),
            states=self._load_states(),
            transitions=self._load_transitions(),
            entry_state=self.raw["entry_state"],
            terminal_states=frozenset(self.raw["terminal_states"]),
            gates=self._load_gates(),
            actions=self._load_actions(),
            context_schema=self._load_context_schema(),
        )

    def _validate_required_fields(self) -> None:
        """Validate all required fields are present."""
        for field in self.REQUIRED_FIELDS:
            if field not in self.raw:
                raise BlueprintValidationError(
                    f"Missing required field: {field}",
                    path="root"
                )

    def _validate_references(self) -> None:
        """Validate all internal references are valid."""
        states = set(self.raw.get("states", {}).keys())
        gates = set(self.raw.get("gates", {}).keys())
        actions = set(self.raw.get("actions", {}).keys())

        # Validate entry_state
        entry = self.raw["entry_state"]
        if entry not in states:
            raise BlueprintValidationError(
                f"Entry state '{entry}' not defined",
                path="entry_state"
            )

        # Validate terminal_states
        for ts in self.raw["terminal_states"]:
            if ts not in states:
                raise BlueprintValidationError(
                    f"Terminal state '{ts}' not defined",
                    path="terminal_states"
                )

        # Validate transitions
        for i, trans in enumerate(self.raw.get("transitions", [])):
            path = f"transitions[{i}]"

            # from_state
            from_s = trans.get("from", "")
            if from_s != "*" and from_s not in states:
                raise BlueprintValidationError(
                    f"Unknown from_state: '{from_s}'",
                    path=path
                )

            # to_state
            to_s = trans.get("to", "")
            if to_s not in states:
                raise BlueprintValidationError(
                    f"Unknown to_state: '{to_s}'",
                    path=path
                )

            # gates
            for gate_id in trans.get("gates", []):
                if gate_id not in gates:
                    raise BlueprintValidationError(
                        f"Unknown gate: '{gate_id}'",
                        path=path
                    )

            # actions
            for action_id in trans.get("actions", []):
                if action_id not in actions:
                    raise BlueprintValidationError(
                        f"Unknown action: '{action_id}'",
                        path=path
                    )

        # Validate state on_enter/on_exit actions
        for state_id, state in self.raw.get("states", {}).items():
            path = f"states.{state_id}"
            for action_id in state.get("on_enter", []):
                if action_id not in actions:
                    raise BlueprintValidationError(
                        f"Unknown on_enter action: '{action_id}'",
                        path=path
                    )
            for action_id in state.get("on_exit", []):
                if action_id not in actions:
                    raise BlueprintValidationError(
                        f"Unknown on_exit action: '{action_id}'",
                        path=path
                    )

    def _load_states(self) -> dict[str, State]:
        """Load state definitions."""
        states = {}
        for state_id, raw_state in self.raw.get("states", {}).items():
            states[state_id] = State(
                id=state_id,
                name=raw_state.get("name", state_id),
                description=raw_state.get("description"),
                on_enter=tuple(raw_state.get("on_enter", [])),
                on_exit=tuple(raw_state.get("on_exit", [])),
                metadata=raw_state.get("metadata", {}),
            )
        return states

    def _load_transitions(self) -> tuple[Transition, ...]:
        """Load transition definitions."""
        transitions = []
        for i, raw_trans in enumerate(self.raw.get("transitions", [])):
            trans_id = raw_trans.get("id", f"transition_{i}")
            transitions.append(Transition(
                id=trans_id,
                from_state=raw_trans["from"],
                to_state=raw_trans["to"],
                on_event=raw_trans["on_event"],
                gates=tuple(raw_trans.get("gates", [])),
                actions=tuple(raw_trans.get("actions", [])),
                description=raw_trans.get("description"),
            ))
        return tuple(transitions)

    def _load_gates(self) -> dict[str, Gate]:
        """Load gate definitions."""
        gates = {}
        for gate_id, raw_gate in self.raw.get("gates", {}).items():
            gate_type = GateType(raw_gate.get("type", "expression"))
            gates[gate_id] = Gate(
                id=gate_id,
                type=gate_type,
                expression=raw_gate.get("expression"),
                compute_unit=raw_gate.get("compute_unit"),
                input_map=raw_gate.get("input_map", {}),
                description=raw_gate.get("description"),
            )
        return gates

    def _load_actions(self) -> dict[str, Action]:
        """Load action definitions."""
        actions = {}
        for action_id, raw_action in self.raw.get("actions", {}).items():
            action_type = ActionType(raw_action.get("type", "set"))

            # Parse branches for FORK actions
            branches = tuple()
            if action_type == ActionType.FORK:
                branches = tuple(
                    ForkBranch(
                        id=b.get("id", f"branch_{i}"),
                        actions=tuple(b.get("actions", []))
                    )
                    for i, b in enumerate(raw_action.get("branches", []))
                )

            # Parse join strategy
            join_str = raw_action.get("join", "all")
            join = JoinStrategy(join_str)

            actions[action_id] = Action(
                id=action_id,
                type=action_type,
                # SET
                target=raw_action.get("target"),
                value=raw_action.get("value"),
                value_from=raw_action.get("value_from"),
                # COMPUTE
                compute_unit=raw_action.get("compute_unit"),
                input_map=raw_action.get("input_map", {}),
                output_map=raw_action.get("output_map", {}),
                # EMIT
                event=raw_action.get("event"),
                payload_map=raw_action.get("payload_map", {}),
                # FORK
                branches=branches,
                join=join,
                join_count=raw_action.get("join_count"),
                timeout_ms=raw_action.get("timeout_ms"),
                on_timeout=raw_action.get("on_timeout"),
                # Meta
                description=raw_action.get("description"),
            )
        return actions

    def _load_context_schema(self) -> ContextSchema:
        """Load context schema definition."""
        ctx = self.raw.get("context", {})
        return ContextSchema(
            schema=ctx.get("$schema", {}),
            defaults=ctx.get("$defaults", {}),
        )


# =========================================================================
# PUBLIC API
# =========================================================================

def load_blueprint(source: Union[str, Path, dict]) -> Blueprint:
    """
    Load a blueprint from various sources.

    Args:
        source: JSON file path, Path object, or raw dict

    Returns:
        Validated Blueprint object

    Raises:
        BlueprintValidationError: If validation fails
        FileNotFoundError: If file doesn't exist
        json.JSONDecodeError: If JSON is invalid
    """
    if isinstance(source, dict):
        raw = source
    elif isinstance(source, (str, Path)):
        path = Path(source)
        with open(path, 'r') as f:
            raw = json.load(f)
    else:
        raise TypeError(f"Invalid source type: {type(source)}")

    loader = BlueprintLoader(raw)
    return loader.load()


def load_blueprint_from_json(json_str: str) -> Blueprint:
    """
    Load a blueprint from a JSON string.

    Args:
        json_str: JSON string

    Returns:
        Validated Blueprint object
    """
    raw = json.loads(json_str)
    return load_blueprint(raw)


__all__ = [
    'BlueprintLoader',
    'BlueprintValidationError',
    'load_blueprint',
    'load_blueprint_from_json',
]
