"""
L++ Blueprint Schema Definitions

Type-safe structures for Nodes, Edges, Gates, Actions, and the Blueprint.
These are the rigid, immutable definitions loaded from JSON.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Optional


# =========================================================================
# ENUMS
# =========================================================================

class GateType(Enum):
    """Type of gate evaluation."""
    EXPRESSION = "expression"
    COMPUTE = "compute"


class ActionType(Enum):
    """Type of action to execute."""
    SET = "set"
    COMPUTE = "compute"
    EMIT = "emit"
    FORK = "fork"


class JoinStrategy(Enum):
    """Strategy for joining parallel branches."""
    ALL = "all"
    ANY = "any"
    N_OF_M = "n_of_m"


# =========================================================================
# GATE DEFINITIONS
# =========================================================================

@dataclass(frozen=True)
class Gate:
    """
    A gate is a guard condition that must pass for a transition.
    Gates are immutable blueprint definitions.
    """
    id: str
    type: GateType
    expression: Optional[str] = None
    compute_unit: Optional[str] = None
    input_map: dict[str, str] = field(default_factory=dict)
    description: Optional[str] = None

    def __post_init__(self):
        if self.type == GateType.EXPRESSION and not self.expression:
            raise ValueError(f"Gate '{self.id}': expression required")
        if self.type == GateType.COMPUTE and not self.compute_unit:
            raise ValueError(f"Gate '{self.id}': compute_unit required")


# =========================================================================
# ACTION DEFINITIONS
# =========================================================================

@dataclass(frozen=True)
class ForkBranch:
    """A branch in a FORK action."""
    id: str
    actions: tuple[str, ...] = field(default_factory=tuple)


@dataclass(frozen=True)
class Action:
    """
    An action is a side-effect operation executed during a transition.
    Actions are immutable blueprint definitions.
    """
    id: str
    type: ActionType

    # For SET actions
    target: Optional[str] = None
    value: Any = None
    value_from: Optional[str] = None

    # For COMPUTE actions
    compute_unit: Optional[str] = None
    input_map: dict[str, str] = field(default_factory=dict)
    output_map: dict[str, str] = field(default_factory=dict)

    # For EMIT actions
    event: Optional[str] = None
    payload_map: dict[str, str] = field(default_factory=dict)

    # For FORK actions
    branches: tuple[ForkBranch, ...] = field(default_factory=tuple)
    join: JoinStrategy = JoinStrategy.ALL
    join_count: Optional[int] = None
    timeout_ms: Optional[int] = None
    on_timeout: Optional[str] = None

    description: Optional[str] = None


# =========================================================================
# STATE (NODE) DEFINITIONS
# =========================================================================

@dataclass(frozen=True)
class State:
    """
    A state (node) in the state machine.
    States are immutable blueprint definitions.
    """
    id: str
    name: str
    description: Optional[str] = None
    on_enter: tuple[str, ...] = field(default_factory=tuple)
    on_exit: tuple[str, ...] = field(default_factory=tuple)
    metadata: dict[str, Any] = field(default_factory=dict)


# =========================================================================
# TRANSITION (EDGE) DEFINITIONS
# =========================================================================

@dataclass(frozen=True)
class Transition:
    """
    A transition (edge) between states.
    Transitions are immutable blueprint definitions.
    """
    id: str
    from_state: str  # "*" means any state
    to_state: str
    on_event: str
    gates: tuple[str, ...] = field(default_factory=tuple)
    actions: tuple[str, ...] = field(default_factory=tuple)
    description: Optional[str] = None


# =========================================================================
# CONTEXT SCHEMA
# =========================================================================

@dataclass(frozen=True)
class ContextSchema:
    """Schema definition for the context object."""
    schema: dict[str, Any] = field(default_factory=dict)
    defaults: dict[str, Any] = field(default_factory=dict)


# =========================================================================
# BLUEPRINT (THE COMPLETE DEFINITION)
# =========================================================================

@dataclass(frozen=True)
class Blueprint:
    """
    The complete L++ Blueprint definition.
    This is the immutable, validated representation of a workflow.
    """
    schema_version: str
    id: str
    name: str
    version: str
    description: Optional[str]

    # The graph
    states: dict[str, State]
    transitions: tuple[Transition, ...]
    entry_state: str
    terminal_states: frozenset[str]

    # Definitions
    gates: dict[str, Gate]
    actions: dict[str, Action]

    # Context
    context_schema: ContextSchema

    def get_state(self, state_id: str) -> State:
        """Get a state by ID."""
        if state_id not in self.states:
            raise KeyError(f"State '{state_id}' not found")
        return self.states[state_id]

    def get_gate(self, gate_id: str) -> Gate:
        """Get a gate by ID."""
        if gate_id not in self.gates:
            raise KeyError(f"Gate '{gate_id}' not found")
        return self.gates[gate_id]

    def get_action(self, action_id: str) -> Action:
        """Get an action by ID."""
        if action_id not in self.actions:
            raise KeyError(f"Action '{action_id}' not found")
        return self.actions[action_id]

    def get_transitions_from(self, state_id: str) -> list[Transition]:
        """Get all transitions from a given state."""
        result = []
        for t in self.transitions:
            if t.from_state == state_id or t.from_state == "*":
                result.append(t)
        return result

    def is_terminal(self, state_id: str) -> bool:
        """Check if a state is terminal."""
        return state_id in self.terminal_states


__all__ = [
    # Enums
    'GateType',
    'ActionType',
    'JoinStrategy',
    # Definitions
    'Gate',
    'Action',
    'ForkBranch',
    'State',
    'Transition',
    'ContextSchema',
    'Blueprint',
]
