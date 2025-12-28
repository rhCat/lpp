"""
L++ Frame - Python Package

The Universal Deterministic Logic Workflow Machine.

Structure:
    lpp_core.py    - The Four Atomic Operations (Assembly Language)
    schema.py      - Blueprint Definitions (Immutable)
    loader.py      - JSON Parser & Validator
    orchestrator.py - The Thin Conductor
"""

# ==========================================================================
# ATOMIC CORE (The Four Atoms)
# ==========================================================================

from .lpp_core import (
    atom_EVALUATE,
    atom_TRANSITION,
    atom_MUTATE,
    atom_DISPATCH,
    ComputeUnitFunc,
    TransitionTrace,
)

# ==========================================================================
# BLUEPRINT INFRASTRUCTURE
# ==========================================================================

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

from .loader import (
    load_blueprint,
    load_blueprint_from_json,
    BlueprintLoader,
    BlueprintValidationError,
)

# ==========================================================================
# ORCHESTRATOR
# ==========================================================================

from .orchestrator import run_frame


__version__ = "0.1.0"

__all__ = [
    # Atomic Core
    'atom_EVALUATE',
    'atom_TRANSITION',
    'atom_MUTATE',
    'atom_DISPATCH',
    'ComputeUnitFunc',
    'TransitionTrace',

    # Schema
    'Blueprint',
    'State',
    'Transition',
    'Gate',
    'GateType',
    'Action',
    'ActionType',
    'ForkBranch',
    'JoinStrategy',
    'ContextSchema',

    # Loader
    'load_blueprint',
    'load_blueprint_from_json',
    'BlueprintLoader',
    'BlueprintValidationError',

    # Orchestrator
    'run_frame',
]
