"""
L++ Frame - Python Package

The Universal Deterministic Logic Workflow Machine.

Structure:
    lpp_core.py    - The Four Atomic Operations (Assembly Language)
    schema.py      - Blueprint Definitions (Immutable)
    loader.py      - JSON Parser & Validator
    compiler.py    - JSON to Python Compiler
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
    ContextSchema,
)

from .loader import (
    load_blueprint,
    load_blueprint_from_json,
    BlueprintLoader,
    BlueprintValidationError,
)

# ==========================================================================
# COMPILER
# ==========================================================================

from .compiler import compile_blueprint, compile_blueprint_dict

# ==========================================================================
# ORCHESTRATOR
# ==========================================================================

from .orchestrator import run_frame

# ==========================================================================
# OPERATIONAL VALIDATOR
# ==========================================================================

from .operational_validator import (
    validate_python_file,
    validate_skill_directory,
    validate_skill,
    sanitize_python_code,
    OperationalValidationError,
)

# ==========================================================================
# ASSEMBLY VALIDATOR
# ==========================================================================

from .assembly_validator import (
    loadAssembly,
    validateAssembly,
    validateTerminals,
    validateInterfaces,
    generateAssemblyTla,
    AssemblyValidationError,
    ComponentLoadError,
    InterfaceCompatibilityError,
)


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
    'ContextSchema',

    # Loader
    'load_blueprint',
    'load_blueprint_from_json',
    'BlueprintLoader',
    'BlueprintValidationError',

    # Compiler
    'compile_blueprint',
    'compile_blueprint_dict',

    # Orchestrator
    'run_frame',

    # Operational Validator
    'validate_python_file',
    'validate_skill_directory',
    'validate_skill',
    'sanitize_python_code',
    'OperationalValidationError',

    # Assembly Validator
    'loadAssembly',
    'validateAssembly',
    'validateTerminals',
    'validateInterfaces',
    'generateAssemblyTla',
    'AssemblyValidationError',
    'ComponentLoadError',
    'InterfaceCompatibilityError',
]
