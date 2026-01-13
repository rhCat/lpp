"""
L++ Core Runtime

The Universal Deterministic Logic Workflow Machine core runtime.

Structure:
    atoms.py       - The Four Atomic Operations (Assembly Language)
    schema.py      - Blueprint Definitions (Immutable Dataclasses)
    loader.py      - JSON Parser & Validator
    compiler.py    - JSON to Python Compiler
    orchestrator.py - The Thin Conductor
    safe_eval.py   - Sandboxed Expression Evaluation
    visualizer.py  - Diagram Generation
    validators/    - Validation subpackage

Quick Start:
    from lpp.core import BlueprintLoader, compile_blueprint, run_frame

    # Load a blueprint
    loader = BlueprintLoader(raw_json)
    blueprint, error = loader.load()

    # Compile to Python
    code, error = compile_blueprint("blueprint.json", "output.py")

    # Execute events
    new_state, new_ctx, traces, error = run_frame(
        blueprint, context, "EVENT", payload, compute_registry
    )
"""

# ==========================================================================
# ATOMIC CORE (The Four Atoms)
# ==========================================================================

from .atoms import (
    atom_EVALUATE,
    atom_TRANSITION,
    atom_MUTATE,
    atom_DISPATCH,
    ComputeUnitFunc,
    TransitionTrace,
    AtomError,
    EvaluateError,
    TransitionError,
    MutateError,
    DispatchError,
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
# SAFE EVALUATION
# ==========================================================================

from .safe_eval import safe_eval_bool, SafeEvalError

# ==========================================================================
# VISUALIZATION
# ==========================================================================

from .visualizer import LppVisualizer

# ==========================================================================
# VALIDATORS (also available via lpp.core.validators)
# ==========================================================================

from .validators import (
    # Blueprint validation
    validate_blueprint,
    BlueprintValidationError,
    # Operational validation
    validate_python_file,
    validate_skill_directory,
    validate_skill,
    sanitize_python_code,
    OperationalValidationError,
    # Assembly validation
    loadAssembly,
    validateAssembly,
    validateTerminals,
    validateInterfaces,
    generateAssemblyTla,
    AssemblyValidationError,
    ComponentLoadError,
    InterfaceCompatibilityError,
    # TLA+ validation
    generate_tla,
    validate_tla,
    save_tla,
    TLAValidationError,
)

__all__ = [
    # Atomic Core
    "atom_EVALUATE",
    "atom_TRANSITION",
    "atom_MUTATE",
    "atom_DISPATCH",
    "ComputeUnitFunc",
    "TransitionTrace",
    "AtomError",
    "EvaluateError",
    "TransitionError",
    "MutateError",
    "DispatchError",
    # Schema
    "Blueprint",
    "State",
    "Transition",
    "Gate",
    "GateType",
    "Action",
    "ActionType",
    "ContextSchema",
    # Loader
    "load_blueprint",
    "load_blueprint_from_json",
    "BlueprintLoader",
    "BlueprintValidationError",
    # Compiler
    "compile_blueprint",
    "compile_blueprint_dict",
    # Orchestrator
    "run_frame",
    # Safe Eval
    "safe_eval_bool",
    "SafeEvalError",
    # Visualizer
    "LppVisualizer",
    # Validators
    "validate_blueprint",
    "validate_python_file",
    "validate_skill_directory",
    "validate_skill",
    "sanitize_python_code",
    "OperationalValidationError",
    "loadAssembly",
    "validateAssembly",
    "validateTerminals",
    "validateInterfaces",
    "generateAssemblyTla",
    "AssemblyValidationError",
    "ComponentLoadError",
    "InterfaceCompatibilityError",
    "generate_tla",
    "validate_tla",
    "save_tla",
    "TLAValidationError",
]
