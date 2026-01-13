"""
DEPRECATED: frame_py is deprecated and will be removed in v2.0.0

Migration guide:
    # Old imports (deprecated)
    from frame_py.loader import BlueprintLoader
    from frame_py.compiler import compile_blueprint
    from frame_py import run_frame

    # New imports (recommended)
    from lpp.core import BlueprintLoader
    from lpp.core import compile_blueprint
    from lpp.core import run_frame

See migration guide at docs/migration/v1_to_v2.md
"""

import warnings as _warnings

_warnings.warn(
    "frame_py is deprecated. Use 'lpp.core' instead. "
    "See migration guide at docs/migration/v1_to_v2.md",
    DeprecationWarning,
    stacklevel=2
)

# Re-export everything from lpp.core for backward compatibility
from lpp.core import (
    # Atomic Core
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
    # Schema
    Blueprint,
    State,
    Transition,
    Gate,
    GateType,
    Action,
    ActionType,
    ContextSchema,
    # Loader
    load_blueprint,
    load_blueprint_from_json,
    BlueprintLoader,
    BlueprintValidationError,
    # Compiler
    compile_blueprint,
    compile_blueprint_dict,
    # Orchestrator
    run_frame,
    # Safe Eval
    safe_eval_bool,
    SafeEvalError,
    # Validators
    validate_blueprint,
    validate_python_file,
    validate_skill_directory,
    validate_skill,
    sanitize_python_code,
    OperationalValidationError,
    loadAssembly,
    validateAssembly,
    validateTerminals,
    validateInterfaces,
    generateAssemblyTla,
    AssemblyValidationError,
    ComponentLoadError,
    InterfaceCompatibilityError,
    generate_tla,
    validate_tla,
    save_tla,
    TLAValidationError,
)

__version__ = "0.1.0"  # Legacy version

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
