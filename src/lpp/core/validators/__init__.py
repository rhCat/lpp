"""
L++ Core Validators

Validation modules for blueprints, assemblies, operations, and TLA+ specs.

Modules:
    blueprint   - Schema validation for blueprint JSON
    operational - Runtime validation of generated Python code
    assembly    - Assembly blueprint validation and interface checking
    tla         - TLA+ specification generation and model checking
"""

from .blueprint import (
    validate_blueprint,
    BlueprintValidationError,
)

from .operational import (
    validate_python_file,
    validate_skill_directory,
    validate_skill,
    sanitize_python_code,
    OperationalValidationError,
)

from .assembly import (
    loadAssembly,
    validateAssembly,
    validateTerminals,
    validateInterfaces,
    generateAssemblyTla,
    AssemblyValidationError,
    ComponentLoadError,
    InterfaceCompatibilityError,
)

from .tla import (
    generate_tla,
    validate_with_tlc,
    save_tla,
    TLAValidationError,
)

# Alias for backward compatibility
validate_tla = validate_with_tlc

__all__ = [
    # Blueprint validation
    "validate_blueprint",
    "BlueprintValidationError",
    # Operational validation
    "validate_python_file",
    "validate_skill_directory",
    "validate_skill",
    "sanitize_python_code",
    "OperationalValidationError",
    # Assembly validation
    "loadAssembly",
    "validateAssembly",
    "validateTerminals",
    "validateInterfaces",
    "generateAssemblyTla",
    "AssemblyValidationError",
    "ComponentLoadError",
    "InterfaceCompatibilityError",
    # TLA+ validation
    "generate_tla",
    "validate_tla",
    "validate_with_tlc",
    "save_tla",
    "TLAValidationError",
]
