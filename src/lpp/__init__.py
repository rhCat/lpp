"""
L++ Dev Suite - The Universal Deterministic Logic Workflow Machine

A complete development suite for building deterministic, verifiable workflows.

Packages:
    lpp.core     - Core runtime (atoms, loader, compiler, validators)
    lpp.util     - 31 utility tools (test generator, linter, decoder, etc.)
    lpp.workflow - Workflow definitions (py2lpp, lvp, canvas)

Quick Start:
    from lpp.core import BlueprintLoader, compile_blueprint, run_frame
    from lpp.util.logic_decoder import run as decode
    from lpp.workflow.python_to_lpp import run as refactor

CLI Tools:
    lpp compile <blueprint.json>
    lpp util <tool_name> [args]
    lpp workflow <workflow_name> [args]
"""

__version__ = "1.2.5"

# Convenience re-exports from lpp.core
from lpp.core import (
    # Atomic operations
    atom_EVALUATE,
    atom_TRANSITION,
    atom_MUTATE,
    atom_DISPATCH,
    # Schema
    Blueprint,
    State,
    Transition,
    Gate,
    Action,
    # Loader
    load_blueprint,
    BlueprintLoader,
    # Compiler
    compile_blueprint,
    # Orchestrator
    run_frame,
)

__all__ = [
    "__version__",
    # Atoms
    "atom_EVALUATE",
    "atom_TRANSITION",
    "atom_MUTATE",
    "atom_DISPATCH",
    # Schema
    "Blueprint",
    "State",
    "Transition",
    "Gate",
    "Action",
    # Loader
    "load_blueprint",
    "BlueprintLoader",
    # Compiler
    "compile_blueprint",
    # Orchestrator
    "run_frame",
]
