"""
L++ Skill Contractor Utility

Autonomous L++ skill generator. Continuously iterates on logic to achieve coding targets with self-evaluation. Two-phase workflow: (1) Blueprint phase generates and validates JSON until TLC passes, (2) Implementation phase generates compute+interactive with auto-sanitization (fixes literal newlines in strings) and enhanced validation (content checks, AST parsing, import validation, structure checks). Features auto-correction of schema issues with logging. Enforces L++ schema v0.1.2 and build_rules.md for skill creation.
"""
from pathlib import Path

# Blueprint location
BLUEPRINT_PATH = Path(__file__).parent / "blueprint.json"

# Re-export compute registry
try:
    from .compute import COMPUTE_REGISTRY
except ImportError:
    COMPUTE_REGISTRY = {}

def run(params: dict) -> dict:
    """Run the skill_contractor utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json
    
    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)
    
    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}
    
    # Initialize context from params
    context = params.copy()
    
    # Dispatch START event
    new_state, new_ctx, traces, err = run_frame(
        blueprint, context, "START", {}, COMPUTE_REGISTRY
    )
    
    if err:
        return {"error": err, "state": new_state}
    
    return {"state": new_state, "context": new_ctx}

__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
