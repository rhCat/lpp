"""
L++ Compliance Checker Utility

Verifies L++ blueprints against compliance policies
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
    """Run the compliance_checker utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Initialize context with required variables
    context = {
        "blueprint": None,
        "blueprint_path": None,
        "blueprint_name": None,
        "policies": None,
        "findings": None,
        "summary": None,
        "report": None,
        "score": None,
        "error": None,
    }
    context.update(params)
    state = blueprint.entry_state

    # Get blueprint path from params
    bp_path = params.get("blueprint_path")

    # LOAD_BLUEPRINT expects path in event payload
    state, context, traces, err = run_frame(
        blueprint, context, "LOAD_BLUEPRINT", {"path": bp_path}, COMPUTE_REGISTRY
    )

    if err:
        return {"error": err, "state": state}

    return {"state": state, "context": context}

__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
