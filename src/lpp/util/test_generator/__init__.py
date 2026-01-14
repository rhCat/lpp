"""
L++ Test Generator Utility

Auto-generates test cases from L++ blueprints for comprehensive testing
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
    """Run the test_generator utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Initialize context
    context = {
        "blueprint_path": params.get("blueprint_path"),
        "output_format": params.get("output_format", "pytest"),
        "blueprint": None,  # Will be loaded by LOAD transition
        "error": None,
    }
    context.update(params)
    state = blueprint.entry_state

    # Run LOAD (with path in payload) then ANALYZE, GENERATE_ALL
    bp_path = params.get("blueprint_path")

    # LOAD event needs path in payload
    state, context, traces, err = run_frame(
        blueprint, context, "LOAD", {"path": bp_path}, COMPUTE_REGISTRY
    )
    if err:
        return {"error": err, "state": state}

    # Run remaining events
    for event in ["ANALYZE", "GENERATE", "AUTO"]:
        if state in blueprint.terminal_states:
            break
        state, context, traces, err = run_frame(
            blueprint, context, event, {}, COMPUTE_REGISTRY
        )
        if err:
            return {"error": err, "state": state}

    return {"state": state, "context": context}

__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
