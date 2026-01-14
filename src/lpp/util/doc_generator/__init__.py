"""
L++ Doc Generator Utility

Generates documentation artifacts for L++ blueprints.
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
    """Run the doc_generator utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Initialize context with defaults for required variables
    context = {
        "blueprints": [],
        "options": params.get("options", {"all": True}),
        "utilsPath": params.get("utilsPath", "."),
        "outputPath": params.get("outputPath", "./results"),
        "results": {"generated": 0, "errors": []},
        "error": None,
    }
    context.update(params)
    state = blueprint.entry_state

    # Run through state machine until terminal or error
    events = ["START", "GENERATE"] + ["DONE"] * 10  # Max iterations
    for event in events:
        state, context, traces, err = run_frame(
            blueprint, context, event, {}, COMPUTE_REGISTRY
        )
        if err:
            return {"error": err, "state": state}
        if state in blueprint.terminal_states:
            break

    return {"state": state, "context": context}


__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
