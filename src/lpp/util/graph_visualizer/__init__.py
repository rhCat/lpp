"""
L++ Graph Visualizer Utility

Generates an interactive HTML/SVG state machine diagram.
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
    """Run the graph_visualizer utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Initialize context with defaults
    context = {
        "blueprint": params.get("blueprint"),
        "html_path": params.get("html_path"),
        "has_blueprint": params.get("blueprint") is not None,
        "has_html": False,
        "error": None,
    }
    context.update(params)
    state = blueprint.entry_state

    # Run through state machine
    events = ["START", "GENERATE"] + ["DONE"] * 3
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
