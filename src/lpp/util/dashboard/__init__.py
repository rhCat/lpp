"""
L++ Dashboard Utility

Aggregates and visualizes all L++ utility tools with interactive search, filtering, and quick access to visualizations.
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
    """Run the dashboard utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Initialize context with required variables
    context = {
        "utilsPath": params.get("utilsPath", "src/lpp/util"),
        "tools": None,
        "categories": None,
        "statistics": None,
        "error": None,
    }
    context.update(params)
    state = blueprint.entry_state

    # Run events: SCAN then AUTO transitions to complete
    events = ['SCAN'] + ['AUTO'] * 10
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
