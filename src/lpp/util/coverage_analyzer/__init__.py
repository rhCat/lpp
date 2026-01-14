"""
L++ Coverage Analyzer Utility

Tracks runtime coverage of blueprints during execution
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
    """Run the coverage_analyzer utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Initialize context with required variables
    context = {
        "blueprint_path": params.get("blueprint_path"),
        "blueprint": None,
        "trace_log": params.get("trace_log"),
        "trace_data": None,
        "coverage_data": None,
        "metrics": None,
        "summary_report": None,
        "detailed_report": None,
        "gap_report": None,
        "html_report": None,
        "json_report": None,
        "error": None,
    }
    context.update(params)
    state = blueprint.entry_state

    # Get blueprint path from params
    bp_path = params.get("blueprint_path")

    # LOAD expects path in event payload
    state, context, traces, err = run_frame(
        blueprint, context, "LOAD", {"path": bp_path}, COMPUTE_REGISTRY
    )
    if err:
        return {"error": err, "state": state}

    return {"state": state, "context": context}

__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
