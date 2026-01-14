"""
L++ Legacy Extractor Utility

Extract state machine patterns from legacy Python code and convert to L++ blueprints
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
    """Run the legacy_extractor utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Support both filePath and file_path params
    file_path = params.get("filePath") or params.get("file_path")

    # Initialize context with required variables
    context = {
        "filePath": file_path,
        "sourceCode": None,
        "ast": None,
        "patterns": None,
        "extractedStates": None,
        "mode": params.get("mode", "auto"),
        "error": None,
    }
    context.update(params)
    context["filePath"] = file_path  # Ensure it's set after update
    state = blueprint.entry_state

    # Dispatch EXTRACT event
    state, context, traces, err = run_frame(
        blueprint, context, "EXTRACT", {}, COMPUTE_REGISTRY
    )

    if err:
        return {"error": err, "state": state}

    return {"state": state, "context": context}

__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
