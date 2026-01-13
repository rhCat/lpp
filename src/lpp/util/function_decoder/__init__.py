"""
L++ Function Decoder Utility

Analyze Python scripts to extract inbound/outbound function interfaces and build modular dependency graphs
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
    """Run the function_decoder utility with given parameters."""
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
