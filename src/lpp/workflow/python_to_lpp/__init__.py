"""
L++ Python To Lpp Workflow

Refactors a Python repository into an L++ based project with full documentation
"""
from pathlib import Path

# Assembly/Blueprint location
ASSEMBLY_PATH = Path(__file__).parent / "assembly.json"
BLUEPRINT_PATH = Path(__file__).parent / "blueprint.json"
COMPONENTS_DIR = Path(__file__).parent / "components"

# Re-export compute registry
try:
    from .compute import COMPUTE_REGISTRY
except ImportError:
    COMPUTE_REGISTRY = {}


def run(project_path: str = None, output_path: str = None, **options) -> dict:
    """
    Run the python_to_lpp workflow.

    Args:
        project_path: Input path (workflow-specific)
        output_path: Output directory
        **options: Additional workflow options

    Returns:
        dict with workflow results
    """
    from lpp.core import load_blueprint, run_frame
    import json

    # Prefer assembly if exists, else blueprint
    bp_path = ASSEMBLY_PATH if ASSEMBLY_PATH.exists() else BLUEPRINT_PATH
    
    with open(bp_path) as f:
        bp_raw = json.load(f)
    
    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}
    
    # Initialize context
    context = {
        "projectPath": project_path,
        "outputPath": output_path or "./output",
        **options
    }
    
    # Start workflow - find event that progresses from entry state
    entry = bp_raw.get("entry_state", "idle")
    entry_events = []
    for t in bp_raw.get("transitions", []):
        if t.get("from") == entry and t.get("to") != entry:
            entry_events.append(t.get("on_event"))
    event = entry_events[0] if entry_events else "REFACTOR"

    new_state, new_ctx, traces, err = run_frame(
        blueprint, context, event, {}, COMPUTE_REGISTRY
    )
    
    if err:
        return {"error": err, "state": new_state}
    
    return {"state": new_state, "context": new_ctx}


__all__ = ["ASSEMBLY_PATH", "BLUEPRINT_PATH", "COMPONENTS_DIR", "COMPUTE_REGISTRY", "run"]
