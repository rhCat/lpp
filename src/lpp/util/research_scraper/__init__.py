"""
L++ Research Scraper Utility

Scrape academic papers from arXiv, Semantic Scholar, and web
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
    """Run the research_scraper utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json
    
    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)
    
    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}
    
    # Initialize context from params
    context = params.copy()
    
    # Dispatch search event based on source parameter
    source = params.get("source", "arxiv").lower()
    event_map = {
        "arxiv": "SEARCH_ARXIV",
        "scholar": "SEARCH_SCHOLAR",
        "web": "SEARCH_WEB",
    }
    event = event_map.get(source, "SEARCH_ARXIV")

    new_state, new_ctx, traces, err = run_frame(
        blueprint, context, event, {}, COMPUTE_REGISTRY
    )
    
    if err:
        return {"error": err, "state": new_state}
    
    return {"state": new_state, "context": new_ctx}

__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
