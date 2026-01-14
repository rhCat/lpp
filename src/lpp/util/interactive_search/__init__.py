"""
L++ Interactive Search

A refined interactive search tool with iterative refinement capabilities.

Usage:
    from lpp.util.interactive_search import InteractiveSearch

    search = InteractiveSearch("/path/to/search")
    search.run("initial query")

CLI:
    lpp-search [path] [query]
    lpp-search --help
"""
from pathlib import Path

from .compute import COMPUTE_REGISTRY
from .cli import InteractiveSearch, main

# Blueprint location
BLUEPRINT_PATH = Path(__file__).parent / "blueprint.json"


def run(params: dict) -> dict:
    """Run the interactive_search utility with given parameters."""
    from lpp.core import load_blueprint, run_frame
    import json

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, error = load_blueprint(bp_raw)
    if error:
        return {"error": error}

    # Initialize context
    context = {
        "query": params.get("query"),
        "search_path": params.get("search_path", "."),
        "results": None,
        "error": None,
    }
    context.update(params)
    state = blueprint.entry_state

    # Dispatch SEARCH event
    state, context, traces, err = run_frame(
        blueprint, context, "SEARCH", {}, COMPUTE_REGISTRY
    )

    if err:
        return {"error": err, "state": state}

    return {"state": state, "context": context}


__all__ = [
    "BLUEPRINT_PATH",
    "COMPUTE_REGISTRY",
    "InteractiveSearch",
    "main",
    "run",
]
