"""
L++ Policy Generator

Generate L++ policies from source repositories or decoded blueprints
with full provenance tracking.

Usage:
    from lpp.util.policy_generator import run, COMPUTE_REGISTRY

    # Generate policy from source repo
    result = run({
        "source_path": "/path/to/repo",
        "policy_name": "my_policy",
        "source_repo": "https://github.com/user/repo"
    })

CLI:
    lpp util policy_generator /path/to/repo --name my_policy --repo https://github.com/user/repo
"""

from pathlib import Path

# Blueprint location
BLUEPRINT_PATH = Path(__file__).parent.parent.parent.parent.parent / "utils" / "policy_generator" / "policy_generator.json"

# Re-export compute registry
try:
    import sys
    compute_path = Path(__file__).parent.parent.parent.parent.parent / "utils" / "policy_generator" / "src"
    sys.path.insert(0, str(compute_path))
    from policy_generator_compute import COMPUTE_REGISTRY
except ImportError:
    COMPUTE_REGISTRY = {}


def run(params: dict) -> dict:
    """
    Run the policy generator.

    Args:
        params: Dict with:
            - source_path: Path to source repo or decoded JSON
            - policy_name: Name for generated policy
            - source_repo: Git URL for provenance (optional)
            - output_path: Output directory (optional)

    Returns:
        dict with state and context
    """
    import json
    from lpp.core import load_blueprint, run_frame

    with open(BLUEPRINT_PATH) as f:
        bp_raw = json.load(f)

    blueprint, err = load_blueprint(bp_raw)
    if err:
        return {"error": err}

    # Initialize context
    context = {
        "source_path": params.get("source_path"),
        "policy_name": params.get("policy_name", "generated_policy"),
        "source_repo": params.get("source_repo"),
        "output_path": params.get("output_path"),
    }

    # Run through all states
    events = [
        "GENERATE", "ANALYZED", "STATES_EXTRACTED", "SLOTS_EXTRACTED",
        "TERMINALS_EXTRACTED", "COMPOSED", "TLA_GENERATED", "VALIDATED", "WRITTEN"
    ]

    state = "idle"
    for event in events:
        new_state, new_ctx, traces, err = run_frame(
            blueprint, context, event, {}, COMPUTE_REGISTRY
        )
        if err:
            return {"error": err, "state": new_state}
        state = new_state
        context = new_ctx
        if state in ["complete", "error"]:
            break

    return {"state": state, "context": context}


__all__ = ["BLUEPRINT_PATH", "COMPUTE_REGISTRY", "run"]
