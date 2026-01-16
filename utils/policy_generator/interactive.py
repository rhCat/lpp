#!/usr/bin/env python3
"""
Policy Generator Interactive CLI

Generate L++ policies from source repositories or decoded blueprints.

Usage:
    python interactive.py <source_path> [--name <policy_name>] [--repo <git_url>] [--output <dir>]

Examples:
    python interactive.py /tmp/datum_open --name service_router --repo https://github.com/rhCat/datum_open
    python interactive.py /tmp/proxy_core_decoded.json --name proxy_policy
    python interactive.py . --name my_policy --output ./policies
"""

import sys
import json
import argparse
from pathlib import Path

# Import L++ runtime first
sys.path.insert(0, str(Path(__file__).parent.parent.parent / "src"))
try:
    from lpp.core import load_blueprint, run_frame
except ImportError:
    from frame_py.compiler import compile_blueprint
    from frame_py.loader import load_blueprint
    from frame_py.lpp_core import dispatch as run_frame

# Then import compute functions
sys.path.insert(0, str(Path(__file__).parent / "src"))
from policy_generator_compute import COMPUTE_REGISTRY


def main():
    parser = argparse.ArgumentParser(
        description="Generate L++ policies from source code",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    parser.add_argument("source_path", help="Path to source repo or decoded JSON")
    parser.add_argument("--name", "-n", default="generated_policy",
                        help="Name for generated policy")
    parser.add_argument("--repo", "-r", help="Git repository URL for provenance")
    parser.add_argument("--output", "-o", help="Output directory for policy")
    parser.add_argument("--no-tla", action="store_true",
                        help="Skip TLA+ generation")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Verbose output")

    args = parser.parse_args()

    # Load blueprint
    blueprint_path = Path(__file__).parent / "policy_generator.json"
    with open(blueprint_path) as f:
        bp_raw = json.load(f)

    blueprint, err = load_blueprint(bp_raw)
    if err:
        print(f"Error loading blueprint: {err}")
        return 1

    # Initialize context
    context = {
        "source_path": args.source_path,
        "policy_name": args.name,
        "source_repo": args.repo,
        "output_path": args.output,
    }

    print(f"Policy Generator: {args.source_path}")
    print(f"  Policy name: {args.name}")
    if args.repo:
        print(f"  Source repo: {args.repo}")
    print()

    # Run through all states
    events = [
        "GENERATE",
        "ANALYZED",
        "STATES_EXTRACTED",
        "SLOTS_EXTRACTED",
        "TERMINALS_EXTRACTED",
        "COMPOSED",
        "TLA_GENERATED",
        "VALIDATED",
        "WRITTEN"
    ]

    state = "idle"
    for event in events:
        if args.verbose:
            print(f"  [{state}] -> {event}")

        new_state, new_ctx, traces, err = run_frame(
            blueprint, context, event, {}, COMPUTE_REGISTRY
        )

        if err:
            print(f"Error: {err}")
            return 1

        state = new_state
        context = new_ctx

        if args.verbose and traces:
            for trace in traces:
                print(f"    {trace}")

        if state in ["complete", "error"]:
            break

    # Output results
    if state == "complete":
        print(f"Policy generated successfully!")
        print(f"  Output: {context.get('output_path')}")
        if context.get("tla_path"):
            print(f"  TLA+:   {context.get('tla_path')}")

        # Print summary
        policy = context.get("policy", {})
        print()
        print(f"Policy Summary:")
        print(f"  States: {len(policy.get('states', {}))}")
        print(f"  Terminals: {len(policy.get('terminal_states', {}))}")
        print(f"  Slots: {len(policy.get('slots', {}))}")
        print(f"  Transitions: {len(policy.get('transitions', []))}")

        return 0

    elif state == "error":
        print(f"Error: {context.get('error')}")
        return 1

    else:
        print(f"Unexpected state: {state}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
