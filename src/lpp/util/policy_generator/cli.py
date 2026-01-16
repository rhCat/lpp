"""
L++ Policy Generator CLI

Generate L++ policies from source repositories or decoded blueprints.

Usage:
    lpp util policy_generator <source_path> [options]

Options:
    --name <name>       Name for the generated policy
    --repo <url>        Git repository URL for provenance
    --output <dir>      Output directory (default: ./generated_policies)
"""

import argparse
import sys
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(
        prog="lpp util policy_generator",
        description="Generate L++ policies from source code with provenance"
    )
    parser.add_argument(
        "source_path",
        help="Path to source repo, decoded JSON, or Python file"
    )
    parser.add_argument(
        "--name", "-n",
        dest="policy_name",
        default=None,
        help="Name for the generated policy (default: derived from source)"
    )
    parser.add_argument(
        "--repo", "-r",
        dest="source_repo",
        default=None,
        help="Git repository URL for provenance tracking"
    )
    parser.add_argument(
        "--output", "-o",
        dest="output_path",
        default="./generated_policies",
        help="Output directory (default: ./generated_policies)"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Show detailed progress"
    )

    args = parser.parse_args()

    # Derive policy name from source if not provided
    source = Path(args.source_path)
    if not args.policy_name:
        args.policy_name = source.stem.replace("_decoded", "")

    # Import and run
    from lpp.util.policy_generator import run

    params = {
        "source_path": str(source.resolve()),
        "policy_name": args.policy_name,
        "source_repo": args.source_repo,
        "output_path": str(Path(args.output_path).resolve()),
    }

    if args.verbose:
        print(f"Policy Generator")
        print(f"  Source: {params['source_path']}")
        print(f"  Name:   {params['policy_name']}")
        print(f"  Repo:   {params['source_repo'] or '(not specified)'}")
        print(f"  Output: {params['output_path']}")
        print()

    result = run(params)

    if result.get("error"):
        print(f"Error: {result['error']}")
        return 1

    state = result.get("state", "unknown")
    ctx = result.get("context", {})

    if state == "complete":
        print("Policy generated successfully!")
        print(f"  Output: {ctx.get('output_path')}")
        if ctx.get("tla_path"):
            print(f"  TLA+:   {ctx.get('tla_path')}")
        print()
        policy = ctx.get("policy", {})
        print("Policy Summary:")
        print(f"  States: {len(policy.get('states', {}))}")
        print(f"  Terminals: {len(policy.get('terminal_states', {}))}")
        print(f"  Slots: {len(policy.get('slots', {}))}")
        print(f"  Transitions: {len(policy.get('transitions', []))}")
        return 0
    elif state == "error":
        print(f"Error: {ctx.get('error', 'Unknown error')}")
        return 1
    else:
        print(f"Unexpected state: {state}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
