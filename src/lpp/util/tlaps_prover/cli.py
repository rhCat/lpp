#!/usr/bin/env python3
"""
TLAPS Proof Generator CLI

Generates TLAPS-ready TLA+ specifications with formal proofs.

Usage:
    lpp util tlaps_prover <blueprint.json> [--output <dir>] [--verify]
    python -m lpp.util.tlaps_prover <blueprint.json>

Examples:
    lpp util tlaps_prover blueprint.json
    lpp util tlaps_prover blueprint.json --output tla/
    lpp util tlaps_prover blueprint.json --verify
"""
import sys
import argparse
from pathlib import Path


def main(args=None):
    parser = argparse.ArgumentParser(
        description='Generate TLAPS-ready TLA+ specs with proofs'
    )
    parser.add_argument('blueprint', nargs='?',
                        help='Path to L++ blueprint JSON')
    parser.add_argument('--output', '-o', default='.',
                        help='Output directory (default: current)')
    parser.add_argument('--verify', '-v', action='store_true',
                        help='Run TLAPS verification after generation')

    parsed = parser.parse_args(args)

    if not parsed.blueprint:
        parser.print_help()
        print("\nError: blueprint path required")
        return 1

    bp_path = Path(parsed.blueprint)
    if not bp_path.exists():
        print(f"Error: Blueprint not found: {bp_path}")
        return 1

    from . import run

    result = run({
        "blueprintPath": str(bp_path),
        "outputDir": parsed.output,
        "verify": parsed.verify,
    })

    if result.get("error"):
        print(f"Error: {result['error']}")
        return 1

    ctx = result.get("context", {})
    tla_spec = ctx.get("tlaSpec")

    if tla_spec:
        print(f"Generated: {tla_spec}")

    if parsed.verify and ctx.get("proofResult"):
        pr = ctx["proofResult"]
        if pr.get("success"):
            print("TLAPS verification: PASSED")
        else:
            print(f"TLAPS verification: FAILED - {pr.get('error', 'Unknown')}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
