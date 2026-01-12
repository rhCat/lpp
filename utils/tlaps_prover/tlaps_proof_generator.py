#!/usr/bin/env python3
"""
L++ TLAPS Proof Generator

Generates TLAPS-ready TLA+ specifications with complete proofs for L++ blueprints.
Proves type safety and inductive invariants for all state machine blueprints.

Usage:
    python tlaps_proof_generator.py <blueprint.json> [--output <dir>] [--verify]
    python tlaps_proof_generator.py --all [--verify]
"""

import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple


def loadBlueprint(bpPath: str) -> Dict:
    """Load a blueprint JSON file."""
    with open(bpPath, 'r') as f:
        return json.load(f)


def getTerminalIds(bp: Dict) -> List[str]:
    """Get terminal state IDs (handles v0.2.0 and legacy)."""
    termStates = bp.get('terminal_states', {})
    if isinstance(termStates, dict):
        return list(termStates.keys())
    return list(termStates)


def sanitizeId(s: str) -> str:
    """Convert string to valid TLA+ identifier."""
    result = s.replace('-', '_').replace('.', '_').replace(' ', '_').replace(':', '_')
    if result and not result[0].isalpha():
        result = 'S_' + result
    return result


def generateTlapsSpec(bp: Dict, moduleName: str) -> str:
    """Generate a TLAPS-ready TLA+ specification with complete proofs."""

    states = list(bp.get('states', {}).keys())
    transitions = bp.get('transitions', [])
    terminals = getTerminalIds(bp)
    entryState = bp.get('entry_state', states[0] if states else 'idle')

    # Build lines
    lines = []

    # Header
    lines.append(f"--------------------------- MODULE {moduleName}_proofs ---------------------------")
    lines.append("(*")
    lines.append(f" * L++ Blueprint: {bp.get('name', moduleName)}")
    lines.append(f" * Version: {bp.get('version', '1.0.0')}")
    lines.append(" * TLAPS Mathematical Proof")
    lines.append(" *)")
    lines.append("")
    lines.append("EXTENDS Naturals, TLAPS")
    lines.append("")

    # Constants for states
    lines.append("CONSTANTS")
    stateConsts = [f"STATE_{sanitizeId(s)}" for s in states]
    lines.append("    " + ", ".join(stateConsts))
    lines.append("")

    # Distinctness assumption
    lines.append("ASSUME ConstantsDistinct ==")
    distinctPairs = []
    for i, s1 in enumerate(stateConsts):
        for s2 in stateConsts[i+1:]:
            distinctPairs.append(f"{s1} /= {s2}")
    if distinctPairs:
        lines.append("    /\\ " + "\n    /\\ ".join(distinctPairs))
    else:
        lines.append("    TRUE")
    lines.append("")

    # Variables
    lines.append("VARIABLE state")
    lines.append("")
    lines.append("vars == <<state>>")
    lines.append("")

    # Type definitions
    lines.append("States == {" + ", ".join(stateConsts) + "}")
    if terminals:
        termConsts = [f"STATE_{sanitizeId(t)}" for t in terminals]
        lines.append("TerminalStates == {" + ", ".join(termConsts) + "}")
    else:
        lines.append("TerminalStates == {}")
    lines.append("")

    # Type invariant
    lines.append("TypeInvariant == state \\in States")
    lines.append("")

    # Init
    lines.append("Init == state = STATE_" + sanitizeId(entryState))
    lines.append("")

    # Transitions
    transNames = []
    for trans in transitions:
        transId = trans.get('id', 'unknown')
        transName = "t_" + sanitizeId(transId)
        transNames.append(transName)

        fromState = trans.get('from', '*')
        toState = trans.get('to', '*')

        lines.append(f"(* Transition: {transId} *)")
        lines.append(f"{transName} ==")

        if fromState == '*':
            lines.append("    /\\ TRUE  \\* Global transition")
        else:
            lines.append(f"    /\\ state = STATE_{sanitizeId(fromState)}")

        lines.append(f"    /\\ state' = STATE_{sanitizeId(toState)}")
        lines.append("")

    # Next relation
    if transNames:
        lines.append("Next ==")
        lines.append("    \\/ " + "\n    \\/ ".join(transNames))
    else:
        lines.append("Next == FALSE")
    lines.append("")

    # Spec
    lines.append("Spec == Init /\\ [][Next]_vars")
    lines.append("")

    # Inductive invariant (same as TypeInvariant for simple specs)
    lines.append("Inv == TypeInvariant")
    lines.append("")

    # Proofs section
    lines.append("-----------------------------------------------------------------------------")
    lines.append("(* TLAPS Proofs *)")
    lines.append("")

    # Init establishes invariant
    lines.append("LEMMA InitEstablishesInv == Init => Inv")
    lines.append("BY DEF Init, Inv, TypeInvariant, States")
    lines.append("")

    # Each transition preserves invariant
    for transName in transNames:
        lemmaName = transName.replace("t_", "").title().replace("_", "") + "PreservesInv"
        lines.append(f"LEMMA {lemmaName} == Inv /\\ {transName} => Inv'")
        lines.append(f"BY ConstantsDistinct DEF Inv, {transName}, TypeInvariant, States")
        lines.append("")

    # Stuttering preserves invariant
    lines.append("LEMMA StutterPreservesInv == Inv /\\ UNCHANGED vars => Inv'")
    lines.append("BY DEF Inv, vars, TypeInvariant")
    lines.append("")

    # Next preserves invariant
    lines.append("LEMMA NextPreservesInv == Inv /\\ Next => Inv'")
    if transNames:
        lemmaRefs = [tn.replace("t_", "").title().replace("_", "") + "PreservesInv" for tn in transNames]
        lines.append("BY " + ", ".join(lemmaRefs) + " DEF Next")
    else:
        lines.append("BY DEF Next, Inv")
    lines.append("")

    # Inductive invariant theorem
    lines.append("THEOREM InductiveInvariant == Inv /\\ [Next]_vars => Inv'")
    lines.append("BY NextPreservesInv, StutterPreservesInv DEF vars")
    lines.append("")

    # Main safety theorem
    lines.append("THEOREM TypeSafety == Spec => []Inv")
    lines.append("<1>1. Init => Inv")
    lines.append("  BY InitEstablishesInv")
    lines.append("<1>2. Inv /\\ [Next]_vars => Inv'")
    lines.append("  BY InductiveInvariant")
    lines.append("<1>3. QED")
    lines.append("  BY <1>1, <1>2, PTL DEF Spec")
    lines.append("")

    lines.append("=============================================================================")

    return "\n".join(lines)


def runTlaps(tlaPath: str) -> Tuple[bool, str]:
    """Run TLAPS on a TLA+ file. Returns (success, output)."""
    try:
        # Use absolute path and run from the file's directory
        absPath = os.path.abspath(tlaPath)
        tlaDir = os.path.dirname(absPath)
        tlaFile = os.path.basename(absPath)

        result = subprocess.run(
            ['/usr/local/bin/tlapm', '--toolbox', '0', '0', tlaFile],
            capture_output=True,
            text=True,
            timeout=300,
            cwd=tlaDir
        )
        output = result.stdout + result.stderr

        # Check for success
        if "obligations failed" in output:
            # Extract failure count
            import re
            match = re.search(r'(\d+)/(\d+) obligations failed', output)
            if match:
                failed = int(match.group(1))
                total = int(match.group(2))
                return False, f"FAILED: {failed}/{total} obligations failed"

        if "All" in output and "obligations proved" in output:
            import re
            match = re.search(r'All (\d+) obligations proved', output)
            if match:
                return True, f"PASSED: All {match.group(1)} obligations proved"

        return False, f"UNKNOWN: {output[-500:]}"

    except subprocess.TimeoutExpired:
        return False, "TIMEOUT: Proof took too long"
    except FileNotFoundError:
        return False, "ERROR: TLAPS not found at /usr/local/bin/tlapm"
    except Exception as e:
        return False, f"ERROR: {str(e)}"


def processBlueprint(bpPath: str, outputDir: Optional[str] = None, verify: bool = False) -> Tuple[str, bool, str]:
    """Process a single blueprint. Returns (name, success, message)."""
    try:
        bp = loadBlueprint(bpPath)

        # Skip if not a valid blueprint
        if 'states' not in bp or 'transitions' not in bp:
            return bpPath, True, "SKIPPED: Not a state machine blueprint"

        # Skip assembly blueprints (they have 'components')
        if 'components' in bp:
            return bpPath, True, "SKIPPED: Assembly blueprint (use assembly_validator)"

        bpName = bp.get('id', Path(bpPath).stem)
        moduleName = sanitizeId(bpName)

        # Generate spec
        tlaSpec = generateTlapsSpec(bp, moduleName)

        # Determine output path
        if outputDir:
            os.makedirs(outputDir, exist_ok=True)
            tlaPath = os.path.join(outputDir, f"{moduleName}_proofs.tla")
        else:
            # Put in tla/ folder next to blueprint
            bpDir = os.path.dirname(bpPath)
            tlaDir = os.path.join(bpDir, 'tla')
            os.makedirs(tlaDir, exist_ok=True)
            tlaPath = os.path.join(tlaDir, f"{moduleName}_proofs.tla")

        # Write spec
        with open(tlaPath, 'w') as f:
            f.write(tlaSpec)

        if verify:
            success, msg = runTlaps(tlaPath)
            return bpName, success, msg
        else:
            return bpName, True, f"GENERATED: {tlaPath}"

    except Exception as e:
        return bpPath, False, f"ERROR: {str(e)}"


def findAllBlueprints(rootDir: str = '.') -> List[str]:
    """Find all blueprint JSON files."""
    blueprints = []

    skipDirs = {'node_modules', '__pycache__', '.git', '.tlacache', 'results'}

    for root, dirs, files in os.walk(rootDir):
        # Skip certain directories
        dirs[:] = [d for d in dirs if d not in skipDirs and not d.startswith('.')]

        for f in files:
            if not f.endswith('.json'):
                continue

            fpath = os.path.join(root, f)

            # Quick check if it looks like a blueprint
            try:
                with open(fpath, 'r') as fp:
                    data = json.load(fp)
                if 'states' in data and 'transitions' in data:
                    blueprints.append(fpath)
            except:
                pass

    return blueprints


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description='Generate TLAPS proofs for L++ blueprints')
    parser.add_argument('blueprint', nargs='?', help='Blueprint JSON file')
    parser.add_argument('--all', action='store_true',
                        help='Process all blueprints in current directory')
    parser.add_argument('--output', '-o', help='Output directory for TLA+ files')
    parser.add_argument('--verify', '-v', action='store_true',
                        help='Run TLAPS verification after generating')

    args = parser.parse_args()

    if args.all:
        blueprints = findAllBlueprints('.')
        print(f"Found {len(blueprints)} blueprints")
        print()

        results = {'passed': 0, 'failed': 0, 'skipped': 0, 'generated': 0}
        failures = []

        for bp in sorted(blueprints):
            name, success, msg = processBlueprint(bp, args.output, args.verify)

            if 'SKIPPED' in msg:
                results['skipped'] += 1
                status = 'SKIP'
            elif 'GENERATED' in msg:
                results['generated'] += 1
                status = 'GEN'
            elif success:
                results['passed'] += 1
                status = 'PASS'
            else:
                results['failed'] += 1
                status = 'FAIL'
                failures.append((name, msg))

            print(f"[{status}] {name}")
            if not success and 'SKIPPED' not in msg:
                print(f"       {msg}")

        print()
        print("=" * 60)
        print(f"Results: {results['passed']} passed, {results['failed']} failed, "
              f"{results['skipped']} skipped, {results['generated']} generated")

        if failures:
            print()
            print("Failures:")
            for name, msg in failures:
                print(f"  - {name}: {msg}")
            sys.exit(1)

    elif args.blueprint:
        name, success, msg = processBlueprint(args.blueprint, args.output, args.verify)
        print(f"{name}: {msg}")
        if not success:
            sys.exit(1)

    else:
        parser.print_help()
        sys.exit(1)


if __name__ == '__main__':
    main()
