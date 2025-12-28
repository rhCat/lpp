"""
L++ TLA+ Generator and Validator

Generates TLA+ specifications from L++ blueprints for formal verification.
Can validate using TLC model checker if available.
"""

import json
import subprocess
import tempfile
import os
from pathlib import Path
from typing import Optional, Tuple, List


class TLAValidationError(Exception):
    """Raised when TLA+ validation fails."""
    pass


def generate_tla(bp: dict) -> str:
    """
    Generate TLA+ specification from blueprint.

    Args:
        bp: Blueprint dictionary

    Returns:
        TLA+ specification as string
    """
    lines = []

    name = bp.get("id", "Blueprint").replace("-", "_").replace(" ", "_")
    states = list(bp.get("states", {}).keys())
    entry = bp.get("entry_state", states[0] if states else "init")
    terminal = bp.get("terminal_states", [])
    transitions = bp.get("transitions", [])
    gates = bp.get("gates", {})
    context_schema = bp.get("context_schema", {})
    properties = context_schema.get("properties", {})

    # Module header
    lines.append(
        "---------------------------- "
        f"MODULE {name} ----------------------------"
    )
    lines.append(f"\\* L++ Blueprint: {bp.get('name', 'Unnamed')}")
    lines.append(f"\\* Version: {bp.get('version', '0.0.0')}")
    lines.append("\\* Auto-generated TLA+ specification")
    lines.append("")
    lines.append("EXTENDS Integers, Sequences, TLC")
    lines.append("")

    # Constants
    lines.append("\\* States")
    state_set = ", ".join(f'"{s}"' for s in states)
    lines.append(f"States == {{{state_set}}}")
    lines.append("")

    # Events from transitions
    events = set(t.get("on_event", "") for t in transitions)
    event_set = ", ".join(f'"{e}"' for e in sorted(events))
    lines.append(f"Events == {{{event_set}}}")
    lines.append("")

    # Terminal states
    if terminal:
        term_set = ", ".join(f'"{s}"' for s in terminal)
        lines.append(f"TerminalStates == {{{term_set}}}")
    else:
        lines.append("TerminalStates == {}")
    lines.append("")

    # Variables
    lines.append("VARIABLES")
    lines.append("    state,           \\* Current state")
    for prop in properties.keys():
        lines.append(f"    {prop},           \\* Context variable")
    lines.append("    event_history    \\* Trace of events")
    lines.append("")

    var_list = ["state"] + list(properties.keys()) + ["event_history"]
    lines.append(f"vars == <<{', '.join(var_list)}>>")
    lines.append("")

    # Type invariant
    lines.append("\\* Type invariant")
    lines.append("TypeInvariant ==")
    lines.append("    /\\ state \\in States")
    lines.append("    /\\ event_history \\in Seq(Events)")
    for prop, spec in properties.items():
        ptype = spec.get("type", "string")
        if ptype == "number":
            lines.append(f"    /\\ {prop} \\in Int \\cup {{NULL}}")
        elif ptype == "string":
            lines.append(f"    /\\ {prop} \\in STRING \\cup {{NULL}}")
        else:
            lines.append(f"    /\\ TRUE  \\* {prop}")
    lines.append("")

    # Initial state
    lines.append("\\* Initial state")
    lines.append("Init ==")
    lines.append(f'    /\\ state = "{entry}"')
    for prop in properties.keys():
        lines.append(f"    /\\ {prop} = NULL")
    lines.append("    /\\ event_history = <<>>")
    lines.append("")

    # Generate transition actions
    lines.append("\\* Transitions")
    for i, trans in enumerate(transitions):
        tid = trans.get("id", f"trans_{i}")
        from_state = trans.get("from", "*")
        to_state = trans.get("to", "")
        event = trans.get("on_event", "")
        gate_ids = trans.get("gates", [])

        lines.append(f"\\* {tid}: {from_state} --({event})--> {to_state}")
        lines.append(f"{tid} ==")

        # From state condition
        if from_state == "*":
            lines.append("    /\\ TRUE  \\* from any state")
        else:
            lines.append(f'    /\\ state = "{from_state}"')

        # Gate conditions
        for gid in gate_ids:
            gate = gates.get(gid, {})
            expr = gate.get("expression", "TRUE")
            tla_expr = _python_to_tla(expr, properties)
            lines.append(f"    /\\ {tla_expr}  \\* gate: {gid}")

        # State transition
        lines.append(f'    /\\ state\' = "{to_state}"')

        # Context unchanged (simplified - real impl would track mutations)
        for prop in properties.keys():
            lines.append(f"    /\\ {prop}' = {prop}")

        # Event history
        lines.append(
            f'    /\\ event_history\' = Append(event_history, "{event}")')
        lines.append("")

    # Next state relation
    lines.append("\\* Next state relation")
    lines.append("Next ==")
    trans_ids = [t.get("id", f"trans_{i}") for i, t in enumerate(transitions)]
    if trans_ids:
        lines.append("    \\/ " + "\n    \\/ ".join(trans_ids))
    else:
        lines.append("    FALSE")
    lines.append("")

    # Spec
    lines.append("\\* Specification")
    lines.append("Spec == Init /\\ [][Next]_vars")
    lines.append("")

    # Safety properties
    lines.append("\\* Safety: Always in valid state")
    lines.append("AlwaysValidState == state \\in States")
    lines.append("")

    # Deadlock freedom (if no terminal states, should always have next)
    if not terminal:
        lines.append("\\* Liveness: No deadlock (always can make progress)")
        lines.append("NoDeadlock == <>(ENABLED Next)")
        lines.append("")

    # Reachability
    lines.append("\\* Reachability: Entry state is reachable")
    lines.append(f'EntryReachable == state = "{entry}"')
    lines.append("")

    # Terminal reachability (if terminal states exist)
    if terminal:
        lines.append("\\* Terminal states are reachable")
        term_cond = " \\/ ".join(f'state = "{t}"' for t in terminal)
        lines.append(f"TerminalReachable == <>({term_cond})")
        lines.append("")

    lines.append(
        "============================"
        "=================================================")

    return "\n".join(lines)


def _python_to_tla(expr: str, properties: dict) -> str:
    """
    Convert Python expression to TLA+ expression (best effort).
    """
    import re

    tla = expr

    # Handle 'in' operator for tuples/sets first (before other replacements)
    # e.g., "op in
    # ('+', '-', '*', '/')" -> "op \\in {\"+\", \"-\", \"*\", \"/\"}"
    in_pattern = r"(\w+)\s+in\s+\(([^)]+)\)"

    def replace_in(m):
        var = m.group(1)
        items = m.group(2)
        # Convert Python strings to TLA+ strings
        items = re.sub(r"'([^']*)'", r'"\1"', items)
        return f"{var} \\in {{{items}}}"
    tla = re.sub(in_pattern, replace_in, tla)

    # Simple translations
    tla = tla.replace(" is not None", " /= NULL")
    tla = tla.replace(" is None", " = NULL")
    tla = tla.replace(" and ", " /\\ ")
    tla = tla.replace(" or ", " \\/ ")
    tla = tla.replace("not ", "~")
    tla = tla.replace(" == ", " = ")
    tla = tla.replace(" != ", " /= ")
    tla = tla.replace("True", "TRUE")
    tla = tla.replace("False", "FALSE")
    tla = tla.replace("_state", "state")

    # Handle remaining parentheses
    # Don't convert all ) to } - only for set literals

    return tla


def generate_cfg(bp: dict, check_deadlock: bool = True) -> str:
    """
    Generate TLC configuration file.
    """
    lines = []
    name = bp.get("id", "Blueprint").replace("-", "_").replace(" ", "_")

    lines.append(f"\\* TLC Configuration for {name}")
    lines.append("")
    lines.append("SPECIFICATION Spec")
    lines.append("")
    lines.append("INVARIANT TypeInvariant")
    lines.append("INVARIANT AlwaysValidState")
    lines.append("")

    if check_deadlock:
        lines.append("CHECK_DEADLOCK TRUE")
    else:
        lines.append("CHECK_DEADLOCK FALSE")

    lines.append("")
    lines.append("\\* Constants")
    lines.append("CONSTANT NULL = NULL")
    lines.append("CONSTANT STRING = STRING")

    return "\n".join(lines)


def validate_with_tlc(
    bp: dict,
    tlc_path: str = "tlc",
    timeout: int = 60
) -> Tuple[bool, str]:
    """
    Validate blueprint using TLC model checker.

    Args:
        bp: Blueprint dictionary
        tlc_path: Path to TLC executable (default assumes in PATH)
        timeout: Timeout in seconds

    Returns:
        Tuple of (success, output_message)
    """
    # Generate TLA+ spec
    tla_spec = generate_tla(bp)
    cfg_spec = generate_cfg(bp)

    name = bp.get("id", "Blueprint").replace("-", "_").replace(" ", "_")

    # Write to temp files
    with tempfile.TemporaryDirectory() as tmpdir:
        tla_path = Path(tmpdir) / f"{name}.tla"
        cfg_path = Path(tmpdir) / f"{name}.cfg"

        tla_path.write_text(tla_spec)
        cfg_path.write_text(cfg_spec)

        # Check if TLC is available
        try:
            result = subprocess.run(
                [tlc_path, "-h"],
                capture_output=True,
                timeout=5
            )
        except FileNotFoundError:
            return False, \
                "TLC not found. Install TLA+ tools or specify tlc_path."
        except subprocess.TimeoutExpired:
            pass  # -h might hang, that's ok

        # Run TLC
        try:
            result = subprocess.run(
                [tlc_path, "-config", str(cfg_path), str(tla_path)],
                capture_output=True,
                text=True,
                timeout=timeout,
                cwd=tmpdir
            )

            output = result.stdout + result.stderr

            if result.returncode == 0 and "Error" not in output:
                return True, "TLC validation passed.\n" + output
            else:
                return False, "TLC validation failed.\n" + output

        except subprocess.TimeoutExpired:
            return False, f"TLC timed out after {timeout}s"
        except Exception as e:
            return False, f"TLC error: {str(e)}"


def save_tla(bp: dict, output_dir: str) -> Tuple[str, str]:
    """
    Save TLA+ spec and config to files.

    Args:
        bp: Blueprint dictionary
        output_dir: Directory to save files

    Returns:
        Tuple of (tla_path, cfg_path)
    """
    name = bp.get("id", "Blueprint").replace("-", "_").replace(" ", "_")

    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    tla_path = output_path / f"{name}.tla"
    cfg_path = output_path / f"{name}.cfg"

    tla_path.write_text(generate_tla(bp))
    cfg_path.write_text(generate_cfg(bp))

    return str(tla_path), str(cfg_path)


# CLI
if __name__ == "__main__":
    import sys

    usage = """
Usage: python -m frame_py.tla_validator <blueprint.json> [options]

Options:
    --output, -o DIR    Save TLA+ files to directory
    --validate, -v      Run TLC validation (requires TLC installed)
    --tlc PATH          Path to TLC executable

Examples:
    python -m frame_py.tla_validator blueprint.json
    python -m frame_py.tla_validator blueprint.json -o ./tla_specs
    python -m frame_py.tla_validator blueprint.json --validate
"""

    if len(sys.argv) < 2 or "-h" in sys.argv or "--help" in sys.argv:
        print(usage)
        sys.exit(0)

    # Parse args
    bp_path = None
    output_dir = None
    do_validate = False
    tlc_path = "tlc"

    i = 1
    while i < len(sys.argv):
        arg = sys.argv[i]
        if arg in ("--output", "-o") and i + 1 < len(sys.argv):
            output_dir = sys.argv[i + 1]
            i += 2
        elif arg in ("--validate", "-v"):
            do_validate = True
            i += 1
        elif arg == "--tlc" and i + 1 < len(sys.argv):
            tlc_path = sys.argv[i + 1]
            i += 2
        elif not arg.startswith("-"):
            bp_path = arg
            i += 1
        else:
            i += 1

    if not bp_path:
        print("Error: No blueprint file specified")
        sys.exit(1)

    # Load blueprint
    with open(bp_path) as f:
        bp = json.load(f)

    # Generate TLA+
    tla_spec = generate_tla(bp)

    if output_dir:
        tla_path, cfg_path = save_tla(bp, output_dir)
        print(f"TLA+ spec saved to: {tla_path}")
        print(f"TLC config saved to: {cfg_path}")
    else:
        print(tla_spec)

    # Validate if requested
    if do_validate:
        print("\nRunning TLC validation...")
        success, message = validate_with_tlc(bp, tlc_path)
        print(message)
        sys.exit(0 if success else 1)
