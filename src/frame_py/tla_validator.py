"""
L++ TLA+ Generator and Validator

Universal adaptor that generates TLA+ specifications from any L++ blueprint.
Automatically extracts domains from context_schema (enums, numbers, strings).
Can validate using TLC model checker if available.
"""

import json
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Optional, Tuple, Dict


class TLAValidationError(Exception):
    """Raised when TLA+ validation fails."""
    pass


def _extract_domains(bp: dict) -> Dict[str, dict]:
    """
    Extract type domains from blueprint context_schema.

    Returns dict mapping property name to domain info:
        {
            "prop_name": {
                "type": "number" | "string" | "enum" | "boolean",
                "enum_values": [...] if enum,
                "domain_name": "PropNameDomain" for TLA+
            }
        }
    """
    domains = {}
    context_schema = bp.get("context_schema", {})
    properties = context_schema.get("properties", {})

    for prop, spec in properties.items():
        ptype = spec.get("type", "string")
        enum_vals = spec.get("enum", [])

        domain_info = {
            "type": ptype,
            "nullable": True,  # All L++ context values can be NULL
        }

        if enum_vals:
            # Has explicit enum - create named domain
            domain_info["type"] = "enum"
            domain_info["enum_values"] = enum_vals
            # Create TLA+ safe domain name (PascalCase)
            domain_info["domain_name"] = _to_pascal_case(prop) + "Domain"
        elif ptype == "number":
            domain_info["domain_name"] = "BoundedInt"
        elif ptype == "boolean":
            domain_info["domain_name"] = "BOOLEAN"
        else:
            # String without enum - any string (use STRING placeholder)
            domain_info["domain_name"] = None  # Will use TRUE check

        domains[prop] = domain_info

    return domains


def _to_pascal_case(name: str) -> str:
    """Convert snake_case or kebab-case to PascalCase."""
    parts = re.split(r'[-_]', name)
    return ''.join(p.capitalize() for p in parts)


def _to_tla_safe(name: str) -> str:
    """Make identifier TLA+ safe (alphanumeric + underscore)."""
    return re.sub(r'[^a-zA-Z0-9_]', '_', name)


def _escape_tla_string(s: str) -> str:
    """
    Escape a string for TLA+ string literal.
    Handles special characters that conflict with TLA+ operators.
    """
    # "/" conflicts with TLA+ division - use "div" for division operator
    if s == "/":
        return "div"
    # Escape backslashes and quotes
    s = s.replace("\\", "\\\\")
    s = s.replace('"', '\\"')
    return s


def generate_tla(
    bp: dict,
    int_min: int = -10,
    int_max: int = 10,
    max_history: int = 5
) -> str:
    """
    Generate TLA+ specification from any L++ blueprint.

    Automatically extracts:
    - States from states dict
    - Events from transitions
    - Domains from context_schema (numbers, enums, strings)
    - Gates and their expressions

    Args:
        bp: Blueprint dictionary
        int_min: Minimum integer value for bounded model checking
        int_max: Maximum integer value for bounded model checking
        max_history: Maximum event history length

    Returns:
        TLA+ specification as string
    """
    lines = []

    # Extract blueprint components
    name = _to_tla_safe(bp.get("id", "Blueprint"))
    states = list(bp.get("states", {}).keys())
    entry = bp.get("entry_state", states[0] if states else "init")
    terminal = bp.get("terminal_states", [])
    transitions = bp.get("transitions", [])
    gates = bp.get("gates", {})
    context_schema = bp.get("context_schema", {})
    properties = context_schema.get("properties", {})

    # Extract domains from schema
    domains = _extract_domains(bp)

    # Module header
    lines.append(
        "---------------------------- "
        f"MODULE {name} ----------------------------"
    )
    lines.append(f"\\* L++ Blueprint: {bp.get('name', 'Unnamed')}")
    lines.append(f"\\* Version: {bp.get('version', '0.0.0')}")
    lines.append("\\* Auto-generated TLA+ specification (universal adaptor)")
    lines.append("")
    lines.append("EXTENDS Integers, Sequences, TLC")
    lines.append("")

    # Bounds for state space
    lines.append(
        "\\* =========================================================")
    lines.append("\\* BOUNDS - Constrain state space for model checking")
    lines.append(
        "\\* =========================================================")
    lines.append(f"INT_MIN == {int_min}")
    lines.append(f"INT_MAX == {int_max}")
    lines.append(f"MAX_HISTORY == {max_history}")
    lines.append("BoundedInt == INT_MIN..INT_MAX")
    lines.append("")

    # NULL constant
    lines.append("\\* NULL constant for uninitialized values")
    lines.append("CONSTANT NULL")
    lines.append("")

    # Generate domain sets for enums (dynamically from schema)
    enum_domains = {
        prop: info for prop, info in domains.items()
        if info.get("type") == "enum"
    }
    if enum_domains:
        lines.append(
            "\\* =========================================================")
        lines.append("\\* DOMAINS - Auto-extracted from context_schema")
        lines.append(
            "\\* =========================================================")
        for prop, info in enum_domains.items():
            enum_vals = info["enum_values"]
            # Escape values for TLA+
            escaped = [f'"{_escape_tla_string(v)}"' for v in enum_vals]
            domain_name = info["domain_name"]
            lines.append(f"{domain_name} == {{{', '.join(escaped)}}}")
        lines.append("")

    # States
    lines.append("\\* States")
    state_set = ", ".join(f'"{s}"' for s in states)
    lines.append(f"States == {{{state_set}}}")
    lines.append("")

    # Events from transitions
    events = set(t.get("on_event", "") for t in transitions)
    events.discard("")  # Remove empty
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
        safe_prop = _to_tla_safe(prop)
        desc = properties[prop].get("description", "Context variable")
        lines.append(f"    {safe_prop},           \\* {desc}")
    lines.append("    event_history    \\* Trace of events")
    lines.append("")

    var_list = ["state"] + [_to_tla_safe(p) for p in properties.keys()] + \
        ["event_history"]
    lines.append(f"vars == <<{', '.join(var_list)}>>")
    lines.append("")

    # Type invariant (structural correctness)
    lines.append("\\* Type invariant - structural correctness")
    lines.append("TypeInvariant ==")
    lines.append("    /\\ state \\in States")
    for prop, info in domains.items():
        safe_prop = _to_tla_safe(prop)
        domain_name = info.get("domain_name")
        if domain_name:
            lines.append(
                f"    /\\ ({safe_prop} \\in {domain_name}) \\/ "
                f"({safe_prop} = NULL)"
            )
        else:
            # String without enum - accept anything
            lines.append(f"    /\\ TRUE  \\* {safe_prop}: any string or NULL")
    lines.append("")

    # State constraint (bounds exploration)
    lines.append("\\* State constraint - limits TLC exploration depth")
    lines.append("StateConstraint ==")
    lines.append("    /\\ Len(event_history) <= MAX_HISTORY")
    for prop, info in domains.items():
        safe_prop = _to_tla_safe(prop)
        if info.get("type") == "number":
            lines.append(
                f"    /\\ ({safe_prop} = NULL) \\/ "
                f"({safe_prop} \\in BoundedInt)"
            )
    lines.append("")

    # Initial state
    lines.append("\\* Initial state")
    lines.append("Init ==")
    lines.append(f'    /\\ state = "{entry}"')
    for prop in properties.keys():
        safe_prop = _to_tla_safe(prop)
        lines.append(f"    /\\ {safe_prop} = NULL")
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
            tla_expr = _python_to_tla(expr, properties, domains)
            lines.append(f"    /\\ {tla_expr}  \\* gate: {gid}")

        # State transition
        lines.append(f'    /\\ state\' = "{to_state}"')

        # Context unchanged (simplified - real impl would track mutations)
        for prop in properties.keys():
            safe_prop = _to_tla_safe(prop)
            lines.append(f"    /\\ {safe_prop}' = {safe_prop}")

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


def _python_to_tla(
    expr: str,
    properties: dict,
    domains: Optional[Dict[str, dict]] = None
) -> str:
    """
    Universal Python to TLA+ expression converter.

    Handles:
    - None/null checks -> NULL
    - Boolean operators (and, or, not)
    - Comparison operators (==, !=, <, >, <=, >=)
    - 'in' membership tests -> \\in {set} or \\in DomainName
    - String literals ('x' or "x") -> "x"
    - Special characters (/ -> div in string literals)
    - Domain-aware: uses domain names when available
    """
    tla = expr
    domains = domains or {}

    # First, convert Python string literals to TLA+ format
    # Handle both single and double quoted strings
    def convert_string_literal(m):
        s = m.group(1) or m.group(2)  # Group 1 is single-quoted, 2 is double
        # Escape special TLA+ characters
        escaped = _escape_tla_string(s)
        return f'"{escaped}"'

    # Single-quoted strings: 'value'
    tla = re.sub(r"'([^']*)'(?!')", convert_string_literal, tla)

    # Handle 'in' operator for tuples/lists/sets
    # If we have a domain for the variable, use the domain name
    in_pattern = r"(\w+)\s+in\s+\(([^)]+)\)"

    def replace_in(m):
        var = m.group(1)
        items = m.group(2)
        # Check if this variable has a known domain
        if var in domains and domains[var].get("domain_name"):
            domain_name = domains[var]["domain_name"]
            return f"{var} \\in {domain_name}"
        # Otherwise, build inline set
        return f"{var} \\in {{{items}}}"

    tla = re.sub(in_pattern, replace_in, tla)

    # Also handle list syntax: x in ['a', 'b']
    list_pattern = r"(\w+)\s+in\s+\[([^\]]+)\]"
    tla = re.sub(list_pattern, replace_in, tla)

    # Python to TLA+ operator translations
    translations = [
        (" is not None", " /= NULL"),
        (" is None", " = NULL"),
        (" != None", " /= NULL"),
        (" == None", " = NULL"),
        ("!= None", " /= NULL"),
        ("== None", " = NULL"),
        (" and ", " /\\ "),
        (" or ", " \\/ "),
        ("not ", "~"),
        (" == ", " = "),
        (" != ", " /= "),
        (" >= ", " >= "),
        (" <= ", " <= "),
        (" > ", " > "),
        (" < ", " < "),
        ("True", "TRUE"),
        ("False", "FALSE"),
        ("None", "NULL"),  # Standalone None -> NULL
        ("_state", "state"),  # L++ uses _state for current state
    ]

    for py_op, tla_op in translations:
        # Use word boundary for _state to avoid matching sim_state -> simstate
        if py_op == "_state":
            tla = re.sub(r'\b_state\b', tla_op, tla)
        else:
            tla = tla.replace(py_op, tla_op)

    # Handle len() -> Len() for TLA+ (case-sensitive)
    tla = re.sub(r'\blen\(', 'Len(', tla)

    return tla


def generate_cfg(bp: dict, check_deadlock: bool = False) -> str:
    """
    Generate TLC configuration file.

    Note: CHECK_DEADLOCK defaults to FALSE because L++ state machines
    may intentionally allow states with no outgoing transitions.
    """
    lines = []
    name = _to_tla_safe(bp.get("id", "Blueprint"))

    lines.append(f"\\* TLC Configuration for {name}")
    lines.append("\\* Bounded model checking configuration")
    lines.append("")
    lines.append("SPECIFICATION Spec")
    lines.append("")
    lines.append("\\* State constraint to bound exploration")
    lines.append("CONSTRAINT StateConstraint")
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
    lines.append("CONSTANT")
    lines.append("NULL = NULL")

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

    name = _to_tla_safe(bp.get("id", "Blueprint"))

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


def save_tla(
    bp: dict,
    output_dir: str,
    int_min: int = -10,
    int_max: int = 10,
    max_history: int = 5
) -> Tuple[str, str]:
    """
    Save TLA+ spec and config to files.

    Args:
        bp: Blueprint dictionary
        output_dir: Directory to save files
        int_min: Minimum integer bound
        int_max: Maximum integer bound
        max_history: Maximum event history length

    Returns:
        Tuple of (tla_path, cfg_path)
    """
    name = _to_tla_safe(bp.get("id", "Blueprint"))

    output_path = Path(output_dir)
    output_path.mkdir(parents=True, exist_ok=True)

    tla_path = output_path / f"{name}.tla"
    cfg_path = output_path / f"{name}.cfg"

    tla_path.write_text(generate_tla(bp, int_min, int_max, max_history))
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
    --int-min N         Minimum integer value (default: -10)
    --int-max N         Maximum integer value (default: 10)
    --max-history N     Maximum event history length (default: 5)

Bounds control state space explosion:
    Small bounds (e.g., -3..3, history=3) = fast checking, limited coverage
    Large bounds (e.g., -100..100, history=10) = thorough but slow

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
    int_min = -10
    int_max = 10
    max_history = 5

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
        elif arg == "--int-min" and i + 1 < len(sys.argv):
            int_min = int(sys.argv[i + 1])
            i += 2
        elif arg == "--int-max" and i + 1 < len(sys.argv):
            int_max = int(sys.argv[i + 1])
            i += 2
        elif arg == "--max-history" and i + 1 < len(sys.argv):
            max_history = int(sys.argv[i + 1])
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

    # Print bounds info
    print(
        f"Bounds: integers [{int_min}..{int_max}], history max {max_history}")

    # Generate TLA+
    tla_spec = generate_tla(bp, int_min, int_max, max_history)

    if output_dir:
        tla_path, cfg_path = save_tla(
            bp, output_dir, int_min, int_max, max_history)
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
