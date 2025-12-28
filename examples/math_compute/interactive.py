#!/usr/bin/env python3
"""
L++ Interactive Calculator

An interactive REPL for the L++ calculator state machine.
Type numbers, operators (+, -, *, /), and = to compute.

Commands:
  [number]  - Enter a number (e.g., 42, 3.14)
  +, -, *, / - Select operator
  =         - Compute result
  c, clear  - Clear calculator
  s, state  - Show current state
  h, help   - Show help
  q, quit   - Exit
"""

from frame_py.compiler import compile_blueprint
import sys
import importlib.util
from pathlib import Path

# Setup paths
HERE = Path(__file__).parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "src"))


# =========================================================================
# COMPUTE REGISTRY
# =========================================================================

def math_calculate(payload: dict) -> dict:
    """Hermetic compute unit for arithmetic."""
    a = payload.get("a", 0)
    b = payload.get("b", 0)
    op = payload.get("op", "+")

    ops = {
        "+": lambda x, y: x + y,
        "-": lambda x, y: x - y,
        "*": lambda x, y: x * y,
        "/": lambda x, y: x / y if y != 0 else None,
    }

    result = ops.get(op, lambda x, y: None)(a, b)
    if result is None:
        return {"error": "Invalid", "status": "failed"}
    return {"result": result, "status": "success"}


REGISTRY = {
    ("math", "calculate"): math_calculate,
}


# =========================================================================
# COMPILE AND LOAD
# =========================================================================

def setup_calculator():
    """Compile blueprint and return operator factory."""
    results_dir = HERE / "results"
    results_dir.mkdir(exist_ok=True)

    blueprint_path = HERE / "math_compute.json"
    compiled_path = results_dir / "interactive_compiled.py"

    # Compile
    compile_blueprint(str(blueprint_path), str(compiled_path))

    # Load
    spec = importlib.util.spec_from_file_location("calc", compiled_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)

    return module.create_operator


# =========================================================================
# DISPLAY HELPERS
# =========================================================================

def format_display(calc) -> str:
    """Format the calculator display."""
    state = calc.state
    ctx = calc.context

    if state == "error":
        return f"ERROR: {ctx.get('error', 'Unknown')}"

    if state == "showing_result":
        result = ctx.get("result")
        if isinstance(result, float) and result.is_integer():
            return str(int(result))
        return str(result)

    if state == "has_operand_b":
        return str(ctx.get("operand_b", 0))

    if state == "has_operator":
        a = ctx.get("operand_a", 0)
        op = ctx.get("operator", "")
        return f"{a} {op} _"

    if state == "has_operand_a":
        return str(ctx.get("operand_a", 0))

    return "0"


def format_expression(calc) -> str:
    """Format the full expression based on current state."""
    ctx = calc.context
    state = calc.state

    # Handle states explicitly
    if state == "idle":
        return "0"

    if state == "error":
        return f"Error: {ctx.get('error', 'Unknown')}"

    parts = []

    if ctx.get("operand_a") is not None:
        parts.append(str(ctx["operand_a"]))

    if ctx.get("operator") and state in (
        "has_operator", "has_operand_b", "showing_result"
    ):
        parts.append(ctx["operator"])

    if ctx.get("operand_b") is not None and state in (
        "has_operand_b", "showing_result"
    ):
        parts.append(str(ctx["operand_b"]))

    if ctx.get("result") is not None and state == "showing_result":
        parts.append("=")
        parts.append(str(ctx["result"]))

    return " ".join(parts) if parts else "0"


def show_state(calc):
    """Show detailed state info."""
    print(f"\n  State: {calc.state}")
    print(f"  operand_a: {calc.context.get('operand_a')}")
    print(f"  operator:  {calc.context.get('operator')}")
    print(f"  operand_b: {calc.context.get('operand_b')}")
    print(f"  result:    {calc.context.get('result')}")
    print(f"  error:     {calc.context.get('error')}")
    print()


def show_help():
    """Show help message."""
    print("""
  L++ Interactive Calculator
  ==========================

  Enter numbers and operators to calculate:

    123       Enter number 123
    +         Add
    -         Subtract
    *         Multiply
    /         Divide
    =         Calculate result

  Commands:
    c, clear  Clear calculator
    s, state  Show internal state
    h, help   Show this help
    q, quit   Exit

  Example: 5 + 3 =
    Type: 5 [enter] + [enter] 3 [enter] = [enter]
""")


# =========================================================================
# MAIN REPL
# =========================================================================

def main():
    print("\n" + "=" * 50)
    print("  L++ Interactive Calculator")
    print("  Type 'h' for help, 'q' to quit")
    print("=" * 50)

    # Setup
    print("\nCompiling calculator...")
    create_operator = setup_calculator()
    calc = create_operator(REGISTRY)
    print("Ready!\n")

    while True:
        # Show current display
        display = format_display(calc)
        expr = format_expression(calc)

        print(f"  [{calc.state}]")
        print(f"  {expr}")
        print(f"  Display: {display}")

        # Get input
        try:
            user_input = input("\n> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\nGoodbye!")
            break

        if not user_input:
            continue

        # Process input
        cmd = user_input.lower()

        # Quit
        if cmd in ("q", "quit", "exit"):
            print("Goodbye!")
            break

        # Help
        if cmd in ("h", "help", "?"):
            show_help()
            continue

        # Clear
        if cmd in ("c", "clear"):
            calc.dispatch("CLEAR")
            print("  Cleared.\n")
            continue

        # State
        if cmd in ("s", "state"):
            show_state(calc)
            continue

        # Equals
        if cmd == "=":
            ok, state, err = calc.dispatch("EQUALS")
            if not ok:
                print(f"  ! {err}\n")
            continue

        # Operator
        if cmd in ("+", "-", "*", "/"):
            ok, state, err = calc.dispatch("OPERATOR", {"op": cmd})
            if not ok:
                print(f"  ! {err}\n")
            continue

        # Number
        try:
            num = float(user_input)
            if num.is_integer():
                num = int(num)
            ok, state, err = calc.dispatch("NUMBER", {"value": num})
            if not ok:
                print(f"  ! {err}\n")
            continue
        except ValueError:
            pass

        print(f"  Unknown input: {user_input}")
        print("  Type 'h' for help.\n")


if __name__ == "__main__":
    main()
