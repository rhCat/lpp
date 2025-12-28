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

    # Show 'a' as the display value (either operand or result)
    a = ctx.get("a")
    b = ctx.get("b")

    if b is not None:
        return str(int(b) if isinstance(b, float) and b.is_integer() else b)
    if a is not None:
        return str(int(a) if isinstance(a, float) and a.is_integer() else a)

    return "0"


def format_expression(calc) -> str:
    """Format the full expression based on current state."""
    ctx = calc.context
    state = calc.state

    if state == "error":
        return f"Error: {ctx.get('error', 'Unknown')}"

    parts = []
    a, b, op = ctx.get("a"), ctx.get("b"), ctx.get("op")

    if a is not None:
        parts.append(str(a))

    if op and state == "has_operator":
        parts.append(op)
        parts.append("_")
    elif op and b is not None:
        parts.append(op)
        parts.append(str(b))

    return " ".join(parts) if parts else "0"


def show_state(calc):
    """Show detailed state info."""
    print(f"\n  State: {calc.state}")
    print(f"  a:     {calc.context.get('a')}")
    print(f"  op:    {calc.context.get('op')}")
    print(f"  b:     {calc.context.get('b')}")
    print(f"  error: {calc.context.get('error')}")
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
