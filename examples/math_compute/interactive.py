#!/usr/bin/env python3
"""
    L++ Interactive Calculator
    Type numbers, operators (+,-,*,/), = to compute
    State persistence: save/load between sessions
"""

from frame_py.compiler import compile_blueprint
import sys
import importlib.util
from pathlib import Path

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE.parent.parent / "src"))

REGISTRY = {
    ("math", "calculate"): lambda p: (
        {
            "error": "div/0",
            "status": "failed"
        } if p["op"] == "/" and p["b"] == 0
        else {
            "result": eval(
                f"{p['a']} {p['op']} {p['b']}"
            ), "status": "success"
        }
    )
}

# Default state file location
STATES_DIR = HERE / "states"


def load():
    """Compile and load calculator."""
    out = HERE / "results" / "interactive_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "math_compute.json"), str(out))
    spec = importlib.util.spec_from_file_location("calc", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.create_operator(REGISTRY)


def main():
    print("\nL++ Calculator (h=help, q=quit)\n")
    calc = load()

    # Try to load saved state
    state_path = STATES_DIR / "calculator.json"
    if state_path.exists():
        if calc.load_state(str(state_path)):
            print(f"  [Restored state from {state_path}]")

    while True:
        # Display comes from compiled rules
        print(f"  [{calc.state}] {calc.display()}")

        try:
            cmd = input("> ").strip()
        except (EOFError, KeyboardInterrupt):
            # Auto-save on exit
            saved = calc.save_state(str(state_path))
            print(f"\n  [State saved to {saved}]")
            break

        if not cmd:
            continue
        if cmd in "qQ":
            # Save state on quit
            saved = calc.save_state(str(state_path))
            print(f"  [State saved to {saved}]")
            break
        if cmd in "hH?":
            print("  [num] + - * / = c(lear) s(tate)")
            print("  save  - save state to file")
            print("  load  - load state from file")
            print("  q     - quit (auto-saves)")
            continue
        if cmd in "cC":
            calc.dispatch("CLEAR")
            continue
        if cmd in "sS":
            print(f"  {calc.context}")
            continue
        if cmd == "save":
            saved = calc.save_state(str(state_path))
            print(f"  [Saved to {saved}]")
            continue
        if cmd == "load":
            if calc.load_state(str(state_path)):
                print(f"  [Loaded from {state_path}]")
            else:
                print("  [No saved state found]")
            continue
        if cmd == "=":
            calc.dispatch("EQUALS")
            continue
        if cmd in "+-*/":
            calc.dispatch("OPERATOR", {"op": cmd})
            continue
        try:
            n = float(cmd)
            calc.dispatch("NUMBER", {"value": int(n) if n.is_integer() else n})
        except ValueError:
            print(f"  ? {cmd}")


if __name__ == "__main__":
    main()
