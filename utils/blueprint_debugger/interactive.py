#!/usr/bin/env python3
"""
L++ Blueprint Debugger - Interactive Shell

Step-through debugging for L++ blueprints with breakpoints, inspection,
and time-travel debugging capabilities.
"""

import sys
import json
from pathlib import Path

# Import from src package
from src import DEBUG_REGISTRY
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with given COMPUTE registry."""
    import importlib.util

    out = HERE / "results" / f"{Path(blueprint_json).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint_json, str(out))

    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


def print_help():
    """Print help message."""
    print("""
L++ Blueprint Debugger Commands:

  LOADING:
    load <path>       - Load blueprint for debugging
    unload            - Unload current blueprint

  DEBUGGING:
    start             - Start debug session (init state)
    stop              - Stop debugging, return to loaded
    reset             - Reset to initial state (keep breakpoints)

  STEPPING:
    step [event]      - Step one transition (with optional event)
    s [event]         - Alias for step
    over [event]      - Step over (skip action details)
    back              - Step back to previous state
    b                 - Alias for back

  EXECUTION:
    run               - Run until breakpoint or terminal
    continue          - Continue after breakpoint
    c                 - Alias for continue
    pause             - Pause execution

  BREAKPOINTS:
    bp <type> <target> [condition]
                      - Set breakpoint (types: state, transition, gate, event, conditional)
    bp state loaded   - Example: break on entering 'loaded' state
    bp event LOAD     - Example: break on LOAD event
    bp cond "x > 5"   - Example: conditional breakpoint
    del <id>          - Remove breakpoint by ID
    list              - List all breakpoints

  INSPECTION:
    state             - Inspect current state
    ctx [key]         - Inspect context (or specific key)
    eval <expr>       - Evaluate expression
    events            - Show available events

  WATCHES:
    watch <expr> [name] - Add watch expression
    unwatch <id>      - Remove watch
    watches           - Show all watches

  TIME-TRAVEL:
    history           - Show execution history
    goto <step>       - Jump to specific step
    compare [s1] [s2] - Compare states at two steps

  OTHER:
    status            - Show current status
    help              - Show this help
    quit              - Exit debugger
""")


def main():
    print("\n[L++ Blueprint Debugger]")
    print("Type 'help' for commands\n")

    dbg = compile_and_load(str(HERE / "blueprint_debugger.json"), DEBUG_REGISTRY)

    # CLI arg for auto-load
    if len(sys.argv) > 1:
        dbg.dispatch("LOAD", {"path": sys.argv[1]})
        if dbg.state == "loaded":
            dbg.dispatch("START")

    ICONS = {
        "idle": "[.]",
        "loaded": "[+]",
        "debugging": "[>]",
        "paused": "[||]",
        "inspecting": "[?]",
        "time_travel": "[<>]",
        "error": "[!]"
    }

    while True:
        icon = ICONS.get(dbg.state, "[?]")
        debug_state = dbg.context.get("debug_state", "-")
        history_idx = dbg.context.get("history_index", 0)

        prompt = f"{icon} {dbg.state}"
        if dbg.state in ("debugging", "paused"):
            prompt = f"{icon} {debug_state} (step {history_idx})"
            if dbg.state == "paused":
                hit_bp = dbg.context.get("hit_breakpoint")
                if hit_bp:
                    prompt += f" @{hit_bp['id']}"

        # Show output if any
        output = dbg.context.get("output")
        if output:
            print(f"\n{output}")
            dbg.set("output", None)

        # Show error if any
        error = dbg.context.get("error")
        if error and dbg.state != "error":
            print(f"\n[ERROR] {error}")
            dbg.set("error", None)

        try:
            cmd = input(f"\n{prompt}> ").strip()
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        parts = cmd.split(maxsplit=2)
        action = parts[0].lower()
        arg1 = parts[1] if len(parts) > 1 else None
        arg2 = parts[2] if len(parts) > 2 else None

        # Parse commands
        if action in ("q", "quit", "exit"):
            break

        elif action == "help":
            print_help()

        elif action == "load" and arg1:
            dbg.dispatch("LOAD", {"path": arg1})
            if dbg.context.get("blueprint"):
                print(f"Loaded: {dbg.context.get('blueprint_name')}")

        elif action == "self":
            dbg.dispatch("LOAD", {"path": str(HERE / "blueprint_debugger.json")})
            if dbg.context.get("blueprint"):
                dbg.dispatch("START")

        elif action == "viz":
            viz_path = HERE.parent / "visualizer" / "visualizer.json"
            dbg.dispatch("LOAD", {"path": str(viz_path)})
            if dbg.context.get("blueprint"):
                dbg.dispatch("START")

        elif action == "sim":
            sim_path = HERE.parent / "event_simulator" / "event_simulator.json"
            dbg.dispatch("LOAD", {"path": str(sim_path)})
            if dbg.context.get("blueprint"):
                dbg.dispatch("START")

        elif action == "unload":
            dbg.dispatch("UNLOAD")

        elif action == "start":
            dbg.dispatch("START")

        elif action == "stop":
            dbg.dispatch("STOP")

        elif action == "reset":
            dbg.dispatch("RESET")

        elif action in ("step", "s"):
            dbg.dispatch("STEP", {
                "event_name": arg1.upper() if arg1 else None,
                "payload": {}
            })

        elif action == "over":
            dbg.dispatch("STEP_OVER", {
                "event_name": arg1.upper() if arg1 else None,
                "payload": {}
            })

        elif action in ("back", "b"):
            dbg.dispatch("STEP_BACK")

        elif action == "run":
            dbg.dispatch("RUN", {"max_steps": int(arg1) if arg1 else 1000})

        elif action in ("continue", "c"):
            dbg.dispatch("CONTINUE")

        elif action == "pause":
            dbg.dispatch("PAUSE")

        elif action == "bp" and arg1:
            # bp <type> <target> [condition]
            bp_type = arg1.lower()
            target = arg2
            condition = None

            # Handle "bp cond <expr>" shorthand
            if bp_type in ("cond", "conditional"):
                bp_type = "conditional"
                target = arg2 if arg2 else arg1
                condition = target

            # Parse remaining args for condition
            if len(parts) > 2:
                rest = cmd.split(maxsplit=3)
                if len(rest) > 3:
                    condition = rest[3]

            if target:
                dbg.dispatch("SET_BREAKPOINT", {
                    "type": bp_type,
                    "target": target,
                    "condition": condition
                })
            else:
                print("Usage: bp <type> <target> [condition]")
                print("Types: state, transition, gate, event, conditional")

        elif action == "del" and arg1:
            dbg.dispatch("REMOVE_BREAKPOINT", {"bp_id": arg1})

        elif action == "list":
            dbg.dispatch("LIST_BREAKPOINTS")

        elif action == "state":
            dbg.dispatch("INSPECT_STATE")

        elif action == "ctx":
            dbg.dispatch("INSPECT_CONTEXT", {"key": arg1})

        elif action == "eval" and arg1:
            # Rejoin the expression
            expr = cmd[5:].strip()  # Everything after "eval "
            dbg.dispatch("EVAL", {"expression": expr})

        elif action == "events":
            avail = dbg.context.get("available_transitions", [])
            print("\nAvailable Events:")
            for t in avail:
                gates = t.get("gates", [])
                gate_str = f" [gates: {gates}]" if gates else ""
                print(f"  {t['event']}: {t['from']} -> {t['to']}{gate_str}")

        elif action == "watch" and arg1:
            # watch <expr> [name]
            expr = arg1
            name = arg2
            dbg.dispatch("ADD_WATCH", {"expression": expr, "name": name})

        elif action == "unwatch" and arg1:
            dbg.dispatch("REMOVE_WATCH", {"watch_id": arg1})

        elif action == "watches":
            dbg.dispatch("GET_WATCHES")

        elif action == "history":
            dbg.dispatch("HISTORY")

        elif action == "goto" and arg1:
            try:
                step_num = int(arg1)
                dbg.dispatch("GOTO", {"step": step_num})
            except ValueError:
                print("Error: step must be a number")

        elif action == "compare":
            step1 = int(arg1) if arg1 else 0
            step2 = int(arg2) if arg2 else None
            dbg.dispatch("COMPARE", {"step1": step1, "step2": step2})

        elif action == "status":
            dbg.dispatch("STATUS")

        elif action == "full":
            # Show full operator context
            print("\nFull Operator Context:")
            print(json.dumps(dbg.context, indent=2, default=str))

        # Direct event dispatch (if in debugging/paused state)
        elif dbg.state in ("debugging", "paused"):
            avail = dbg.context.get("available_events", [])
            if action.upper() in avail:
                dbg.dispatch("STEP", {
                    "event_name": action.upper(),
                    "payload": {}
                })
            else:
                print(f"Unknown command or event: {action}")
                print(f"Available events: {avail[:5]}{'...' if len(avail) > 5 else ''}")

        else:
            print(f"Unknown command: {action}")
            print("Type 'help' for available commands")

    print("\nGoodbye!")


if __name__ == "__main__":
    main()
