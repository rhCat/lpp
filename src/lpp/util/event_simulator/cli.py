#!/usr/bin/env python3
"""
L++ Event Sequence Simulator - Interactive Shell

A minimal CLI that drives compiled L++ operators for simulation.
Supports manual event dispatch, sequence execution, fuzzing, and
state space exploration.
"""

import sys
import json
from pathlib import Path

# Import from src package
from src import SIM_REGISTRY
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
L++ Event Sequence Simulator Commands:

  LOADING:
    load <path>       - Load blueprint for simulation
    unload            - Unload current blueprint

  SIMULATION:
    start             - Start simulation (init state)
    stop              - Stop simulation, return to ready
    reset             - Reset to initial state
    dispatch <event>  - Dispatch an event (or just type event name)
    set <key> <val>   - Set context value

  NAVIGATION:
    back              - Step back to previous state
    fork [name]       - Create a fork of current state
    switch <name>     - Switch to a named fork

  SEQUENCE:
    seq <e1,e2,...>   - Set event sequence
    run               - Run the event sequence

  EXPLORATION:
    fuzz [n]          - Random walk for n steps (default 10)
    path <state>      - Find path to target state
    explore [depth]   - Explore state space (BFS)

  VIEWING:
    status            - Show current status
    trace             - Show execution trace
    space             - Show explored state space
    events            - Show available events
    gates             - Evaluate all gates
    ctx               - Show full context

  TRACE:
    export [path]     - Export trace to JSON
    import <path>     - Import trace for replay

  OTHER:
    help              - Show this help
    quit              - Exit simulator
""")


def main():
    print("\n[L++ Event Sequence Simulator]")
    print("Type 'help' for commands\n")

    sim = compile_and_load(str(HERE / "event_simulator.json"), SIM_REGISTRY)

    # CLI arg for auto-load
    if len(sys.argv) > 1:
        sim.dispatch("LOAD", {"path": sys.argv[1]})
        if sim.state == "ready":
            sim.dispatch("START")

    ICONS = {
        "idle": "[.]",
        "ready": "[+]",
        "simulating": "[>]",
        "error": "[!]"
    }

    while True:
        icon = ICONS.get(sim.state, "[?]")
        sim_state = sim.context.get("sim_state", "-")
        mode = sim.context.get("mode", "")
        fork = sim.context.get("current_fork", "")

        prompt = f"{icon} {sim.state}"
        if sim.state == "simulating":
            prompt = f"{icon} {sim_state}"
            if mode:
                prompt += f" ({mode})"
            if fork:
                prompt += f" @{fork}"

        # Show output if any
        output = sim.context.get("output")
        if output:
            print(f"\n{output}")
            sim.set("output", None)

        # Show error if any
        error = sim.context.get("error")
        if error and sim.state != "error":
            print(f"\n[ERROR] {error}")
            sim.set("error", None)

        try:
            cmd = input(f"\n{prompt}> ").strip()
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        parts = cmd.split(maxsplit=1)
        action = parts[0].lower()
        arg = parts[1] if len(parts) > 1 else None

        # Parse commands
        if action in ("q", "quit", "exit"):
            break

        elif action == "help":
            print_help()

        elif action == "load" and arg:
            sim.dispatch("LOAD", {"path": arg})
            if sim.context.get("blueprint"):
                print(f"Loaded: {sim.context.get('blueprint_name')}")

        elif action == "self":
            sim.dispatch("LOAD", {"path": str(HERE / "event_simulator.json")})
            if sim.context.get("blueprint"):
                sim.dispatch("START")

        elif action == "viz":
            viz_path = HERE.parent / "visualizer" / "visualizer.json"
            sim.dispatch("LOAD", {"path": str(viz_path)})
            if sim.context.get("blueprint"):
                sim.dispatch("START")

        elif action == "unload":
            sim.dispatch("UNLOAD")

        elif action == "start":
            sim.dispatch("START")

        elif action == "stop":
            sim.dispatch("STOP")

        elif action == "reset":
            sim.dispatch("RESET")

        elif action == "dispatch" and arg:
            event_parts = arg.split(maxsplit=1)
            event_name = event_parts[0]
            payload = {}
            if len(event_parts) > 1:
                try:
                    payload = json.loads(event_parts[1])
                except json.JSONDecodeError:
                    payload = {"value": event_parts[1]}
            sim.dispatch("DISPATCH", {
                "event_name": event_name,
                "payload": payload
            })

        elif action == "set" and arg:
            set_parts = arg.split(maxsplit=1)
            if len(set_parts) >= 2:
                key = set_parts[0]
                try:
                    value = json.loads(set_parts[1])
                except json.JSONDecodeError:
                    value = set_parts[1]
                sim.dispatch("SET_CONTEXT", {"key": key, "value": value})
                print(f"Set {key} = {value}")

        elif action == "back":
            sim.dispatch("STEP_BACK")

        elif action == "fork":
            sim.dispatch("FORK", {"fork_name": arg})

        elif action == "switch" and arg:
            sim.dispatch("SWITCH_FORK", {"fork_name": arg})

        elif action == "seq" and arg:
            events = [e.strip() for e in arg.split(",")]
            sim.dispatch("SET_SEQUENCE", {"events": events})
            print(f"Sequence set: {events}")

        elif action == "run":
            sim.dispatch("RUN_SEQUENCE")

        elif action == "fuzz":
            steps = int(arg) if arg and arg.isdigit() else 10
            sim.dispatch("FUZZ", {"steps": steps})

        elif action == "path" and arg:
            sim.dispatch("FIND_PATH", {"target_state": arg})

        elif action == "explore":
            depth = int(arg) if arg and arg.isdigit() else 10
            sim.dispatch("EXPLORE", {"max_depth": depth})

        elif action == "status":
            sim.dispatch("REFRESH")

        elif action == "trace":
            sim.dispatch("VIEW_TRACE")

        elif action == "space":
            sim.dispatch("VIEW_SPACE")

        elif action == "events":
            avail = sim.context.get("available_events", [])
            trans = sim.context.get("available_transitions", [])
            print("\nAvailable Events:")
            for t in trans:
                gates = t.get("gates", [])
                gate_str = f" (gates: {gates})" if gates else ""
                print(f"  {t['event']}: {t['from']} -> {t['to']}{gate_str}")

        elif action == "gates":
            sim.dispatch("EVAL_GATES")

        elif action == "ctx":
            ctx = sim.context.get("sim_context", {})
            print("\nSimulation Context:")
            print(json.dumps(ctx, indent=2, default=str))

        elif action == "export":
            sim.dispatch("EXPORT", {"path": arg})

        elif action == "import" and arg:
            sim.dispatch("IMPORT", {"path": arg})

        elif action == "state":
            print("\nFull Operator Context:")
            print(json.dumps(sim.context, indent=2, default=str))

        # Direct event dispatch (if in simulating state)
        elif sim.state == "simulating":
            # Try to dispatch as event
            avail = sim.context.get("available_events", [])
            if action.upper() in avail:
                sim.dispatch("DISPATCH", {
                    "event_name": action.upper(),
                    "payload": {}
                })
            else:
                print(f"Unknown command or event: {action}")
                print(f"Available events: {avail}")

        else:
            print(f"Unknown command: {action}")
            print("Type 'help' for available commands")

    print("\nGoodbye!")


if __name__ == "__main__":
    main()
