#!/usr/bin/env python3
"""
L++ Execution Tracer - Interactive Shell

Structured logging and tracing for L++ blueprint execution with
OpenTelemetry-compatible output formats.
"""

import sys
import json
from pathlib import Path

# Import from src package
from src import TRACER_REGISTRY
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
L++ Execution Tracer Commands:

  INITIALIZATION:
    init [format]     - Initialize tracer (otlp, jsonl, human, timeline)
    reset             - Reset tracer to idle state

  TRACE LIFECYCLE:
    start <name> [id] - Start tracing a blueprint
    end               - End current trace
    pause             - Pause tracing
    resume            - Resume tracing
    clear             - Clear trace data

  RECORDING:
    state <from> <to> [event] [transition_id]
                      - Record state transition
    gate <id> <pass/fail> [expr]
                      - Record gate evaluation
    action <id> <type> [duration_ms]
                      - Record action execution
    event <name> [payload_json]
                      - Record event dispatch
    ctx <key> <old> <new>
                      - Record context change

  SPANS:
    span <name> <type> [duration_ms]
                      - Record a complete span
    sstart <name> <type>
                      - Start a timed span
    send [span_id]    - End active span

  OUTPUT:
    format <type>     - Set output format (otlp, jsonl, human, timeline)
    otlp              - Format as OpenTelemetry JSON
    jsonl             - Format as JSON Lines
    human             - Format as human-readable text
    timeline          - Format as ASCII timeline

  EXPORT & ANALYSIS:
    export [path]     - Export trace to file
    analyze           - Analyze trace for insights

  OTHER:
    status            - Show current status
    show              - Show formatted output
    spans             - List all spans
    events            - List all events
    help              - Show this help
    quit              - Exit tracer

  DEMO:
    demo              - Run a demonstration trace
""")


def run_demo(tracer):
    """Run a demonstration trace."""
    print("\n[Running demonstration trace...]\n")

    # Start trace
    tracer.dispatch("START_TRACE", {
        "blueprint_id": "demo_workflow",
        "blueprint_name": "Demo Workflow",
        "metadata": {"version": "1.0.0"}
    })

    # Simulate some execution
    tracer.dispatch("STATE_CHANGE", {
        "from_state": "idle",
        "to_state": "processing",
        "transition_id": "t_start",
        "trigger_event": "START"
    })

    tracer.dispatch("GATE_EVAL", {
        "gate_id": "has_data",
        "expression": "data is not None",
        "result": True,
        "input_values": {"data": "sample"}
    })

    tracer.dispatch("ACTION", {
        "action_id": "process_data",
        "action_type": "compute",
        "input_map": {"data": "data"},
        "output_map": {"result": "result"},
        "duration_ms": 45.5
    })

    tracer.dispatch("CONTEXT_CHANGE", {
        "key": "result",
        "old_value": None,
        "new_value": {"processed": True}
    })

    tracer.dispatch("STATE_CHANGE", {
        "from_state": "processing",
        "to_state": "validating",
        "transition_id": "t_validate",
        "trigger_event": "PROCESSED"
    })

    tracer.dispatch("GATE_EVAL", {
        "gate_id": "is_valid",
        "expression": "result.get('processed') == True",
        "result": True,
        "input_values": {"result": {"processed": True}}
    })

    tracer.dispatch("ACTION", {
        "action_id": "validate_result",
        "action_type": "compute",
        "duration_ms": 12.3
    })

    tracer.dispatch("STATE_CHANGE", {
        "from_state": "validating",
        "to_state": "completed",
        "transition_id": "t_complete",
        "trigger_event": "VALIDATED"
    })

    tracer.dispatch("EVENT", {
        "event_name": "WORKFLOW_COMPLETED",
        "event_payload": {"success": True}
    })

    # End trace
    tracer.dispatch("END_TRACE")

    print("[Demo trace completed]")
    print("Use 'human', 'timeline', 'otlp', or 'jsonl' to view the trace\n")


def main():
    print("\n[L++ Execution Tracer]")
    print("Type 'help' for commands\n")

    tracer = compile_and_load(
        str(HERE / "execution_tracer.json"),
        TRACER_REGISTRY
    )

    ICONS = {
        "idle": "[.]",
        "configured": "[+]",
        "tracing": "[>]",
        "paused": "[||]",
        "completed": "[*]",
        "analyzing": "[?]",
        "exporting": "[^]",
        "error": "[!]"
    }

    while True:
        icon = ICONS.get(tracer.state, "[?]")
        trace_id = tracer.context.get("trace_id")
        bp_name = tracer.context.get("blueprint_name")

        prompt = f"{icon} {tracer.state}"
        if trace_id:
            short_id = trace_id[:8]
            if bp_name:
                prompt = f"{icon} {bp_name} [{short_id}]"
            else:
                prompt = f"{icon} {short_id}"

        # Show output if any
        output = tracer.context.get("output")
        if output:
            print(f"\n{output}")
            tracer.set("output", None)

        # Show error if any
        error = tracer.context.get("error")
        if error and tracer.state != "error":
            print(f"\n[ERROR] {error}")
            tracer.set("error", None)

        try:
            cmd = input(f"\n{prompt}> ").strip()
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        parts = cmd.split(maxsplit=4)
        action = parts[0].lower()
        args = parts[1:] if len(parts) > 1 else []

        # Parse commands
        if action in ("q", "quit", "exit"):
            break

        elif action == "help":
            print_help()

        elif action == "init":
            fmt = args[0] if args else "human"
            tracer.dispatch("INIT", {"output_format": fmt})

        elif action == "reset":
            tracer.dispatch("RESET")

        elif action == "start":
            name = args[0] if args else "Unnamed Blueprint"
            bp_id = args[1] if len(args) > 1 else None
            tracer.dispatch("START_TRACE", {
                "blueprint_name": name,
                "blueprint_id": bp_id or name.lower().replace(" ", "_")
            })

        elif action == "end":
            tracer.dispatch("END_TRACE")

        elif action == "pause":
            tracer.dispatch("PAUSE")

        elif action == "resume":
            tracer.dispatch("RESUME")

        elif action == "clear":
            tracer.dispatch("CLEAR")

        elif action == "state" and len(args) >= 2:
            tracer.dispatch("STATE_CHANGE", {
                "from_state": args[0],
                "to_state": args[1],
                "trigger_event": args[2] if len(args) > 2 else None,
                "transition_id": args[3] if len(args) > 3 else None
            })

        elif action == "gate" and len(args) >= 2:
            result = args[1].lower() in ("pass", "true", "1", "yes")
            tracer.dispatch("GATE_EVAL", {
                "gate_id": args[0],
                "result": result,
                "expression": args[2] if len(args) > 2 else None
            })

        elif action == "action" and len(args) >= 2:
            dur = float(args[2]) if len(args) > 2 else 0
            tracer.dispatch("ACTION", {
                "action_id": args[0],
                "action_type": args[1],
                "duration_ms": dur
            })

        elif action == "event" and args:
            payload = {}
            if len(args) > 1:
                try:
                    payload = json.loads(args[1])
                except json.JSONDecodeError:
                    payload = {"value": args[1]}
            tracer.dispatch("EVENT", {
                "event_name": args[0],
                "event_payload": payload
            })

        elif action == "ctx" and len(args) >= 3:
            tracer.dispatch("CONTEXT_CHANGE", {
                "key": args[0],
                "old_value": args[1],
                "new_value": args[2]
            })

        elif action == "span" and len(args) >= 2:
            dur = float(args[2]) if len(args) > 2 else 0
            tracer.dispatch("RECORD_SPAN", {
                "name": args[0],
                "span_type": args[1],
                "duration_ms": dur
            })

        elif action == "sstart" and len(args) >= 2:
            tracer.dispatch("START_SPAN", {
                "name": args[0],
                "span_type": args[1]
            })

        elif action == "send":
            span_id = args[0] if args else None
            tracer.dispatch("END_SPAN", {"span_id": span_id})

        elif action == "format" and args:
            tracer.dispatch("SET_FORMAT", {"format": args[0]})
            print(f"Output format set to: {args[0]}")

        elif action == "otlp":
            tracer.dispatch("FORMAT_OTLP")

        elif action == "jsonl":
            tracer.dispatch("FORMAT_JSONL")

        elif action == "human":
            tracer.dispatch("FORMAT_HUMAN")

        elif action == "timeline":
            tracer.dispatch("FORMAT_TIMELINE")

        elif action == "export":
            path = args[0] if args else None
            tracer.dispatch("EXPORT", {"path": path})

        elif action == "analyze":
            tracer.dispatch("ANALYZE")

        elif action == "status":
            tracer.dispatch("STATUS")

        elif action == "show":
            formatted = tracer.context.get("formatted_output")
            if formatted:
                print(f"\n{formatted}")
            else:
                print("No formatted output. Use otlp/jsonl/human/timeline.")

        elif action == "spans":
            spans = tracer.context.get("spans") or []
            if not spans:
                print("No spans recorded")
            else:
                print(f"\nSpans ({len(spans)}):")
                print("-" * 60)
                for s in spans[:20]:
                    name = s.get("name", "unknown")[:30]
                    stype = s.get("span_type", "?")[:10]
                    dur = s.get("duration_ms", 0) or 0
                    print(f"  [{stype:10}] {name:30} {dur:8.2f}ms")
                if len(spans) > 20:
                    print(f"  ... and {len(spans) - 20} more")

        elif action == "events":
            events = tracer.context.get("events") or []
            if not events:
                print("No events recorded")
            else:
                print(f"\nEvents ({len(events)}):")
                print("-" * 60)
                for e in events[:20]:
                    ts = e.get("timestamp", "")
                    if ts:
                        ts = ts.split("T")[1][:12]
                    etype = e.get("type", "unknown")[:15]
                    attrs = e.get("attributes", {})
                    summary = str(attrs)[:40]
                    print(f"  [{ts}] {etype:15} {summary}")
                if len(events) > 20:
                    print(f"  ... and {len(events) - 20} more")

        elif action == "demo":
            run_demo(tracer)

        elif action == "full":
            # Debug: show full context
            print("\nFull Context:")
            ctx = dict(tracer.context)
            # Truncate large fields
            for k in ["spans", "events", "formatted_output"]:
                if k in ctx and ctx[k]:
                    if isinstance(ctx[k], list):
                        ctx[k] = f"[{len(ctx[k])} items]"
                    elif isinstance(ctx[k], str) and len(ctx[k]) > 100:
                        ctx[k] = ctx[k][:100] + "..."
            print(json.dumps(ctx, indent=2, default=str))

        else:
            print(f"Unknown command: {action}")
            print("Type 'help' for available commands")

    print("\nGoodbye!")


if __name__ == "__main__":
    main()
