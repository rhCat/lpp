#!/usr/bin/env python3
"""
L++ Blueprint Composer - Interactive Shell

A minimal CLI that drives compiled L++ operators for blueprint composition.
All logic lives in blueprints + COMPUTE units. This is just a thin caller.
"""

import sys
import json
from pathlib import Path
from src import COMPOSE_REGISTRY
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with given COMPUTE registry."""
    import importlib.util

    out = HERE / "results" / f"{Path(blueprint_json).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint_json, str(out))

    # Load compiled operator
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    # Convert "ns:name" -> (ns, name)
    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


def main():
    print("\n  L++ Blueprint Composer\n")

    # Load compiled composer operator
    composer = compile_and_load(
        str(HERE / "blueprint_composer.json"), COMPOSE_REGISTRY
    )

    # CLI arg - load manifest and compose
    if len(sys.argv) > 1:
        arg = sys.argv[1]
        if arg.endswith(".json"):
            # Check if it's a manifest or a parent blueprint
            with open(arg) as f:
                data = json.load(f)
            if "embeddings" in data:
                # It's a manifest
                composer.dispatch("LOAD_MANIFEST", {"path": arg})
            else:
                # It's a parent blueprint
                composer.dispatch("LOAD_PARENT", {"path": arg})

    ICONS = {
        "idle": "[.]",
        "parent_loaded": "[P]",
        "child_loaded": "[PC]",
        "defining_embedding": "[~]",
        "embedding_ready": "[E]",
        "composed": "[C]",
        "validated": "[V]",
        "error": "[!]"
    }

    while True:
        ctx = composer.context

        # Status line
        parentName = ctx.get("parent_blueprint", {}).get("name", "none")
        childName = ctx.get("child_blueprint", {}).get("name", "none")
        embCount = len(ctx.get("embeddings") or [])

        if composer.state == "composed":
            composedName = ctx.get("composed_blueprint", {}).get("name", "?")
            status = f"Composed: {composedName}"
        elif composer.state == "validated":
            result = ctx.get("validation_result", {})
            errC = len(result.get("errors", []))
            warnC = len(result.get("warnings", []))
            status = f"E:{errC} W:{warnC}"
        else:
            status = f"P:{parentName[:20]} | C:{childName[:15]} | E:{embCount}"

        icon = ICONS.get(composer.state, '[?]')
        print(f"\n  {icon} {composer.state} | {status}")

        # Show validation results if available
        if composer.state == "validated":
            result = ctx.get("validation_result", {})
            if result.get("errors"):
                print("\n  Errors:")
                for err in result["errors"]:
                    print(f"    [E] {err}")
            if result.get("warnings"):
                print("\n  Warnings:")
                for warn in result["warnings"]:
                    print(f"    [W] {warn}")
            if result.get("valid"):
                print("\n  Composition is valid!")

        # Show export path if available
        if ctx.get("export_path"):
            print(f"\n  Exported: {ctx['export_path']}")

        # Show error if any
        if ctx.get("error"):
            print(f"\n  Error: {ctx['error']}")

        try:
            cmd = input("\n> ").strip().split(maxsplit=1)
        except (EOFError, KeyboardInterrupt):
            break

        if not cmd:
            continue

        action, arg = cmd[0].lower(), cmd[1] if len(cmd) > 1 else None

        # Command dispatch
        if action in ("q", "quit", "exit"):
            break
        elif action == "help":
            print_help()
        elif action == "parent" and arg:
            composer.dispatch("LOAD_PARENT", {"path": arg})
        elif action == "child" and arg:
            composer.dispatch("LOAD_CHILD", {"path": arg})
        elif action == "manifest" and arg:
            composer.dispatch("LOAD_MANIFEST", {"path": arg})
        elif action == "define":
            targetState = arg if arg else "processing"
            composer.dispatch("DEFINE", {"target_state": targetState})
        elif action == "input" and arg:
            # Parse input_map from JSON string
            try:
                inputMap = json.loads(arg)
                composer.dispatch("SET_INPUT", {"input_map": inputMap})
            except json.JSONDecodeError:
                print("  Invalid JSON for input_map")
        elif action == "output" and arg:
            try:
                outputMap = json.loads(arg)
                composer.dispatch("SET_OUTPUT", {"output_map": outputMap})
            except json.JSONDecodeError:
                print("  Invalid JSON for output_map")
        elif action == "events" and arg:
            try:
                eventMap = json.loads(arg)
                composer.dispatch("SET_EVENTS", {"event_map": eventMap})
            except json.JSONDecodeError:
                print("  Invalid JSON for event_map")
        elif action == "done":
            composer.dispatch("DONE")
        elif action == "compose":
            composer.dispatch("COMPOSE")
        elif action == "quick" and arg:
            # Quick compose: define target state and compose in one step
            composer.dispatch("QUICK_COMPOSE", {"target_state": arg})
        elif action == "validate":
            composer.dispatch("VALIDATE")
        elif action == "flatten":
            composer.dispatch("FLATTEN")
        elif action == "export" and arg:
            composer.dispatch("EXPORT", {"path": arg})
        elif action == "savemanifest" and arg:
            composer.dispatch("SAVE_MANIFEST", {"path": arg})
        elif action == "addmore":
            composer.dispatch("ADD_MORE")
        elif action == "back":
            composer.dispatch("BACK")
        elif action == "cancel":
            composer.dispatch("CANCEL")
        elif action == "reset":
            composer.dispatch("RESET")
        elif action == "clear":
            composer.dispatch("CLEAR")
        elif action == "state":
            print(json.dumps(ctx, indent=2, default=str))
        elif action == "embeddings":
            embeddings = ctx.get("embeddings", [])
            if embeddings:
                print("\n  Embeddings:")
                for i, emb in enumerate(embeddings):
                    target = emb.get("target_state", "?")
                    childPath = emb.get("child_path", "?")
                    print(f"    {i+1}. {target} <- {Path(childPath).name}")
            else:
                print("  No embeddings defined.")
        elif action == "composed":
            bp = ctx.get("composed_blueprint")
            if bp:
                print(json.dumps(bp, indent=2))
            else:
                print("  No composed blueprint.")
        elif action == "test":
            run_test_composition(composer)
        else:
            print(f"  Unknown command: {action}")
            print("  Type 'help' for available commands.")

    print("  Goodbye!")


def print_help():
    """Print help message."""
    print("""
  L++ Blueprint Composer Commands:

  Loading:
    parent <path>      - Load parent blueprint
    child <path>       - Load child blueprint to embed
    manifest <path>    - Load composition manifest

  Defining Embeddings:
    define [state]     - Start defining embedding for target state
    input <json>       - Set input contract: {"parent.prop": "child.prop"}
    output <json>      - Set output contract: {"child.prop": "parent.prop"}
    events <json>      - Set event mapping: {"PARENT_EV": "CHILD_EV"}
    done               - Finalize current embedding

  Composition:
    compose            - Execute composition
    quick <state>      - Quick compose with default settings
    validate           - Validate composed blueprint
    flatten            - Flatten nested compositions

  Export:
    export <path>      - Export composed blueprint to file
    savemanifest <p>   - Save composition manifest

  Navigation:
    addmore            - Add another embedding
    back               - Go back one step
    cancel             - Cancel current embedding
    reset              - Reset to idle
    clear              - Clear all state

  Inspection:
    state              - Show full context state
    embeddings         - Show defined embeddings
    composed           - Show composed blueprint JSON

  Testing:
    test               - Run test composition with sample blueprints

  Other:
    help               - Show this help
    quit               - Exit
    """)


def run_test_composition(composer):
    """Run a test composition using sample blueprints."""
    testsDir = HERE / "tests"
    parentPath = testsDir / "parent_workflow.json"
    childPath = testsDir / "child_processor.json"

    if not parentPath.exists() or not childPath.exists():
        print("  Test blueprints not found. Creating samples...")
        create_test_blueprints(testsDir)

    # Load and compose
    composer.dispatch("CLEAR")
    composer.dispatch("LOAD_PARENT", {"path": str(parentPath)})
    composer.dispatch("LOAD_CHILD", {"path": str(childPath)})
    composer.dispatch("DEFINE", {"target_state": "processing"})
    composer.dispatch("SET_INPUT", {
        "input_map": {"input_data": "process_input"}
    })
    composer.dispatch("SET_OUTPUT", {
        "output_map": {"process_result": "output_data"}
    })
    composer.dispatch("SET_EVENTS", {
        "event_map": {"PROCESS": "START", "DONE": "COMPLETE"}
    })
    composer.dispatch("DONE")
    composer.dispatch("COMPOSE")
    composer.dispatch("VALIDATE")

    print("\n  Test composition complete!")


def create_test_blueprints(testsDir: Path):
    """Create test blueprints for demonstration."""
    testsDir.mkdir(exist_ok=True)

    # Parent workflow - a simple workflow with a placeholder processing state
    parent = {
        "$schema": "lpp/v0.1.2",
        "id": "parent_workflow",
        "name": "Parent Workflow",
        "version": "1.0.0",
        "description": "A workflow with a placeholder processing state",
        "context_schema": {
            "properties": {
                "input_data": {"type": "object"},
                "output_data": {"type": "object"},
                "status": {"type": "string"}
            }
        },
        "states": {
            "idle": {"description": "Waiting for input"},
            "processing": {"description": "Placeholder for processing logic"},
            "complete": {"description": "Processing complete"},
            "error": {"description": "Error state"}
        },
        "entry_state": "idle",
        "terminal_states": [],
        "gates": {
            "has_input": {
                "type": "expression",
                "expression": "input_data is not None"
            }
        },
        "actions": {
            "set_status_processing": {
                "type": "set",
                "target": "status",
                "value": "processing"
            },
            "set_status_complete": {
                "type": "set",
                "target": "status",
                "value": "complete"
            }
        },
        "transitions": [
            {
                "id": "t_start",
                "from": "idle",
                "to": "processing",
                "on_event": "START",
                "gates": ["has_input"],
                "actions": ["set_status_processing"]
            },
            {
                "id": "t_done",
                "from": "processing",
                "to": "complete",
                "on_event": "DONE",
                "actions": ["set_status_complete"]
            },
            {
                "id": "t_error",
                "from": "processing",
                "to": "error",
                "on_event": "ERROR"
            },
            {
                "id": "t_reset",
                "from": "complete",
                "to": "idle",
                "on_event": "RESET"
            }
        ]
    }

    # Child processor - specific processing logic to embed
    child = {
        "$schema": "lpp/v0.1.2",
        "id": "child_processor",
        "name": "Child Processor",
        "version": "1.0.0",
        "description": "A specific processing implementation",
        "context_schema": {
            "properties": {
                "process_input": {"type": "object"},
                "process_result": {"type": "object"},
                "step": {"type": "number"}
            }
        },
        "states": {
            "init": {"description": "Initialize processing"},
            "step1": {"description": "First processing step"},
            "step2": {"description": "Second processing step"},
            "done": {"description": "Processing complete"}
        },
        "entry_state": "init",
        "terminal_states": ["done"],
        "gates": {
            "has_process_input": {
                "type": "expression",
                "expression": "process_input is not None"
            },
            "step_complete": {
                "type": "expression",
                "expression": "step >= 2"
            }
        },
        "actions": {
            "init_step": {
                "type": "set",
                "target": "step",
                "value": 0
            },
            "increment_step": {
                "type": "compute",
                "compute_unit": "process:increment",
                "input_map": {"current": "step"},
                "output_map": {"step": "next"}
            },
            "compute_result": {
                "type": "compute",
                "compute_unit": "process:compute",
                "input_map": {"data": "process_input"},
                "output_map": {"process_result": "result"}
            }
        },
        "transitions": [
            {
                "id": "t_init",
                "from": "init",
                "to": "step1",
                "on_event": "START",
                "actions": ["init_step"]
            },
            {
                "id": "t_step1_to_2",
                "from": "step1",
                "to": "step2",
                "on_event": "NEXT",
                "actions": ["increment_step"]
            },
            {
                "id": "t_step2_to_done",
                "from": "step2",
                "to": "done",
                "on_event": "NEXT",
                "gates": ["step_complete"],
                "actions": ["increment_step", "compute_result"]
            },
            {
                "id": "t_complete",
                "from": "done",
                "to": "done",
                "on_event": "COMPLETE"
            }
        ]
    }

    with open(testsDir / "parent_workflow.json", "w") as f:
        json.dump(parent, f, indent=2)

    with open(testsDir / "child_processor.json", "w") as f:
        json.dump(child, f, indent=2)

    # Also create a sample manifest
    manifest = {
        "parent": "parent_workflow.json",
        "embeddings": [
            {
                "target_state": "processing",
                "child": "child_processor.json",
                "contract": {
                    "input_map": {"input_data": "process_input"},
                    "output_map": {"process_result": "output_data"}
                },
                "event_map": {"PROCESS": "START", "DONE": "COMPLETE"}
            }
        ]
    }

    with open(testsDir / "composition_manifest.json", "w") as f:
        json.dump(manifest, f, indent=2)

    print(f"  Created test blueprints in {testsDir}")


if __name__ == "__main__":
    main()
