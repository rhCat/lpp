#!/usr/bin/env python3
"""
L++ Task Orchestrator - Minimal Extrusion Layer
Per build_rules.md: < 50 lines, thin dispatch wrapper only.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "src"))

from src import ORCH_REGISTRY  # noqa: E402
from frame_py.compiler import compile_blueprint  # noqa: E402

HERE = Path(__file__).parent


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with COMPUTE registry."""
    import importlib.util
    out = HERE / "results" / f"{Path(blueprint_json).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint_json, str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


def main():
    """Thin CLI for task orchestrator."""
    op = compile_and_load(str(HERE / "task_orchestrator.json"), ORCH_REGISTRY)
    op.dispatch("START", {})
    print(f"State: {op.state} | Ready for tasks")

    while True:
        try:
            cmd = input("\n> ").strip()
            if not cmd:
                continue
            if cmd.lower() in ("quit", "exit", "q"):
                break
            if cmd.lower() == "status":
                ctx = op.context
                print(f"State: {op.state} | Iter: {ctx.get('iteration')}")
                continue
            # Treat input as task
            op.dispatch("SUBMIT", {"task": cmd})
            op.dispatch("DONE", {})
            while op.state not in ("complete", "error", "idle"):
                print(f"  [{op.state}]...")
                op.dispatch("DONE", {})
            print(f"\nResult: {op.context.get('evaluation')}")
        except (KeyboardInterrupt, EOFError):
            break
    print("\nDone.")


if __name__ == "__main__":
    main()
