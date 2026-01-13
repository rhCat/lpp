#!/usr/bin/env python3
"""
L++ LLM Schema Assistant - Minimal Extrusion Layer
Per build_rules.md: < 50 lines, thin dispatch wrapper only.
"""
import sys
from pathlib import Path
from src import LLM_REGISTRY
from frame_py.compiler import compile_blueprint

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
    """Thin CLI - delegates all logic to COMPUTE units."""
    from src.llm_cli import run_cli
    try:
        op = compile_and_load(str(HERE / "llm_assistant.json"), LLM_REGISTRY)
        run_cli(op, HERE)
    except Exception as e:
        print(f"❌ Failed: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
