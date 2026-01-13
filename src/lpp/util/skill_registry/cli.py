#!/usr/bin/env python3
"""Skill Registry CLI - per build_rules.md: < 50 lines."""
from src.registry_compute import COMPUTE_REGISTRY, formatContext
from frame_py.compiler import compile_blueprint
from pathlib import Path
import sys
sys.path.insert(0, "../../src")
HERE = Path(__file__).parent


def load():
    import importlib.util
    out = HERE / "results/skill_registry_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "skill_registry.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.create_operator({tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()})


def main():
    op, base = load(), str(HERE.parent)
    print(
        "SkillRegistry: scan [path] | list | view <id> | export | context | quit")
    while True:
        try:
            line = input(f"[{op.state}]> ").strip()
        except (EOFError, KeyboardInterrupt):
            break
        if not line:
            continue
        parts = line.split(maxsplit=1)
        cmd, arg = parts[0].lower(), parts[1] if len(parts) > 1 else ""
        if cmd == "quit":
            break
        elif cmd == "scan":
            op.dispatch("SCAN", {"path": arg or base})
            for s in (op.context.get("skills") or []):
                print(
                    f"  [{s['id']}] {s['name']} v{s['version']} ({s['stateCount']}S/{s['transitionCount']}T)")
        elif cmd == "list":
            for s in (op.context.get("skills") or []):
                print(f"  {s['id']}: {s['description'][:50]}")
        elif cmd == "view":
            op.dispatch("SELECT", {"skillId": arg})
            sk = op.context.get("selectedSkill")
            if sk:
                print(
                    f"  {sk['name']}: {sk['states']}\n  Flange: {sk['flangeSpec']}")
        elif cmd == "export":
            op.dispatch("EXPORT", {})
            reg = op.context.get("registry")
            if reg:
                print(f"  Exported {len(reg.get('skills', {}))} skills")
        elif cmd == "context":
            reg = op.context.get("registry")
            if reg:
                md = formatContext({"registry": reg}).get("markdown", "")
                print(md[:2000])
        elif cmd == "back":
            op.dispatch("BACK", {})


if __name__ == "__main__":
    main()
