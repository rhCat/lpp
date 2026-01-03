#!/usr/bin/env python3
"""L++ Legacy Code Extractor - Interactive CLI (< 50 lines per build_rules.md)"""
from src.extractor_compute import EXTRACT_REGISTRY
from pathlib import Path
import importlib.util
import json
import os
import sys
sys.path.insert(0, "../../src")
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent


def load():
    out = HERE / "results/legacy_extractor_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "legacy_extractor.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in EXTRACT_REGISTRY.items()}
    return mod.create_operator(reg)


def main():
    op = load()
    print("LegacyExtractor: extract <file.py> | mode <mode> | show | export "
          "<path> | report <path> | reset | quit")
    print("Modes: heuristic (default), annotated, log, hybrid")
    while True:
        try:
            cmd = input(f"[{op.state}]> ").strip()
        except (EOFError, KeyboardInterrupt):
            break
        if not cmd:
            continue
        parts = cmd.split(maxsplit=1)
        verb, arg = parts[0].lower(), parts[1] if len(parts) > 1 else ""

        if verb == "quit":
            break
        elif verb == "mode":
            if arg in ("heuristic", "annotated", "log", "hybrid"):
                op.dispatch("SET_MODE", {"mode": arg})
                print(f"Mode set to: {arg}")
            else:
                print("Modes: heuristic, annotated, log, hybrid")
        elif verb == "extract":
            if not arg:
                print("Usage: extract <path/to/file.py>")
                continue
            op.context["filePath"] = os.path.abspath(arg)
            op.context["analysisMode"] = op.context.get("analysisMode") or \
                "heuristic"
            op.dispatch("EXTRACT", {})
            for _ in range(12):
                op.dispatch("AUTO", {})
            r = op.context.get("extractionReport", {})
            if r:
                s = r.get("extraction_summary", {})
                print(f"Extracted: {s.get('states_extracted', 0)} states, "
                      f"{s.get('transitions_extracted', 0)} transitions")
            if op.context.get("error"):
                print(f"Error: {op.context['error']}")
        elif verb == "show":
            bp = op.context.get("blueprint")
            print(json.dumps(bp, indent=2) if bp else "No blueprint yet.")
        elif verb == "export":
            op.dispatch("EXPORT_BLUEPRINT", {"outputPath": arg or "out.json"})
            print(f"Exported to: {arg or 'out.json'}")
        elif verb == "report":
            op.dispatch("EXPORT_REPORT", {"outputPath": arg or "report.json"})
            print(f"Report exported to: {arg or 'report.json'}")
        elif verb == "reset":
            op.dispatch("RESET", {})
            print("Reset complete.")
        else:
            print("Commands: extract <file> | mode <m> | show | export | reset")


if __name__ == "__main__":
    main()
