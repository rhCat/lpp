#!/usr/bin/env python3
"""L++ Logic Decoder - Interactive CLI (< 50 lines per build_rules.md)"""
from src.decoder_compute import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint
from pathlib import Path
import importlib.util
import json
import os
import sys
sys.path.insert(0, "../../src")

HERE = Path(__file__).parent


def load():
    out = HERE / "results/logic_decoder_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "logic_decoder.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()}
    return mod.create_operator(reg)


def main():
    op = load()
    print(
        "LogicDecoder: decode <file.py> | show | export [file] | reset | quit")
    while True:
        try:
            cmd = input(f"[{op.state}]> ").strip()
        except (EOFError, KeyboardInterrupt):
            break
        if not cmd:
            continue
        parts = cmd.split(maxsplit=1)
        verb = parts[0].lower()
        arg = parts[1] if len(parts) > 1 else ""

        if verb == "quit":
            break
        elif verb == "decode":
            if not arg:
                print("Usage: decode <path/to/file.py>")
                continue
            fpath = os.path.abspath(arg)
            op.context["filePath"] = fpath
            op.dispatch("DECODE", {})
            op.dispatch("AUTO", {})
            op.dispatch("AUTO", {})
            op.dispatch("AUTO", {})
            op.dispatch("AUTO", {})
            report = op.context.get("analysisReport", {})
            if report:
                print(f"Decoded: {report.get('statesCount', 0)} states, "
                      f"{report.get('transitionsCount', 0)} transitions")
                print(f"Imports: {report.get('importCategories', [])}")
            if op.context.get("error"):
                print(f"Error: {op.context['error']}")
        elif verb == "show":
            bp = op.context.get("blueprint")
            if bp:
                print(json.dumps(bp, indent=2))
            else:
                print("No blueprint. Run 'decode <file>' first.")
        elif verb == "export":
            bpJson = op.context.get("blueprintJson")
            if not bpJson:
                print("No blueprint to export.")
                continue
            outPath = arg if arg else "decoded_blueprint.json"
            with open(outPath, "w") as f:
                f.write(bpJson)
            print(f"Exported to: {outPath}")
        elif verb == "reset":
            op.dispatch("RESET", {})
            print("Reset complete.")
        else:
            print(
                "Commands: decode <file> | show | export [file] | reset | quit")


if __name__ == "__main__":
    main()
