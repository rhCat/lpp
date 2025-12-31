#!/usr/bin/env python3
"""TLAPS Seal Certifier - Interactive CLI (< 50 lines per build_rules.md)"""
from src.seal_compute import COMPUTE_REGISTRY
from pathlib import Path
import importlib.util
import json
import sys
sys.path.insert(0, "../../src")
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent


def load():
    out = HERE / "results/tlaps_seal_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(str(HERE / "tlaps_seal.json"), str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()}
    return mod.create_operator(reg)


def main():
    op = load()
    print("TLAPS Seal: certify <bp.json> | prove | seal | view | reset | quit")
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
        elif verb == "certify":
            if not arg:
                print("Usage: certify <path/to/blueprint.json>")
                continue
            op.dispatch("CERTIFY", {"path": arg})
            for _ in range(5):
                op.dispatch("AUTO", {})
            _showStatus(op)
        elif verb == "prove":
            op.dispatch("PROVE", {})
            op.dispatch("AUTO", {})
            _showStatus(op)
        elif verb == "seal":
            op.dispatch("SEAL_TLC", {})
            _showStatus(op)
        elif verb == "view":
            cert = op.context.get("sealCertificate")
            print(json.dumps(cert, indent=2) if cert else "No certificate")
        elif verb == "reset":
            op.dispatch("RESET", {})
            print("Reset to idle")
        else:
            print("Commands: certify, prove, seal, view, reset, quit")


def _showStatus(op):
    if op.context.get("error"):
        print(f"Error: {op.context['error']}")
    cert = op.context.get("sealCertificate")
    if cert:
        print(f"Seal: {cert.get('seal')} | Level: {cert.get('level')}")


if __name__ == "__main__":
    main()
