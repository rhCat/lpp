#!/usr/bin/env python3
"""
Discovery Shopping - Interactive CLI

Fit-first product discovery with explainable matching.
"""

import sys
import json
import importlib.util
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent / "src"))

from frame_py.compiler import compile_blueprint  # noqa: E402
from src import COMPUTE_REGISTRY  # noqa: E402

HERE = Path(__file__).parent


def compile_and_load(blueprint_json: str, registry: dict):
    """Compile blueprint and return operator with COMPUTE registry."""
    out = HERE / "results" / f"{Path(blueprint_json).stem}_compiled.py"
    out.parent.mkdir(exist_ok=True)
    compile_blueprint(blueprint_json, str(out))
    spec = importlib.util.spec_from_file_location("op", out)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    reg = {tuple(k.split(":")): fn for k, fn in registry.items()}
    return mod.create_operator(reg)


def main():
    blueprint = str(HERE / "discovery_shopping.json")
    op = compile_and_load(blueprint, COMPUTE_REGISTRY)

    print("\n🛒 Discovery Shopping - Fit-First Product Discovery")
    print("=" * 50)
    print("Commands: <event> [args] | state | ctx | quit\n")

    while True:
        state = op.state
        prompt = f"[{state}] > "
        try:
            line = input(prompt).strip()
        except (EOFError, KeyboardInterrupt):
            print("\nGoodbye!")
            break

        if not line:
            continue
        if line == "quit":
            break
        if line == "state":
            print(f"Current state: {op.state}")
            continue
        if line == "ctx":
            print(json.dumps(op.context, indent=2, default=str))
            continue

        parts = line.split(maxsplit=1)
        event = parts[0].upper()
        payload = {}

        if len(parts) > 1:
            try:
                payload = json.loads(parts[1])
            except json.JSONDecodeError:
                payload = {"value": parts[1]}

        result = op.dispatch(event, payload)
        success, new_state, error = result
        if success:
            print(f"→ {op.state}")
            # Show relevant context based on state
            _show_state_info(op)
        if error:
            print(f"Error: {error}")


def _show_state_info(op):
    """Show relevant information based on current state."""
    ctx = op.context
    state = op.state

    if state == "quizzing" and ctx.get("quiz_questions"):
        print("\n📋 Quiz Questions:")
        for q in ctx["quiz_questions"]:
            print(f"  {q['id']}: {q['text']}")
            print(f"      Options: {', '.join(q['options'])}")
        print(
            "\n  Answer with: ANSWER {{\"question_id\": "
            "\"q1\", \"answer\": \"Music\"}}"
        )
        print("  Or: SKIP_QUIZ to skip")

    elif state == "fetching" and ctx.get("products"):
        print(f"\n📦 Found {len(ctx['products'])} products")
        print("  Continue with: DONE")

    elif state == "analyzing":
        print("\n🔍 Aggregating review insights...")
        print("  Continue with: DONE")

    elif state == "ranking":
        print("\n🎯 Computing rankings...")
        print("  Continue with: DONE")

    elif state == "browsing" and ctx.get("rankings"):
        print("\n🏆 Product Rankings:")
        for i, r in enumerate(ctx["rankings"][:5], 1):
            print(f"  {i}. {r['product_name']} (${r['price']:.2f})")
            print(f"     Score: {r['score']:.2f} | Rating: {r['rating']}/5")
            print(f"     Why: {'; '.join(r['reasons'][:2])}")
        print("\n  VIEW {\"product_id\": \"hp001\"} - View details")
        print("  COMPARE {\"product_ids\": [\"hp001\", \"hp002\"]} - Compare")

    elif state == "comparing" and ctx.get("comparison"):
        comp = ctx["comparison"]
        print("\n⚖️ Side-by-Side Comparison:")
        for dim in comp.get("dimensions", [])[:4]:
            print(f"\n  {dim}:")
            for p in comp.get("products", []):
                winner = "✓" if comp.get(
                    "winners", {}
                ).get(dim) == p["id"] else " "
                print(
                    f"    {winner} {p['name']}: "
                    f"{p['values'].get(dim, 'N/A')}"
                )
        print("\n  BACK to return to browsing")

    elif state == "detail" and ctx.get("selected_product"):
        pid = ctx["selected_product"]
        print(f"\n📱 Viewing: {pid}")
        if ctx.get("affiliate_links"):
            link = ctx["affiliate_links"].get(pid, "")
            print(f"  Affiliate link: {link}")
        print(
            "\n  SET_ALERT {\"product_id\": \""
            + pid +
            "\", \"alert_type\": \"price\"}"
        )
        print("  COMPARE {\"product_ids\": [\"" + pid + "\", \"hp002\"]}")
        print("  BACK to return")

    elif state == "alerting":
        print("\n🔔 Setting alert...")
        print("  CONFIRM to subscribe | CANCEL to abort")

    elif state == "error":
        print(f"\n❌ Error: {ctx.get('error', 'Unknown')}")
        print("  RETRY to recover")


if __name__ == "__main__":
    main()
