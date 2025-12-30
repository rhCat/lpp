"""
CLI module for L++ LLM Schema Assistant.
Separated from interactive.py per build_rules.md (keep extrusion minimal).
"""

from pathlib import Path
from typing import Any

from .llm_compute import (
    init_config, load_schema, load_blueprint,
    query, explain_blueprint, validate_blueprint,
    suggest_improvements, generate_blueprint
)

ICONS = {"init": "⚙️", "ready": "✅", "querying": "🔄", "error": "❌"}


def print_help():
    print("""
┌─────────────────────────────────────────────────────────────────────┐
│  L++ LLM Schema Assistant                                           │
├─────────────────────────────────────────────────────────────────────┤
│  help              Show this help                                   │
│  status            Show configuration                               │
│  quit/q            Exit                                             │
├─────────────────────────────────────────────────────────────────────┤
│  key <api_key>     Set API key                                      │
│  base <url>        Set API base URL                                 │
│  model <name>      Set model (gpt-4o, gpt-4o-mini, etc.)            │
│  temp <0.0-2.0>    Set temperature                                  │
├─────────────────────────────────────────────────────────────────────┤
│  load <path>       Load blueprint file                              │
│  self              Load this assistant's blueprint                  │
│  clear             Clear blueprint & conversation                   │
├─────────────────────────────────────────────────────────────────────┤
│  ask <question>    Ask about L++ or loaded blueprint                │
│  explain           Explain loaded blueprint                         │
│  validate          Validate blueprint against schema                │
│  suggest           Get improvement suggestions                      │
│  generate <desc>   Generate new blueprint from description          │
├─────────────────────────────────────────────────────────────────────┤
│  Env: OPENAI_API_KEY, OPENAI_API_BASE, LPP_LLM_MODEL                │
└─────────────────────────────────────────────────────────────────────┘
""")


def print_status(ctx: dict):
    print(f"\n  API Key: {'✓' if ctx.get('api_key') else '✗'}")
    print(f"  Model: {ctx.get('model', 'not set')}")
    print(f"  Base: {ctx.get('api_base', 'not set')}")
    print(f"  Schema: {'✓' if ctx.get('schema_content') else '✗'}")
    print(f"  Blueprint: {ctx.get('blueprint_path') or 'none'}")
    print(f"  Conversation: {len(ctx.get('conversation', [])) // 2} turns")
    if ctx.get('error'):
        print(f"  Error: {ctx['error']}")


def format_response(text: str) -> str:
    lines = [
        "\n┌─ Response ─────────────────────────────────────────────────┐"
    ]
    for line in text.split('\n'):
        while len(line) > 70:
            lines.append(f"│ {line[:70]}")
            line = line[70:]
        lines.append(f"│ {line}")
    lines.append(
        "└────────────────────────────────────────────────────────────┘")
    return '\n'.join(lines)


def run_cli(op: Any, here: Path):
    """Main CLI loop. Dispatches events to operator."""
    print("\n🤖 L++ LLM Schema Assistant\nType 'help' for commands.\n")

    # Initialize from environment
    cfg = init_config({})
    op.context.update(cfg)
    op.context["conversation"] = []

    # Load schema
    schema_res = load_schema({})
    if schema_res["schema_content"]:
        op.context["schema_content"] = schema_res["schema_content"]
        print("✅ Schema loaded")

    # Check API key
    if op.context.get("api_key"):
        print(f"✅ Model: {op.context['model']}")
        op.context["_state"] = "ready"
    else:
        print("⚠️  Set OPENAI_API_KEY or use: key <your-key>")

    while True:
        icon = ICONS.get(op.state, "❓")
        bp = Path(op.context.get('blueprint_path', '')
                  ).stem if op.context.get('blueprint_path') else ''
        prompt = f"\n{icon} [{op.state}]{f' 📋{bp}' if bp else ''} > "

        try:
            cmd = input(prompt).strip()
        except (EOFError, KeyboardInterrupt):
            print("\n👋 Bye!")
            break

        if not cmd:
            continue

        parts = cmd.split(maxsplit=1)
        action, arg = parts[0].lower(), parts[1] if len(parts) > 1 else None

        if action in ("q", "quit", "exit"):
            print("👋 Bye!")
            break
        elif action == "help":
            print_help()
        elif action == "status":
            print_status(op.context)
        elif action == "key" and arg:
            op.context["api_key"] = arg
            op.context["_state"] = "ready"
            print("✅ API key set")
        elif action == "base" and arg:
            op.context["api_base"] = arg
            print(f"✅ Base: {arg}")
        elif action == "model" and arg:
            op.context["model"] = arg
            print(f"✅ Model: {arg}")
        elif action == "temp" and arg:
            try:
                t = float(arg)
                if 0 <= t <= 2:
                    op.context["temperature"] = t
                    print(f"✅ Temperature: {t}")
                else:
                    print("❌ Range: 0.0-2.0")
            except ValueError:
                print("❌ Invalid number")
        elif action == "load" and arg:
            res = load_blueprint({"path": arg})
            if res["blueprint"]:
                op.context.update(res)
                op.context["conversation"] = []
                print(f"✅ Loaded: {res['blueprint'].get('name', 'Unnamed')}")
            else:
                print(f"❌ {res['error']}")
        elif action == "self":
            res = load_blueprint({"path": str(here / "llm_assistant.json")})
            if res["blueprint"]:
                op.context.update(res)
                op.context["conversation"] = []
                print("✅ Loaded: llm_assistant (self)")
        elif action == "clear":
            op.context["blueprint"] = None
            op.context["blueprint_path"] = None
            op.context["conversation"] = []
            print("✅ Cleared")
        elif action in ("ask", "explain", "validate", "suggest", "generate"):
            if not op.context.get("api_key"):
                print("❌ No API key")
                continue

            params = {k: op.context.get(k) for k in [
                "api_key", "api_base", "model", "temperature",
                "max_tokens", "schema_content", "blueprint", "conversation"
            ]}

            print("🔄 Querying...")
            if action == "ask" and arg:
                params["query"] = arg
                res = query(params)
            elif action == "explain":
                if not op.context.get("blueprint"):
                    print("❌ No blueprint loaded")
                    continue
                res = explain_blueprint(params)
            elif action == "validate":
                if not op.context.get("blueprint"):
                    print("❌ No blueprint loaded")
                    continue
                res = validate_blueprint(params)
            elif action == "suggest":
                if not op.context.get("blueprint"):
                    print("❌ No blueprint loaded")
                    continue
                res = suggest_improvements(params)
            elif action == "generate" and arg:
                params["description"] = arg
                res = generate_blueprint(params)
            else:
                print("❌ Missing argument")
                continue

            if res.get("response"):
                if res.get("conversation"):
                    op.context["conversation"] = res["conversation"]
                print(format_response(res["response"]))
            else:
                print(f"❌ {res.get('error', 'Unknown error')}")
        else:
            # Treat as freeform query if API key set
            if op.context.get("api_key") and op.state == "ready":
                print("🔄 Querying...")
                params = {k: op.context.get(k) for k in [
                    "api_key", "api_base", "model", "temperature",
                    "max_tokens", "schema_content", "blueprint", "conversation"
                ]}
                params["query"] = cmd
                res = query(params)
                if res.get("response"):
                    op.context["conversation"] = res["conversation"]
                    print(format_response(res["response"]))
                else:
                    print(f"❌ {res.get('error')}")
            else:
                print(f"❓ Unknown: {action}. Type 'help'.")
