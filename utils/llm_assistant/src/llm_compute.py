"""
COMPUTE units for L++ LLM Schema Assistant

Hermetic functions for LLM interactions via OpenAI v1 API.
Per build_rules.md: Pure functions, params: dict -> result: dict.
"""

import json
import os
from pathlib import Path
from typing import Any, Dict, List

# OpenAI v1 API client
try:
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

# Schema path (relative to this file)
SCHEMA_PATH = Path(__file__).parent.parent.parent.parent / \
    "docs" / "schema_v0.1.md"

# System prompts
SYSTEM_PROMPT_BASE = """
You are an expert assistant for L++ (Logic Plus Plus),
a deterministic state machine specification language.

L++ separates Eternal Logic (The Bone - JSON blueprints) from Volatile Compute
(The Flesh - implementation).
The four atomic operators are:
1. TRANSITION - Move between states
2. GATE - Boolean guard conditions  
3. ACTION - Side effects (set, compute, emit)
4. FORK/JOIN - Parallel execution

You help users understand, create, validate, and improve L++ blueprints.
Be precise, reference the schema, and provide concrete examples."""

SYSTEM_PROMPT_WITH_SCHEMA = SYSTEM_PROMPT_BASE + """

L++ Schema Specification v0.1:
{schema}
"""


def init_config(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize configuration from environment. Pure function."""
    return {
        "api_key": os.environ.get("OPENAI_API_KEY") or None,
        "api_base": os.environ.get(
            "OPENAI_API_BASE",
            "https://api.openai.com/v1"
        ),
        "model": os.environ.get("LPP_LLM_MODEL", "gpt-4o-mini"),
        "temperature": 0.7,
        "max_tokens": 2048
    }


def load_schema(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load L++ schema specification. Pure function."""
    try:
        if not SCHEMA_PATH.exists():
            return {
                "schema_content": None,
                "error": f"Schema not found: {SCHEMA_PATH}"
            }
        return {"schema_content": SCHEMA_PATH.read_text(), "error": None}
    except Exception as e:
        return {"schema_content": None, "error": str(e)}


def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load blueprint from file. Pure function."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "blueprint_path": None, "error": "No path"}
    try:
        p = Path(path)
        if not p.exists():
            return {
                "blueprint": None,
                "blueprint_path": None,
                "error": f"Not found: {path}"
            }
        bp = json.loads(p.read_text())
        return {
            "blueprint": bp,
            "blueprint_path": str(p.resolve()),
            "error": None
        }
    except json.JSONDecodeError as e:
        return {
            "blueprint": None,
            "blueprint_path": None,
            "error": f"Invalid JSON: {e}"
        }
    except Exception as e:
        return {"blueprint": None, "blueprint_path": None, "error": str(e)}


def _call_llm(
        api_key: str,
        api_base: str,
        model: str,
        messages: List[Dict],
        temperature: float = 0.7,
        max_tokens: int = 2048
) -> Dict[str, Any]:
    """Internal: Call OpenAI-compatible API. Pure function."""
    if not OPENAI_AVAILABLE:
        return {
            "response": None,
            "error": "openai package not installed: pip install openai"
        }
    if not api_key:
        return {"response": None, "error": "No API key configured"}
    try:
        client = OpenAI(api_key=api_key, base_url=api_base)
        resp = client.chat.completions.create(
            model=model, messages=messages,
            temperature=temperature, max_tokens=max_tokens
        )
        return {
            "response": resp.choices[0].message.content,
            "error": None
        }
    except Exception as e:
        return {
            "response": None,
            "error": f"API error: {e}"
        }


def query(params: Dict[str, Any]) -> Dict[str, Any]:
    """Send query to LLM with context. Pure function."""
    schema = params.get("schema_content")
    blueprint = params.get("blueprint")
    conversation = params.get("conversation") or []
    user_query = params.get("query", "")

    # Build system message
    if schema:
        sys_msg = SYSTEM_PROMPT_WITH_SCHEMA.format(schema=schema)
    else:
        sys_msg = SYSTEM_PROMPT_BASE

    if blueprint:
        sys_msg += "\n\nCurrent blueprint:\n"
        sys_msg += f"```json\n{json.dumps(blueprint, indent=2)}\n```"

    messages = [{"role": "system", "content": sys_msg}]
    messages.extend(conversation)
    messages.append({"role": "user", "content": user_query})

    result = _call_llm(
        params.get("api_key"), params.get(
            "api_base", "https://api.openai.com/v1"),
        params.get("model", "gpt-4o-mini"), messages,
        params.get("temperature", 0.7), params.get("max_tokens", 2048)
    )

    if result["response"]:
        new_conv = list(conversation)
        new_conv.append({"role": "user", "content": user_query})
        new_conv.append({"role": "assistant", "content": result["response"]})
        return {
            "response": result["response"],
            "conversation": new_conv,
            "error": None
        }
    return {
        "response": None,
        "conversation": conversation,
        "error": result["error"]
    }


def explain_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Get detailed explanation of blueprint. Pure function."""
    if not params.get("blueprint"):
        return {
            "response": None,
            "conversation": [],
            "error": "No blueprint loaded"
        }

    params["query"] = """Explain this L++ blueprint comprehensively:
1. **Purpose**: What does this state machine do?
2. **States**: List each state and its role
3. **Flow**: Describe the transition logic
4. **Gates**: What conditions guard transitions?
5. **Actions**: What side effects occur?
6. **Entry/Terminal**: Lifecycle analysis"""
    params["conversation"] = []
    return query(params)


def validate_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Validate blueprint against schema. Pure function."""
    if not params.get("blueprint"):
        return {"response": None, "error": "No blueprint loaded"}

    params["query"] = """Validate this blueprint against L++ v0.1 schema:
1. **Schema Compliance**: All required fields present?
2. **State Integrity**: entry_state valid? terminal_states reachable?
3. **Transitions**: Well-formed? Any unreachable states?
4. **Gates**: Expressions valid?
5. **Actions**: Types correct? References valid?

List all issues with specific fixes."""
    params["conversation"] = []
    return query(params)


def suggest_improvements(params: Dict[str, Any]) -> Dict[str, Any]:
    """Suggest blueprint improvements. Pure function."""
    if not params.get("blueprint"):
        return {"response": None, "error": "No blueprint loaded"}

    params["query"] = """Analyze this blueprint and suggest improvements:
1. **Simplification**: Can states/transitions be consolidated?
2. **Edge Cases**: Missing error handling?
3. **Gate Optimization**: Simpler expressions?
4. **Best Practices**: L++ conventions followed?

Provide actionable suggestions with code examples."""
    params["conversation"] = []
    return query(params)


def generate_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate blueprint from description. Pure function."""
    desc = params.get("description", "")
    if not desc:
        return {"response": None, "error": "No description provided"}

    params["query"] = f"""Generate a complete L++ v0.1 blueprint for:

{desc}

Requirements:
- Valid JSON following schema_v0.1.md exactly
- Clear state names and descriptions
- Appropriate gates for conditions
- Well-defined actions
- Proper entry_state and terminal_states
- Include display rules

Output the complete JSON in a code block."""
    params["conversation"] = []
    return query(params)


# =============================================================================
# COMPUTE REGISTRY - namespace:operation -> function
# =============================================================================
COMPUTE_REGISTRY = {
    "llm:init_config": init_config,
    "llm:load_schema": load_schema,
    "llm:load_blueprint": load_blueprint,
    "llm:query": query,
    "llm:explain_blueprint": explain_blueprint,
    "llm:validate_blueprint": validate_blueprint,
    "llm:suggest_improvements": suggest_improvements,
    "llm:generate_blueprint": generate_blueprint,
}
