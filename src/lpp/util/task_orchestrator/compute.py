"""
Hierarchical Task Orchestrator - Atomic Compute Units

Each function is a single-purpose, hermetic unit.
Input: params dict. Output: result dict.
"""

from email.mime import base
import json
from logging import log
import os
from pathlib import Path
from typing import Any, Dict, List

try:
    from openai import OpenAI
    HAS_OPENAI = True
except ImportError:
    HAS_OPENAI = False


# =========================================================================
# LLM UTILITY (Single Responsibility: Call LLM)
# =========================================================================

def _llm(
    key: str,
    base: str,
    model: str,
    prompt: str,
    temp: float = 0.7
) -> str:
    """Atomic LLM call. Returns response text."""
    if not HAS_OPENAI:
        raise RuntimeError("openai not installed")
    client = OpenAI(api_key=key, base_url=base)
    r = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": prompt}],
        temperature=temp,
        max_tokens=2048
    )
    return r.choices[0].message.content


def _json(text: str) -> Any:
    """Extract JSON from text."""
    if "```json" in text:
        s = text.index("```json") + 7
        e = text.index("```", s)
        text = text[s:e].strip()
    elif "```" in text:
        s = text.index("```") + 3
        e = text.index("```", s)
        text = text[s:e].strip()
    return json.loads(text)


# =========================================================================
# INIT - Configure Environment
# =========================================================================

def init(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize orchestrator config from environment."""
    return {
        "api_key": os.environ.get("OPENAI_API_KEY"),
        "api_base": os.environ.get(
            "OPENAI_API_BASE",
            "https://api.openai.com/v1"
        ),
        "model": os.environ.get("OPENAI_MODEL", "gpt-4o-mini"),
        "max_depth": int(os.environ.get("ORCH_MAX_DEPTH", "3")),
        "max_iterations": int(os.environ.get("ORCH_MAX_ITER", "5")),
        "iteration": 0,
        "workspace_path": os.environ.get("ORCH_WORKSPACE", os.getcwd())
    }


# =========================================================================
# ANALYZE_ROOT - Create Initial Feature Tree
# =========================================================================

def analyze_root(params: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze task and create root feature tree."""
    task = params.get("task", "")

    prompt = f"""Analyze this task and identify top-level features.

TASK: {task}

Return a feature tree as JSON:
```json
{{
  "id": "root",
  "name": "Root Task",
  "desc": "...",
  "children": [
    {{"id": "f1", "name": "Feature 1", "desc": "...", "children": []}},
    {{"id": "f2", "name": "Feature 2", "desc": "...", "children": []}}
  ],
  "status": "pending"
}}
```

Rules:
- Break into 2-5 top-level features
- Each feature should be independently verifiable
- Order by dependency (foundational first)
- Leave children empty for now (will expand later)"""

    try:
        resp = _llm(
            params["api_key"], params["api_base"], params["model"], prompt
        )
        tree = _json(resp)
        has_children = len(tree.get("children", [])) > 0
        return {
            "feature_tree": tree,
            "current_path": [],
            "current_feature": tree,
            "depth": 0,
            "is_leaf": not has_children,
            "error": None
        }
    except Exception as e:
        return {
            "feature_tree": None,
            "current_path": [],
            "current_feature": None,
            "depth": 0,
            "is_leaf": True,
            "error": str(e)
        }


# =========================================================================
# EXPAND - Expand Current Feature into Sub-Features
# =========================================================================

def expand(params: Dict[str, Any]) -> Dict[str, Any]:
    """Expand a feature into sub-features (one level deeper)."""
    tree = params.get("feature_tree", {})
    path = params.get("current_path", [])
    feature = params.get("current_feature", {})
    depth = params.get("depth", 0)
    max_depth = params.get("max_depth", 3)

    # Find next unexpanded node
    node, new_path = _find_unexpanded(tree, max_depth)
    if node is None:
        return {
            "feature_tree": tree,
            "current_feature": feature,
            "depth": depth,
            "is_leaf": True,
            "error": None
        }

    prompt = f"""Expand this feature into atomic sub-features.

FEATURE: {node.get('name', '')}
DESCRIPTION: {node.get('desc', '')}
CURRENT DEPTH: {len(new_path)}

Return expanded children as JSON array:
```json
[
  {{"id": "sf1", "name": "Sub-feature 1", "desc": "...", "children": []}},
  {{"id": "sf2", "name": "Sub-feature 2", "desc": "...", "children": []}}
]
```

Rules:
- Break into 2-4 sub-features
- Make each sub-feature as atomic as possible
- If already atomic, return empty array []
- Each should be a single, verifiable unit of work"""

    try:
        resp = _llm(
            params["api_key"], params["api_base"], params["model"], prompt, 0.5
        )
        children = _json(resp)
        node["children"] = children
        node["status"] = "expanded"

        # Update tree at path
        _set_at_path(tree, new_path, node)

        # Check if more to expand
        next_node, _ = _find_unexpanded(tree, max_depth)
        is_leaf = next_node is None

        return {
            "feature_tree": tree,
            "current_feature": node,
            "depth": len(new_path),
            "is_leaf": is_leaf,
            "error": None
        }
    except Exception as e:
        return {
            "feature_tree": tree,
            "current_feature": feature,
            "depth": depth,
            "is_leaf": True,
            "error": str(e)
        }


def _find_unexpanded(node: dict, max_d: int, path: list = None) -> tuple:
    """Find next node that needs expansion."""
    path = path or []
    children = node.get("children", [])

    # If no children and not at max depth, needs expansion
    if not children and len(path) < max_d and node.get("status") != "expanded":
        return node, path

    # Search children
    for i, child in enumerate(children):
        found, found_path = _find_unexpanded(child, max_d, path + [i])
        if found:
            return found, found_path

    return None, []


def _set_at_path(tree: dict, path: list, value: dict):
    """Set node at path in tree."""
    node = tree
    for i in path[:-1]:
        node = node["children"][i]
    if path:
        node["children"][path[-1]] = value


# =========================================================================
# COLLECT - Gather All Leaf Nodes
# =========================================================================

def collect(params: Dict[str, Any]) -> Dict[str, Any]:
    """Collect all leaf nodes from feature tree."""
    tree = params.get("feature_tree", {})
    leaves = []
    _collect_leaves(tree, [], leaves)

    return {
        "leaf_queue": leaves,
        "leaf_count": len(leaves),
        "exec_count": 0,
        "error": None
    }


def _collect_leaves(node: dict, path: list, result: list):
    """Recursively collect leaf nodes."""
    children = node.get("children", [])
    if not children:
        result.append({
            "path": path,
            "id": node.get("id", ""),
            "name": node.get("name", ""),
            "desc": node.get("desc", ""),
            "status": "pending"
        })
    else:
        for i, child in enumerate(children):
            _collect_leaves(child, path + [i], result)


# =========================================================================
# PLAN_LEAF - Plan Execution for Current Leaf
# =========================================================================

def plan_leaf(params: Dict[str, Any]) -> Dict[str, Any]:
    """Plan execution for current leaf node."""
    queue = params.get("leaf_queue", [])
    idx = params.get("exec_count", 0)
    ws = params.get("workspace_path", ".")

    if idx >= len(queue):
        return {
            "current_feature": None,
            "tools_needed": [],
            "tools_pending": 0,
            "error": None
        }

    leaf = queue[idx]

    prompt = f"""Plan implementation for this atomic feature.

FEATURE: {leaf.get('name', '')}
DESCRIPTION: {leaf.get('desc', '')}
WORKSPACE: {ws}

Return JSON plan:
```json
{{
  "steps": [
    {{"id": "s1", "action": "...", "details": "..."}}
  ],
  "tools_needed": [
    {{"name": "tool_name", "purpose": "..."}}
  ]
}}
```

Rules:
- Keep steps minimal and concrete
- Only list tools if truly needed (prefer existing)
- Each step should be independently executable"""

    try:
        resp = _llm(
            params["api_key"], params["api_base"], params["model"], prompt, 0.3
        )
        plan = _json(resp)
        leaf["plan"] = plan
        tools = plan.get("tools_needed", [])

        return {
            "current_feature": leaf,
            "tools_needed": tools,
            "tools_pending": len(tools),
            "error": None
        }
    except Exception as e:
        return {
            "current_feature": leaf,
            "tools_needed": [],
            "tools_pending": 0,
            "error": str(e)
        }


# =========================================================================
# BUILD - Build Single Tool
# =========================================================================

def build(params: Dict[str, Any]) -> Dict[str, Any]:
    """Build one tool from the needed list."""
    tools = params.get("tools_needed", [])
    pending = params.get("tools_pending", 0)
    built = params.get("tools_built", []) or []
    ws = params.get("workspace_path", ".")

    if not tools:
        return {
            "tools_needed": [],
            "tools_pending": 0,
            "tools_built": built,
            "error": None
        }

    tool = tools[0]
    name = tool.get("name", "tool")

    prompt = f"""Generate L++ skill blueprint for: {name}
Purpose: {tool.get('purpose', '')}

Return valid JSON blueprint (schema v0.1.2):
```json
{{
  "$schema": "lpp/v0.2.0",
  "id": "{name}",
  "name": "...",
  "description": "...",
  "context_schema": {{"properties": {{}}}},
  "states": {{}},
  "entry_state": "idle",
  "terminal_states": [],
  "gates": {{}},
  "actions": {{}},
  "transitions": []
}}
```"""

    try:
        resp = _llm(
            params["api_key"], params["api_base"], params["model"], prompt, 0.3
        )
        bp = _json(resp)

        # Save
        d = Path(ws) / "utils" / name
        d.mkdir(parents=True, exist_ok=True)
        p = d / f"{name}.json"
        p.write_text(json.dumps(bp, indent=2))

        built.append({"name": name, "path": str(p), "status": "created"})
        remaining = tools[1:]

        return {
            "tools_needed": remaining,
            "tools_pending": len(remaining),
            "tools_built": built,
            "error": None
        }
    except Exception as e:
        return {
            "tools_needed": tools,
            "tools_pending": pending,
            "tools_built": built,
            "error": f"Build failed: {e}"
        }


# =========================================================================
# EXEC_LEAF - Execute Single Leaf Node
# =========================================================================

def exec_leaf(params: Dict[str, Any]) -> Dict[str, Any]:
    """Execute current leaf feature."""
    feature = params.get("current_feature", {})
    queue = params.get("leaf_queue", [])
    idx = params.get("exec_count", 0)
    log = params.get("exec_log", []) or []
    ws = params.get("workspace_path", ".")

    if idx >= len(queue):
        return {
            "leaf_queue": queue,
            "exec_count": idx,
            "exec_log": log,
            "error": None
        }

    prompt = f"""Execute this atomic feature and report result.

FEATURE: {feature.get('name', '')}
DESCRIPTION: {feature.get('desc', '')}
PLAN: {json.dumps(feature.get('plan', {}), indent=2)}
WORKSPACE: {ws}

Describe actions taken and outcomes. Be specific."""

    try:
        resp = _llm(
            params["api_key"], params["api_base"], params["model"], prompt
        )

        # Update queue
        queue[idx]["status"] = "complete"
        queue[idx]["result"] = resp[:500]

        # Add to log
        log.append({
            "id": feature.get("id", ""),
            "name": feature.get("name", ""),
            "status": "complete",
            "result": resp[:200]
        })

        return {
            "leaf_queue": queue,
            "exec_count": idx + 1,
            "exec_log": log,
            "error": None
        }
    except Exception as e:
        queue[idx]["status"] = "failed"
        return {
            "leaf_queue": queue,
            "exec_count": idx,
            "exec_log": log,
            "error": str(e)
        }


# =========================================================================
# NEXT_LEAF - Move to Next Leaf
# =========================================================================

def next_leaf(params: Dict[str, Any]) -> Dict[str, Any]:
    """Prepare next leaf for execution."""
    queue = params.get("leaf_queue", [])
    idx = params.get("exec_count", 0)
    count = params.get("leaf_count", 0)

    if idx >= count:
        return {
            "current_feature": None,
            "tools_pending": 0,
            "is_complete": True,
            "error": None
        }

    leaf = queue[idx]
    tools = leaf.get("plan", {}).get("tools_needed", [])

    return {
        "current_feature": leaf,
        "tools_pending": len(tools),
        "is_complete": False,
        "error": None
    }


# =========================================================================
# REFLECT - Assess Progress
# =========================================================================

def reflect(params: Dict[str, Any]) -> Dict[str, Any]:
    """Reflect on execution progress."""
    task = params.get("task", "")
    tree = params.get("feature_tree", {})
    logs = params.get("exec_log", [])
    iteration = params.get("iteration", 0)

    done = [
        ls for ls in logs if ls.get("status") == "complete"
    ]

    prompt = f"""Reflect on task progress.

TASK: {task}
ITERATION: {iteration + 1}
COMPLETED: {len(done)}/{len(logs)} features

EXECUTION LOG:
{json.dumps(logs[-5:], indent=2)}

Provide:
1. Progress assessment
2. What worked
3. What needs adjustment
4. Recommended next steps"""

    try:
        resp = _llm(
            params["api_key"], params["api_base"], params["model"], prompt
        )
        return {
            "reflection": resp,
            "feature_tree": tree,
            "error": None
        }
    except Exception as e:
        return {
            "reflection": "",
            "feature_tree": tree,
            "error": str(e)
        }


# =========================================================================
# EVALUATE - Check Completion
# =========================================================================

def evaluate(params: Dict[str, Any]) -> Dict[str, Any]:
    """Evaluate task completion."""
    task = params.get("task", "")
    logs = params.get("exec_log", [])
    reflection = params.get("reflection", "")
    iteration = params.get("iteration", 0)
    max_iter = params.get("max_iterations", 5)

    done = [ls for ls in logs if ls.get("status") == "complete"]

    prompt = f"""Evaluate task completion.

TASK: {task}
ITERATION: {iteration + 1}/{max_iter}
COMPLETED: {len(done)}/{len(log)} features
REFLECTION: {reflection[:500]}

Return JSON:
```json
{{
  "complete": true/false,
  "score": 0.0-1.0,
  "reason": "...",
  "remaining": []
}}
```

Mark complete=true ONLY if task objectives are fully met."""

    try:
        resp = _llm(
            params["api_key"], params["api_base"], params["model"], prompt, 0.3
        )
        ev = _json(resp)
        return {
            "evaluation": ev,
            "is_complete": ev.get("complete", False),
            "error": None
        }
    except Exception as e:
        return {
            "evaluation": {"complete": False, "score": 0, "reason": str(e)},
            "is_complete": False,
            "error": None
        }


# =========================================================================
# UTILITY ACTIONS
# =========================================================================

def incr(params: Dict[str, Any]) -> Dict[str, Any]:
    """Increment iteration counter."""
    return {"iteration": params.get("iteration", 0) + 1}


def reset_exec(params: Dict[str, Any]) -> Dict[str, Any]:
    """Reset execution state for next iteration."""
    return {"exec_count": 0, "tools_pending": 0}


# =========================================================================
# REGISTRY
# =========================================================================

COMPUTE_REGISTRY = {
    ("orch", "init"): init,
    ("orch", "analyze_root"): analyze_root,
    ("orch", "expand"): expand,
    ("orch", "collect"): collect,
    ("orch", "plan_leaf"): plan_leaf,
    ("orch", "build"): build,
    ("orch", "exec_leaf"): exec_leaf,
    ("orch", "next_leaf"): next_leaf,
    ("orch", "reflect"): reflect,
    ("orch", "evaluate"): evaluate,
    ("orch", "incr"): incr,
    ("orch", "reset_exec"): reset_exec,
}
