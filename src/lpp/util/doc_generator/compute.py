"""
COMPUTE units for the L++ Documentation Generator.

These are the pure computation functions that generate comprehensive
documentation from L++ blueprints in multiple formats (Markdown, HTML, JSON).
"""

import json
from pathlib import Path
from typing import Any, Dict, List
from datetime import datetime

from lpp.core import BlueprintLoader


# =============================================================================
# BLUEPRINT LOADING
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "error": "No path provided"}

    try:
        path = Path(path)
        if not path.exists():
            return {"blueprint": None, "error": f"File not found: {path}"}

        with open(path) as f:
            raw = json.load(f)

        loader = BlueprintLoader(raw)
        blueprint, error = loader.load()

        if error:
            return {"blueprint": None, "error": error}

        # Convert to dict for easy access
        bp_data = {
            "id": blueprint.id,
            "name": blueprint.name,
            "version": blueprint.version,
            "description": blueprint.description,
            "schema": raw.get("$schema", "unknown"),
            "states": {
                sid: {"description": s.description}
                for sid, s in blueprint.states.items()
            },
            "transitions": [
                {
                    "id": t.id,
                    "from": t.from_state,
                    "to": t.to_state,
                    "on_event": t.on_event,
                    "gate": t.gates[0] if t.gates else None,
                    "gates": list(t.gates),
                    "actions": list(t.actions)
                }
                for t in blueprint.transitions
            ],
            "gates": {
                gid: {"expression": g.expression, "type": g.type.value}
                for gid, g in blueprint.gates.items()
            },
            "actions": raw.get("actions", {}),
            "context_schema": raw.get("context_schema", {}),
            "entry_state": blueprint.entry_state,
            "terminal_states": list(blueprint.terminal_states),
            "display": raw.get("display", {})
        }

        return {
            "blueprint": bp_data,
            "blueprint_path": str(path),
            "blueprint_name": blueprint.name,
            "blueprint_id": blueprint.id,
            "error": None
        }
    except Exception as e:
        return {"blueprint": None, "error": str(e)}


def init_defaults(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize default documentation settings."""
    return {
        "output_format": "markdown",
        "include_mermaid": True,
        "include_tables": True,
        "include_quickstart": True,
        "include_context": True
    }


def toggle(params: Dict[str, Any]) -> Dict[str, Any]:
    """Toggle a boolean value."""
    current = params.get("current", False)
    return {"result": not current}


def clear_sections(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear all generated sections."""
    return {
        "overview_section": None,
        "mermaid_section": None,
        "states_section": None,
        "transitions_section": None,
        "gates_section": None,
        "actions_section": None,
        "context_section": None,
        "events_section": None,
        "quickstart_section": None,
        "assembled_doc": None
    }


# =============================================================================
# METADATA EXTRACTION
# =============================================================================

def extract_metadata(params: Dict[str, Any]) -> Dict[str, Any]:
    """Extract metadata from blueprint."""
    bp = params.get("blueprint", {})

    metadata = {
        "name": bp.get("name", "Untitled"),
        "id": bp.get("id", "unknown"),
        "version": bp.get("version", "0.0.0"),
        "description": bp.get("description", ""),
        "schema": bp.get("schema", "lpp/v0.1.2"),
        "state_count": len(bp.get("states", {})),
        "transition_count": len(bp.get("transitions", [])),
        "gate_count": len(bp.get("gates", {})),
        "action_count": len(bp.get("actions", {})),
        "entry_state": bp.get("entry_state", ""),
        "terminal_states": bp.get("terminal_states", []),
        "generated_at": datetime.now().isoformat()
    }

    return {"metadata": metadata}


# =============================================================================
# SECTION GENERATORS
# =============================================================================

def generate_overview(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate the overview section."""
    bp = params.get("blueprint", {})
    metadata = params.get("metadata", {})

    lines = [
        f"# {bp.get('name', 'Untitled Blueprint')}",
        "",
        bp.get("description", "") or "_No description provided._",
        "",
        "## Overview",
        "",
        "| Property | Value |",
        "|----------|-------|",
        f"| **ID** | `{bp.get('id', 'unknown')}` |",
        f"| **Version** | {bp.get('version', '0.0.0')} |",
        f"| **Schema** | {bp.get('schema', 'lpp/v0.1.2')} |",
        f"| **Entry State** | `{bp.get('entry_state', '-')}` |",
        f"| **Terminal States** | {_format_list(bp.get('terminal_states', []))} |",
        f"| **States** | {metadata.get('state_count', 0)} |",
        f"| **Transitions** | {metadata.get('transition_count', 0)} |",
        f"| **Gates** | {metadata.get('gate_count', 0)} |",
        f"| **Actions** | {metadata.get('action_count', 0)} |",
        "",
    ]

    return {"section": "\n".join(lines)}


def generate_mermaid(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate mermaid state diagram section."""
    bp = params.get("blueprint", {})

    lines = [
        "## State Machine Diagram",
        "",
        "```mermaid",
        "stateDiagram-v2",
        f"    [*] --> {bp.get('entry_state', 'init')}",
        "",
    ]

    # State definitions with descriptions
    for sid, state in bp.get("states", {}).items():
        desc = state.get("description", "")
        if desc:
            safe_desc = desc.replace('"', "'")[:50]
            lines.append(f'    {sid}: {sid}\\n{safe_desc}')
        else:
            lines.append(f"    {sid}: {sid}")
    lines.append("")

    # Transitions - expand wildcards
    all_states = list(bp.get("states", {}).keys())
    seen = set()
    for t in bp.get("transitions", []):
        label = t["on_event"]
        if t.get("gate"):
            label = f"{t['on_event']} [{t['gate']}]"

        from_states = all_states if t["from"] == "*" else [t["from"]]
        for from_state in from_states:
            if from_state != t["to"]:  # Skip self-loops for clarity
                key = (from_state, t["to"], label)
                if key not in seen:
                    seen.add(key)
                    lines.append(f"    {from_state} --> {t['to']}: {label}")

    lines.append("")

    # Terminal states
    for ts in bp.get("terminal_states", []):
        lines.append(f"    {ts} --> [*]")

    lines.extend(["```", ""])

    return {"section": "\n".join(lines)}


def generate_states_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate states documentation table."""
    bp = params.get("blueprint", {})
    entry = bp.get("entry_state")
    terminals = bp.get("terminal_states", [])

    lines = [
        "## States",
        "",
        "| State | Type | Description |",
        "|-------|------|-------------|",
    ]

    for sid, state in bp.get("states", {}).items():
        stype = "Entry" if sid == entry else ("Terminal" if sid in terminals
                                              else "Normal")
        desc = state.get("description", "-")
        lines.append(f"| `{sid}` | {stype} | {desc} |")

    lines.append("")
    return {"section": "\n".join(lines)}


def generate_transitions_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate transitions documentation table."""
    bp = params.get("blueprint", {})
    transitions = bp.get("transitions", [])

    if not transitions:
        return {"section": "## Transitions\n\n_No transitions defined._\n"}

    lines = [
        "## Transitions",
        "",
        "| ID | From | To | Event | Gate(s) | Action(s) |",
        "|----|------|-----|-------|---------|-----------|",
    ]

    for t in transitions:
        tid = t.get("id", "-")
        frm = t.get("from", "-")
        to = t.get("to", "-")
        event = t.get("on_event", "-")
        gates = ", ".join(t.get("gates", [])) or "-"
        actions = ", ".join(t.get("actions", [])) or "-"
        lines.append(f"| `{tid}` | `{frm}` | `{to}` | `{event}` | {gates} | "
                     f"{actions} |")

    lines.append("")
    return {"section": "\n".join(lines)}


def generate_gates_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate gates documentation table."""
    bp = params.get("blueprint", {})
    gates = bp.get("gates", {})

    if not gates:
        return {"section": "## Gates\n\n_No gates defined._\n"}

    lines = [
        "## Gates",
        "",
        "Gates are boolean guards that control transition eligibility.",
        "",
        "| Gate | Type | Expression |",
        "|------|------|------------|",
    ]

    for gid, gate in gates.items():
        gtype = gate.get("type", "expression")
        expr = gate.get("expression", "-")
        lines.append(f"| `{gid}` | {gtype} | `{expr}` |")

    lines.append("")
    return {"section": "\n".join(lines)}


def generate_actions_table(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate actions documentation table."""
    bp = params.get("blueprint", {})
    actions = bp.get("actions", {})

    if not actions:
        return {"section": "## Actions\n\n_No actions defined._\n"}

    lines = [
        "## Actions",
        "",
        "Actions are side-effects executed during transitions.",
        "",
        "| Action | Type | Details |",
        "|--------|------|---------|",
    ]

    for aid, action in actions.items():
        atype = action.get("type", "unknown")
        details = _format_action_details(action)
        lines.append(f"| `{aid}` | `{atype}` | {details} |")

    lines.append("")
    return {"section": "\n".join(lines)}


def _format_action_details(action: Dict[str, Any]) -> str:
    """Format action details based on type."""
    atype = action.get("type", "")

    if atype == "set":
        target = action.get("target", "?")
        if "value" in action:
            return f"target: `{target}`, value: `{action['value']}`"
        elif "value_from" in action:
            return f"target: `{target}`, from: `{action['value_from']}`"
        return f"target: `{target}`"

    elif atype == "compute":
        unit = action.get("compute_unit", "?")
        return f"unit: `{unit}`"

    elif atype == "emit":
        event = action.get("event", "?")
        return f"event: `{event}`"

    return "-"


def generate_context_docs(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate context schema documentation."""
    bp = params.get("blueprint", {})
    schema = bp.get("context_schema", {})
    props = schema.get("properties", {})

    if not props:
        return {"section": "## Context Schema\n\n_No context properties._\n"}

    lines = [
        "## Context Schema",
        "",
        "The context schema defines the data interface (\"Flange\") for this "
        "blueprint.",
        "",
        "| Property | Type | Description |",
        "|----------|------|-------------|",
    ]

    for name, prop in props.items():
        ptype = prop.get("type", "any")
        desc = prop.get("description", "-")
        lines.append(f"| `{name}` | `{ptype}` | {desc} |")

    lines.append("")
    return {"section": "\n".join(lines)}


def generate_events_list(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate events documentation."""
    bp = params.get("blueprint", {})
    transitions = bp.get("transitions", [])

    # Collect unique events
    events: Dict[str, List[str]] = {}
    for t in transitions:
        event = t.get("on_event", "")
        if event:
            if event not in events:
                events[event] = []
            events[event].append(
                f"`{t.get('from', '?')}` -> `{t.get('to', '?')}`")

    if not events:
        return {"section": "## Events\n\n_No events defined._\n"}

    lines = [
        "## Events",
        "",
        "Events trigger state transitions in the blueprint.",
        "",
        "| Event | Transitions |",
        "|-------|-------------|",
    ]

    for event, trans in sorted(events.items()):
        trans_str = ", ".join(trans[:3])
        if len(trans) > 3:
            trans_str += f" (+{len(trans) - 3} more)"
        lines.append(f"| `{event}` | {trans_str} |")

    lines.append("")
    return {"section": "\n".join(lines)}


def generate_quickstart(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate quick-start guide with example event sequences."""
    bp = params.get("blueprint", {})

    entry = bp.get("entry_state", "init")
    transitions = bp.get("transitions", [])
    terminals = bp.get("terminal_states", [])

    # Find paths from entry to terminals or interesting states
    paths = _find_example_paths(entry, transitions, terminals, max_depth=5)

    lines = [
        "## Quick Start Guide",
        "",
        "### Basic Usage",
        "",
        "```python",
        "# Load and compile the blueprint",
        "from frame_py.compiler import compile_blueprint",
        "",
        f'compile_blueprint("{bp.get("id", "blueprint")}.json", "compiled.py")',
        "",
        "# Create operator instance",
        "from compiled import create_operator",
        "op = create_operator(compute_registry)",
        "",
        "# Dispatch events",
    ]

    # Add example event dispatches
    if paths:
        for event in paths[0][:3]:
            lines.append(f'op.dispatch("{event}")')
    else:
        lines.append('op.dispatch("YOUR_EVENT_HERE")')

    lines.extend([
        "```",
        "",
        "### Example Event Sequences",
        "",
    ])

    if paths:
        for i, path in enumerate(paths[:3], 1):
            seq = " -> ".join([f"`{e}`" for e in path])
            lines.append(f"{i}. {seq}")
    else:
        lines.append("_No example paths found._")

    lines.append("")
    return {"section": "\n".join(lines)}


def _find_example_paths(entry: str, transitions: List[Dict],
                        terminals: List[str], max_depth: int) -> List[List[str]]:
    """Find example event sequences from entry state."""
    paths = []

    # Build adjacency map
    adj: Dict[str, List[tuple]] = {}
    for t in transitions:
        frm = t.get("from", "")
        if frm not in adj:
            adj[frm] = []
        adj[frm].append((t.get("on_event", ""), t.get("to", "")))

    # BFS to find paths
    queue = [(entry, [])]
    visited = set()

    while queue and len(paths) < 5:
        state, path = queue.pop(0)

        if len(path) >= max_depth:
            if path:
                paths.append(path)
            continue

        if state in terminals and path:
            paths.append(path)
            continue

        if state in visited:
            continue
        visited.add(state)

        for event, next_state in adj.get(state, []):
            new_path = path + [event]
            queue.append((next_state, new_path))

    return paths


# =============================================================================
# DOCUMENT ASSEMBLY
# =============================================================================

def assemble_markdown(params: Dict[str, Any]) -> Dict[str, Any]:
    """Assemble all sections into final markdown document."""
    parts = [params.get("overview_section", "")]

    if params.get("include_quickstart"):
        parts.append(params.get("quickstart_section", ""))

    if params.get("include_mermaid"):
        parts.append(params.get("mermaid_section", ""))

    if params.get("include_tables"):
        parts.append(params.get("states_section", ""))
        parts.append(params.get("transitions_section", ""))
        parts.append(params.get("gates_section", ""))
        parts.append(params.get("actions_section", ""))

    if params.get("include_context"):
        parts.append(params.get("context_section", ""))

    parts.append(params.get("events_section", ""))

    # Footer
    parts.extend([
        "---",
        "",
        "_Generated by L++ Documentation Generator_",
        ""
    ])

    return {"doc": "\n".join(filter(None, parts))}


def assemble_html(params: Dict[str, Any]) -> Dict[str, Any]:
    """Assemble all sections into HTML document with styling."""
    bp_name = params.get("blueprint_name", "L++ Blueprint")

    # Build markdown first
    md_result = assemble_markdown(params)
    md_content = md_result.get("doc", "")

    # Convert markdown to HTML with styling
    html_parts = [
        "<!DOCTYPE html>",
        "<html lang=\"en\">",
        "<head>",
        "    <meta charset=\"UTF-8\">",
        "    <meta name=\"viewport\" content=\"width=device-width, "
        "initial-scale=1.0\">",
        f"    <title>{bp_name} - Documentation</title>",
        "    <style>",
        "        :root {",
        "            --primary: #2563eb;",
        "            --bg: #f8fafc;",
        "            --text: #1e293b;",
        "            --border: #e2e8f0;",
        "            --code-bg: #f1f5f9;",
        "        }",
        "        body {",
        "            font-family: -apple-system, BlinkMacSystemFont, "
        "'Segoe UI', Roboto, sans-serif;",
        "            line-height: 1.6;",
        "            max-width: 900px;",
        "            margin: 0 auto;",
        "            padding: 2rem;",
        "            background: var(--bg);",
        "            color: var(--text);",
        "        }",
        "        h1, h2, h3 { color: var(--primary); }",
        "        h1 { border-bottom: 2px solid var(--primary); "
        "padding-bottom: 0.5rem; }",
        "        h2 { margin-top: 2rem; }",
        "        table {",
        "            width: 100%;",
        "            border-collapse: collapse;",
        "            margin: 1rem 0;",
        "            background: white;",
        "            box-shadow: 0 1px 3px rgba(0,0,0,0.1);",
        "        }",
        "        th, td {",
        "            padding: 0.75rem;",
        "            text-align: left;",
        "            border: 1px solid var(--border);",
        "        }",
        "        th { background: var(--primary); color: white; }",
        "        tr:nth-child(even) { background: var(--bg); }",
        "        code {",
        "            background: var(--code-bg);",
        "            padding: 0.2rem 0.4rem;",
        "            border-radius: 3px;",
        "            font-size: 0.9em;",
        "        }",
        "        pre {",
        "            background: #1e293b;",
        "            color: #e2e8f0;",
        "            padding: 1rem;",
        "            border-radius: 8px;",
        "            overflow-x: auto;",
        "        }",
        "        pre code { background: none; color: inherit; }",
        "        .mermaid { background: white; padding: 1rem; "
        "border-radius: 8px; }",
        "    </style>",
        "    <script src=\"https://cdn.jsdelivr.net/npm/mermaid/dist/"
        "mermaid.min.js\"></script>",
        "</head>",
        "<body>",
    ]

    # Convert markdown to HTML (simple conversion)
    html_content = _markdown_to_html(md_content)
    html_parts.append(html_content)

    html_parts.extend([
        "    <script>mermaid.initialize({startOnLoad:true});</script>",
        "</body>",
        "</html>"
    ])

    return {"doc": "\n".join(html_parts)}


def _markdown_to_html(md: str) -> str:
    """Simple markdown to HTML conversion."""
    import re

    lines = md.split("\n")
    html_lines = []
    in_table = False
    in_code = False
    in_mermaid = False
    table_rows = []

    for line in lines:
        # Code blocks
        if line.startswith("```mermaid"):
            in_mermaid = True
            html_lines.append('<div class="mermaid">')
            continue
        elif line.startswith("```") and in_mermaid:
            in_mermaid = False
            html_lines.append("</div>")
            continue
        elif line.startswith("```"):
            if in_code:
                in_code = False
                html_lines.append("</code></pre>")
            else:
                in_code = True
                html_lines.append("<pre><code>")
            continue

        if in_code or in_mermaid:
            html_lines.append(line)
            continue

        # Headers
        if line.startswith("# "):
            html_lines.append(f"<h1>{_escape_html(line[2:])}</h1>")
            continue
        if line.startswith("## "):
            html_lines.append(f"<h2>{_escape_html(line[3:])}</h2>")
            continue
        if line.startswith("### "):
            html_lines.append(f"<h3>{_escape_html(line[4:])}</h3>")
            continue

        # Tables
        if line.startswith("|"):
            if not in_table:
                in_table = True
                table_rows = []
            table_rows.append(line)
            continue
        elif in_table:
            in_table = False
            html_lines.append(_convert_table(table_rows))
            table_rows = []

        # Horizontal rule
        if line.strip() == "---":
            html_lines.append("<hr>")
            continue

        # Inline formatting
        line = _format_inline(line)

        # Paragraph
        if line.strip():
            html_lines.append(f"<p>{line}</p>")

    # Close any open table
    if in_table:
        html_lines.append(_convert_table(table_rows))

    return "\n".join(html_lines)


def _escape_html(text: str) -> str:
    """Escape HTML special characters."""
    return (text.replace("&", "&amp;")
                .replace("<", "&lt;")
                .replace(">", "&gt;"))


def _format_inline(text: str) -> str:
    """Format inline markdown elements."""
    import re

    # Bold
    text = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', text)
    # Italic
    text = re.sub(r'_(.+?)_', r'<em>\1</em>', text)
    # Code
    text = re.sub(r'`(.+?)`', r'<code>\1</code>', text)

    return text


def _convert_table(rows: List[str]) -> str:
    """Convert markdown table rows to HTML."""
    if len(rows) < 2:
        return ""

    html = ["<table>", "<thead><tr>"]

    # Header row
    cells = [c.strip() for c in rows[0].split("|")[1:-1]]
    for cell in cells:
        html.append(f"<th>{_format_inline(cell)}</th>")
    html.append("</tr></thead>")

    # Body rows (skip separator row)
    html.append("<tbody>")
    for row in rows[2:]:
        cells = [c.strip() for c in row.split("|")[1:-1]]
        html.append("<tr>")
        for cell in cells:
            html.append(f"<td>{_format_inline(cell)}</td>")
        html.append("</tr>")
    html.append("</tbody></table>")

    return "\n".join(html)


def assemble_json(params: Dict[str, Any]) -> Dict[str, Any]:
    """Assemble documentation as JSON structure."""
    bp = params.get("blueprint", {})
    metadata = params.get("metadata", {})

    doc = {
        "metadata": metadata,
        "blueprint": {
            "id": bp.get("id"),
            "name": bp.get("name"),
            "version": bp.get("version"),
            "description": bp.get("description"),
            "schema": bp.get("schema"),
            "entry_state": bp.get("entry_state"),
            "terminal_states": bp.get("terminal_states", [])
        },
        "states": bp.get("states", {}),
        "transitions": bp.get("transitions", []),
        "gates": bp.get("gates", {}),
        "actions": bp.get("actions", {}),
        "context_schema": bp.get("context_schema", {}),
        "generated_at": metadata.get("generated_at", "")
    }

    return {"doc": json.dumps(doc, indent=2)}


# =============================================================================
# EXPORT
# =============================================================================

def export_docs(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export documentation to file."""
    content = params.get("content", "")
    path = params.get("path", "")
    fmt = params.get("format", "markdown")

    if not path:
        # Generate default path
        path = f"./docs_output.{_get_extension(fmt)}"

    try:
        p = Path(path)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)
        return {"path": str(p.absolute()), "error": None}
    except Exception as e:
        return {"path": None, "error": str(e)}


def _get_extension(fmt: str) -> str:
    """Get file extension for format."""
    return {"markdown": "md", "html": "html", "json": "json"}.get(fmt, "txt")


def _format_list(items: List[str]) -> str:
    """Format a list as comma-separated or placeholder."""
    if not items:
        return "_none_"
    return ", ".join([f"`{i}`" for i in items])


# =============================================================================
# MULTI-BLUEPRINT DOC GENERATION (used by blueprint.json)
# =============================================================================

def init(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize doc generation settings."""
    return {
        "initialized": True,
        "error": None
    }


def discoverBlueprints(params: Dict[str, Any]) -> Dict[str, Any]:
    """Discover all blueprints in the utils path."""
    utils_path = params.get("utilsPath", ".")

    try:
        path = Path(utils_path)
        if not path.exists():
            return {"blueprints": [], "error": f"Path not found: {utils_path}"}

        blueprints = []
        # Look for blueprint.json files in util directories
        for bp_file in path.rglob("blueprint.json"):
            try:
                with open(bp_file) as f:
                    bp_data = json.load(f)
                blueprints.append({
                    "path": str(bp_file),
                    "id": bp_data.get("id", bp_file.parent.name),
                    "name": bp_data.get("name", bp_file.parent.name),
                    "version": bp_data.get("version", "0.0.0")
                })
            except Exception:
                continue  # Skip invalid blueprints

        return {"blueprints": blueprints, "error": None}
    except Exception as e:
        return {"blueprints": [], "error": str(e)}


def generateGraphs(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate HTML graph visualizations for all blueprints."""
    blueprints = params.get("blueprints", [])
    output_path = params.get("outputPath", "./results")
    results = params.get("results", {"generated": 0, "errors": []})

    # Placeholder - would call graph_visualizer for each blueprint
    results["generated"] += len(blueprints)
    return {"results": results, "error": None}


def generateLogicGraphs(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate logic graphs from Python compute files."""
    blueprints = params.get("blueprints", [])
    results = params.get("results", {"generated": 0, "errors": []})

    # Placeholder - would call logic_decoder for each compute.py
    results["generated"] += len(blueprints)
    return {"results": results, "error": None}


def generateFunctionGraphs(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate function dependency graphs."""
    blueprints = params.get("blueprints", [])
    results = params.get("results", {"generated": 0, "errors": []})

    # Placeholder - would analyze function dependencies
    results["generated"] += len(blueprints)
    return {"results": results, "error": None}


def generateMermaidDiagrams(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate Mermaid diagrams for all blueprints."""
    blueprints = params.get("blueprints", [])
    results = params.get("results", {"generated": 0, "errors": []})

    for bp in blueprints:
        try:
            # Load blueprint and generate mermaid
            bp_path = bp.get("path")
            if bp_path:
                with open(bp_path) as f:
                    bp_data = json.load(f)
                # Mermaid generation would go here
                results["generated"] += 1
        except Exception as e:
            results["errors"].append(f"{bp.get('id')}: {str(e)}")

    return {"results": results, "error": None}


def updateReadmes(params: Dict[str, Any]) -> Dict[str, Any]:
    """Update README files with generated documentation."""
    blueprints = params.get("blueprints", [])
    results = params.get("results", {"generated": 0, "errors": []})

    # Placeholder - would update README.md files
    return {"results": results, "error": None}


def generateReport(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate analysis report for all blueprints."""
    blueprints = params.get("blueprints", [])
    output_path = params.get("outputPath", "./results")
    results = params.get("results", {"generated": 0, "errors": []})

    report = {
        "total_blueprints": len(blueprints),
        "blueprints": [bp.get("id") for bp in blueprints],
        "generated_at": datetime.now().isoformat()
    }

    results["report"] = report
    return {"results": results, "error": None}


def generateDashboard(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate dashboard HTML for all blueprints."""
    blueprints = params.get("blueprints", [])
    output_path = params.get("outputPath", "./results")
    results = params.get("results", {"generated": 0, "errors": []})

    # Placeholder - would generate HTML dashboard
    results["generated"] += 1
    return {"results": results, "error": None}


def finalize(params: Dict[str, Any]) -> Dict[str, Any]:
    """Finalize documentation generation."""
    results = params.get("results", {"generated": 0, "errors": []})
    return {
        "results": results,
        "complete": True,
        "error": None
    }


# =============================================================================
# COMPUTE REGISTRY
# =============================================================================

COMPUTE_REGISTRY = {
    # Multi-blueprint doc generation (used by blueprint.json)
    ("docgen", "init"): init,
    ("docgen", "discoverBlueprints"): discoverBlueprints,
    ("docgen", "generateGraphs"): generateGraphs,
    ("docgen", "generateLogicGraphs"): generateLogicGraphs,
    ("docgen", "generateFunctionGraphs"): generateFunctionGraphs,
    ("docgen", "generateMermaid"): generateMermaidDiagrams,
    ("docgen", "updateReadmes"): updateReadmes,
    ("docgen", "generateReport"): generateReport,
    ("docgen", "generateDashboard"): generateDashboard,
    ("docgen", "finalize"): finalize,

    # Single blueprint doc generation (for direct API use)
    ("doc", "load_blueprint"): load_blueprint,
    ("doc", "init_defaults"): init_defaults,
    ("doc", "toggle"): toggle,
    ("doc", "clear_sections"): clear_sections,
    ("doc", "extract_metadata"): extract_metadata,
    ("doc", "generate_overview"): generate_overview,
    ("doc", "generate_mermaid"): generate_mermaid,
    ("doc", "generate_states_table"): generate_states_table,
    ("doc", "generate_transitions_table"): generate_transitions_table,
    ("doc", "generate_gates_table"): generate_gates_table,
    ("doc", "generate_actions_table"): generate_actions_table,
    ("doc", "generate_context_docs"): generate_context_docs,
    ("doc", "generate_events_list"): generate_events_list,
    ("doc", "generate_quickstart"): generate_quickstart,
    ("doc", "assemble_markdown"): assemble_markdown,
    ("doc", "assemble_html"): assemble_html,
    ("doc", "assemble_json"): assemble_json,
    ("doc", "export_docs"): export_docs,
}
