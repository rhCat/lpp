"""
Dashboard Compute Module
Aggregates L++ utility tools and generates an interactive dashboard HTML.
"""
import json
import os
from pathlib import Path
from collections import defaultdict


# Tool category patterns for automatic grouping
CATEGORY_PATTERNS = {
    "Blueprint Tools": ["blueprint_"],
    "Visualization": ["graph_", "diagram"],
    "Code Analysis": ["decoder", "extractor", "analyzer"],
    "Testing & Quality": ["test_", "coverage_", "linter", "compliance"],
    "Documentation": ["doc_", "readme_"],
    "Registry & Discovery": ["registry", "skill_"],
    "Orchestration": ["orchestrator", "simulator", "tracer"],
    "Research": ["research_", "scholar_"],
    "LLM Integration": ["llm_"],
    "Migration & Schema": ["migrator"],
    "Verification": ["tlaps_", "seal"]
}


def scanTools(params: dict) -> dict:
    """Scan directories for L++ tool blueprints.

    Supports scanning:
    - utils/ directory: standard tool structure (tool_name/tool_name.json)
    - src/ directory: core blueprints in src/blueprints/core_jsons/
    """
    scanPaths = params.get("scanPaths", [])
    utilsPath = params.get("utilsPath", "")

    # Backwards compatibility: single utilsPath converts to scanPaths
    if utilsPath and not scanPaths:
        scanPaths = [{"path": utilsPath, "type": "utils"}]

    if not scanPaths:
        return {"tools": [], "hasTools": False, "error": "No scan paths provided"}

    tools = []

    for scanConfig in scanPaths:
        scanPath = scanConfig.get("path", "")
        scanType = scanConfig.get("type", "utils")

        if not scanPath or not os.path.isdir(scanPath):
            continue

        if scanType == "src":
            # Scan src/ directory - blueprints in core_jsons/
            tools.extend(_scanSrcDirectory(scanPath))
        else:
            # Scan utils/ directory - standard tool structure
            tools.extend(_scanUtilsDirectory(scanPath))

    return {"tools": tools, "hasTools": len(tools) > 0, "error": None}


def _scanUtilsDirectory(utilsPath: str) -> list:
    """Scan utils/ directory for tool blueprints."""
    tools = []

    for item in sorted(os.listdir(utilsPath)):
        toolDir = os.path.join(utilsPath, item)
        if not os.path.isdir(toolDir):
            continue

        # Skip non-tool directories
        if item.startswith("__") or item in ["results", "src"]:
            continue

        # Look for blueprint JSON (either {name}.json or blueprint.json)
        blueprintPath = None
        for jsonFile in [f"{item}.json", "blueprint.json"]:
            candidate = os.path.join(toolDir, jsonFile)
            if os.path.exists(candidate):
                blueprintPath = candidate
                break

        if not blueprintPath:
            continue

        # Build tool metadata
        toolMeta = {
            "id": item,
            "dir": toolDir,
            "blueprintPath": blueprintPath,
            "visualizations": _findVisualizations(toolDir, item),
            "simpleMmd": _findSimpleMmd(toolDir, item),
            "sourceType": "utils"
        }
        tools.append(toolMeta)

    return tools


def _scanSrcDirectory(srcPath: str) -> list:
    """Scan src/ directory for core framework blueprints."""
    tools = []

    # Core blueprints are in src/blueprints/core_jsons/
    coreJsonsPath = os.path.join(srcPath, "blueprints", "core_jsons")
    framePyPath = os.path.join(srcPath, "frame_py")

    if not os.path.isdir(coreJsonsPath):
        return tools

    for item in sorted(os.listdir(coreJsonsPath)):
        if not item.endswith("_blueprint.json"):
            continue

        blueprintPath = os.path.join(coreJsonsPath, item)
        # Extract tool ID from filename (e.g., "compiler_blueprint.json" -> "compiler")
        toolId = item.replace("_blueprint.json", "")

        # Build tool metadata
        toolMeta = {
            "id": toolId,
            "dir": framePyPath,  # Python implementation directory
            "blueprintPath": blueprintPath,
            "visualizations": _findSrcVisualizations(srcPath, toolId),
            "simpleMmd": _findSrcSimpleMmd(srcPath, toolId),
            "sourceType": "src"
        }
        tools.append(toolMeta)

    return tools


def _findSrcVisualizations(srcPath: str, toolId: str) -> dict:
    """Find visualization files for a src/ core module."""
    resultsDir = os.path.join(srcPath, "frame_py", "results")
    vizs = {
        "stateGraph": None,
        "logicGraph": None,
        "functionsGraph": None,
        "mermaidDiagram": None
    }

    if not os.path.isdir(resultsDir):
        return vizs

    # Pattern matching for visualization files
    patterns = {
        "stateGraph": [f"{toolId}_graph.html", "graph.html"],
        "logicGraph": [f"{toolId}_logic_graph.html", "logic_graph.html"],
        "functionsGraph": [f"{toolId}_functions.html", "functions.html"],
        "mermaidDiagram": [f"{toolId}_diagram.html", "diagram.html"]
    }

    for vizType, filePatterns in patterns.items():
        for pattern in filePatterns:
            candidate = os.path.join(resultsDir, pattern)
            if os.path.exists(candidate):
                vizs[vizType] = candidate
                break

    return vizs


def _findSrcSimpleMmd(srcPath: str, toolId: str) -> str:
    """Find the simplified mermaid diagram file for src/ modules."""
    resultsDir = os.path.join(srcPath, "frame_py", "results")
    if not os.path.isdir(resultsDir):
        return None

    for pattern in [f"{toolId}_simple.mmd", "simple.mmd"]:
        candidate = os.path.join(resultsDir, pattern)
        if os.path.exists(candidate):
            return candidate

    return None


def _findVisualizations(toolDir: str, toolId: str) -> dict:
    """Find visualization files for a tool."""
    resultsDir = os.path.join(toolDir, "results")
    vizs = {
        "stateGraph": None,
        "logicGraph": None,
        "functionsGraph": None,
        "mermaidDiagram": None
    }

    if not os.path.isdir(resultsDir):
        return vizs

    # Pattern matching for visualization files
    patterns = {
        "stateGraph": [f"{toolId}_graph.html", "graph.html"],
        "logicGraph": [f"{toolId}_logic_graph.html", "logic_graph.html"],
        "functionsGraph": [f"{toolId}_functions.html", "functions.html"],
        "mermaidDiagram": [f"{toolId}_diagram.html", "diagram.html"]
    }

    for vizType, filePatterns in patterns.items():
        for pattern in filePatterns:
            candidate = os.path.join(resultsDir, pattern)
            if os.path.exists(candidate):
                vizs[vizType] = candidate
                break

    return vizs


def _findSimpleMmd(toolDir: str, toolId: str) -> str:
    """Find the simplified mermaid diagram file."""
    resultsDir = os.path.join(toolDir, "results")
    if not os.path.isdir(resultsDir):
        return None

    for pattern in [f"{toolId}_simple.mmd", "simple.mmd"]:
        candidate = os.path.join(resultsDir, pattern)
        if os.path.exists(candidate):
            return candidate

    return None


def analyzeTools(params: dict) -> dict:
    """Analyze tool blueprints to extract statistics."""
    tools = params.get("tools", [])
    if not tools:
        return {"tools": tools, "statistics": {}, "error": "No tools to analyze"}

    totalStats = {
        "toolCount": len(tools),
        "totalStates": 0,
        "totalTransitions": 0,
        "totalGates": 0,
        "totalActions": 0,
        "withVisualizations": 0
    }

    analyzedTools = []
    for tool in tools:
        try:
            with open(tool["blueprintPath"], "r", encoding="utf-8") as f:
                blueprint = json.load(f)
        except Exception as e:
            tool["error"] = str(e)
            tool["stats"] = {}
            tool["blueprint"] = {}
            analyzedTools.append(tool)
            continue

        # Extract blueprint metadata
        tool["name"] = blueprint.get("name", tool["id"])
        tool["description"] = blueprint.get("description", "")
        tool["version"] = blueprint.get("version", "")
        tool["schema"] = blueprint.get("$schema", "")

        # Calculate statistics
        states = blueprint.get("states", {})
        transitions = blueprint.get("transitions", [])
        gates = blueprint.get("gates", {})
        actions = blueprint.get("actions", {})

        tool["stats"] = {
            "statesCount": len(states),
            "transitionsCount": len(transitions),
            "gatesCount": len(gates),
            "actionsCount": len(actions),
            "entryState": blueprint.get("entry_state", ""),
            "terminalStates": blueprint.get("terminal_states", [])
        }

        # Store states list for display
        tool["states"] = list(states.keys())

        # Update totals
        totalStats["totalStates"] += len(states)
        totalStats["totalTransitions"] += len(transitions)
        totalStats["totalGates"] += len(gates)
        totalStats["totalActions"] += len(actions)

        # Check visualizations
        vizCount = sum(1 for v in tool["visualizations"].values() if v)
        if vizCount > 0:
            totalStats["withVisualizations"] += 1

        # Load simple mermaid if available
        if tool.get("simpleMmd"):
            try:
                with open(tool["simpleMmd"], "r", encoding="utf-8") as f:
                    tool["mermaidContent"] = f.read()
            except:
                tool["mermaidContent"] = None
        else:
            tool["mermaidContent"] = None

        tool["blueprint"] = blueprint
        analyzedTools.append(tool)

    return {"tools": analyzedTools, "statistics": totalStats, "error": None}


def categorizeTools(params: dict) -> dict:
    """Group tools by naming patterns into categories."""
    tools = params.get("tools", [])
    if not tools:
        return {"categories": {}, "error": "No tools to categorize"}

    categories = defaultdict(list)
    categorized = set()

    # First pass: match against patterns
    for tool in tools:
        toolId = tool["id"].lower()
        matched = False

        for category, patterns in CATEGORY_PATTERNS.items():
            for pattern in patterns:
                if pattern in toolId:
                    categories[category].append(tool)
                    categorized.add(tool["id"])
                    matched = True
                    break
            if matched:
                break

    # Second pass: put uncategorized in "Other Tools"
    for tool in tools:
        if tool["id"] not in categorized:
            categories["Other Tools"].append(tool)

    # Sort categories by name, but keep "Other Tools" last
    sortedCategories = {}
    for cat in sorted(categories.keys()):
        if cat != "Other Tools":
            sortedCategories[cat] = categories[cat]
    if "Other Tools" in categories:
        sortedCategories["Other Tools"] = categories["Other Tools"]

    return {"categories": dict(sortedCategories), "error": None}


def generateDashboard(params: dict) -> dict:
    """Generate interactive dashboard HTML."""
    tools = params.get("tools", [])
    categories = params.get("categories", {})
    statistics = params.get("statistics", {})
    utilsPath = params.get("utilsPath", "")
    outputPath = params.get("outputPath", "")
    basePath = params.get("basePath", "")

    if not tools:
        return {"htmlPath": None, "hasHtml": False, "error": "No tools to display"}

    # Determine output path
    if outputPath:
        htmlPath = outputPath
    elif utilsPath:
        htmlPath = os.path.join(utilsPath, "dashboard.html")
    else:
        return {"htmlPath": None, "hasHtml": False, "error": "No output path specified"}

    html = _buildDashboardHtml(
        tools, categories, statistics, basePath or utilsPath)

    try:
        with open(htmlPath, "w", encoding="utf-8") as f:
            f.write(html)
        return {"htmlPath": htmlPath, "hasHtml": True, "error": None}
    except Exception as e:
        return {"htmlPath": None, "hasHtml": False, "error": str(e)}


def _buildDashboardHtml(tools: list, categories: dict, stats: dict, basePath: str) -> str:
    """Build the dashboard HTML with dark theme."""
    # Prepare tools JSON for client-side filtering
    toolsJson = json.dumps([
        {
            "id": t["id"],
            "name": t.get("name", t["id"]),
            "description": t.get("description", ""),
            "version": t.get("version", ""),
            "stats": t.get("stats", {}),
            "states": t.get("states", []),
            "visualizations": {
                k: os.path.relpath(v, basePath) if v else None
                for k, v in t.get("visualizations", {}).items()
            },
            "mermaidContent": t.get("mermaidContent"),
            "blueprintPath": os.path.relpath(t["blueprintPath"], basePath),
            "dir": os.path.relpath(t["dir"], basePath),
            "sourceType": t.get("sourceType", "utils")
        }
        for t in tools
    ])

    categoriesJson = json.dumps({
        cat: [t["id"] for t in catTools]
        for cat, catTools in categories.items()
    })

    statsJson = json.dumps(stats)

    return f'''<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8"/>
<title>L++ Tools Dashboard</title>
<script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
<style>
* {{ box-sizing: border-box; margin: 0; padding: 0; }}
body {{
    font-family: 'Segoe UI', Arial, sans-serif;
    background: #0f0f23;
    color: #ccc;
    min-height: 100vh;
}}

/* Header */
.header {{
    background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
    padding: 30px 40px;
    border-bottom: 1px solid #333;
}}
.header h1 {{
    color: #00d4ff;
    font-size: 32px;
    margin-bottom: 8px;
}}
.header .subtitle {{
    color: #888;
    font-size: 14px;
}}

/* Stats Bar */
.stats-bar {{
    display: flex;
    gap: 30px;
    padding: 20px 40px;
    background: #16213e;
    border-bottom: 1px solid #333;
    flex-wrap: wrap;
}}
.stat-item {{
    text-align: center;
}}
.stat-value {{
    font-size: 28px;
    font-weight: bold;
    color: #00d4ff;
}}
.stat-label {{
    font-size: 12px;
    color: #888;
    text-transform: uppercase;
}}

/* Controls */
.controls {{
    padding: 20px 40px;
    background: #1a1a2e;
    border-bottom: 1px solid #333;
    display: flex;
    gap: 20px;
    align-items: center;
    flex-wrap: wrap;
}}
.search-box {{
    flex: 1;
    min-width: 250px;
    max-width: 400px;
}}
.search-box input {{
    width: 100%;
    padding: 10px 15px;
    background: #0f0f23;
    border: 1px solid #333;
    border-radius: 6px;
    color: #fff;
    font-size: 14px;
}}
.search-box input:focus {{
    outline: none;
    border-color: #00d4ff;
}}
.filter-buttons {{
    display: flex;
    gap: 8px;
    flex-wrap: wrap;
}}
.filter-btn {{
    padding: 8px 16px;
    background: #2a2a4a;
    border: 1px solid #444;
    border-radius: 4px;
    color: #ccc;
    cursor: pointer;
    font-size: 12px;
    transition: all 0.2s;
}}
.filter-btn:hover {{
    background: #3a3a5a;
}}
.filter-btn.active {{
    background: #00d4ff;
    color: #000;
    border-color: #00d4ff;
}}

/* Main content */
.main {{
    display: flex;
    min-height: calc(100vh - 250px);
}}

/* Sidebar */
.sidebar {{
    width: 280px;
    background: #16213e;
    border-right: 1px solid #333;
    padding: 20px;
    overflow-y: auto;
    max-height: calc(100vh - 250px);
}}
.sidebar h3 {{
    color: #00d4ff;
    font-size: 14px;
    margin-bottom: 15px;
    padding-bottom: 8px;
    border-bottom: 1px solid #333;
}}
.category-item {{
    padding: 8px 12px;
    margin-bottom: 4px;
    border-radius: 4px;
    cursor: pointer;
    display: flex;
    justify-content: space-between;
    align-items: center;
    transition: background 0.2s;
}}
.category-item:hover {{
    background: #2a2a4a;
}}
.category-item.active {{
    background: #00d4ff;
    color: #000;
}}
.category-count {{
    background: #333;
    padding: 2px 8px;
    border-radius: 10px;
    font-size: 11px;
}}
.category-item.active .category-count {{
    background: rgba(0,0,0,0.3);
}}

/* Content area */
.content {{
    flex: 1;
    padding: 30px;
    overflow-y: auto;
    max-height: calc(100vh - 250px);
}}
.content h2 {{
    color: #fff;
    margin-bottom: 20px;
    font-size: 20px;
}}
.tools-grid {{
    display: grid;
    grid-template-columns: repeat(auto-fill, minmax(350px, 1fr));
    gap: 20px;
}}

/* Tool Card */
.tool-card {{
    background: #1a1a2e;
    border: 1px solid #333;
    border-radius: 8px;
    overflow: hidden;
    transition: all 0.3s;
}}
.tool-card:hover {{
    border-color: #00d4ff;
    transform: translateY(-2px);
    box-shadow: 0 4px 20px rgba(0, 212, 255, 0.1);
}}
.tool-card.expanded {{
    grid-column: span 2;
}}
.card-header {{
    padding: 15px 20px;
    background: #16213e;
    border-bottom: 1px solid #333;
    cursor: pointer;
}}
.card-title {{
    display: flex;
    justify-content: space-between;
    align-items: center;
}}
.card-title h3 {{
    color: #00d4ff;
    font-size: 16px;
    margin: 0;
}}
.card-version {{
    color: #666;
    font-size: 11px;
}}
.card-description {{
    color: #888;
    font-size: 13px;
    margin-top: 8px;
    line-height: 1.4;
}}

/* Card Stats */
.card-stats {{
    display: flex;
    gap: 15px;
    padding: 12px 20px;
    border-bottom: 1px solid #333;
    background: rgba(0, 212, 255, 0.03);
}}
.card-stat {{
    text-align: center;
}}
.card-stat-value {{
    font-size: 18px;
    font-weight: bold;
    color: #fff;
}}
.card-stat-label {{
    font-size: 10px;
    color: #666;
    text-transform: uppercase;
}}

/* Card Links */
.card-links {{
    padding: 12px 20px;
    display: flex;
    gap: 8px;
    flex-wrap: wrap;
}}
.viz-link {{
    padding: 6px 12px;
    background: #2a2a4a;
    border: 1px solid #444;
    border-radius: 4px;
    color: #ccc;
    text-decoration: none;
    font-size: 11px;
    transition: all 0.2s;
}}
.viz-link:hover {{
    background: #3a3a5a;
    border-color: #00d4ff;
    color: #00d4ff;
}}
.viz-link.disabled {{
    opacity: 0.4;
    pointer-events: none;
}}
.viz-link.state {{ border-left: 3px solid #4ecdc4; }}
.viz-link.logic {{ border-left: 3px solid #f39c12; }}
.viz-link.functions {{ border-left: 3px solid #9b59b6; }}
.viz-link.mermaid {{ border-left: 3px solid #e74c3c; }}

/* Card Details (expandable) */
.card-details {{
    display: none;
    padding: 15px 20px;
    border-top: 1px solid #333;
}}
.tool-card.expanded .card-details {{
    display: block;
}}
.detail-section {{
    margin-bottom: 15px;
}}
.detail-section h4 {{
    color: #888;
    font-size: 11px;
    text-transform: uppercase;
    margin-bottom: 8px;
}}
.states-list {{
    display: flex;
    flex-wrap: wrap;
    gap: 6px;
}}
.state-tag {{
    padding: 4px 10px;
    background: #2a2a4a;
    border-radius: 12px;
    font-size: 11px;
    color: #ccc;
}}
.state-tag.entry {{ background: #00d4ff; color: #000; }}
.state-tag.terminal {{ background: #ff6b6b; color: #fff; }}

/* Mermaid Preview */
.mermaid-preview {{
    background: #0d0d1a;
    border: 1px solid #333;
    border-radius: 4px;
    padding: 15px;
    overflow-x: auto;
    margin-top: 10px;
}}
.mermaid-preview .mermaid {{
    text-align: center;
}}
.mermaid-preview svg {{
    max-width: 100%;
}}

/* Empty state */
.empty-state {{
    text-align: center;
    padding: 60px 20px;
    color: #666;
}}
.empty-state h3 {{
    margin-bottom: 10px;
    color: #888;
}}

/* Responsive */
@media (max-width: 900px) {{
    .main {{
        flex-direction: column;
    }}
    .sidebar {{
        width: 100%;
        max-height: none;
        border-right: none;
        border-bottom: 1px solid #333;
    }}
    .tools-grid {{
        grid-template-columns: 1fr;
    }}
    .tool-card.expanded {{
        grid-column: span 1;
    }}
}}
</style>
</head>
<body>
<div class="header">
    <h1>L++ Tools Dashboard</h1>
    <div class="subtitle">Interactive overview of all L++ utility blueprints and visualizations</div>
</div>

<div class="stats-bar" id="stats-bar"></div>

<div class="controls">
    <div class="search-box">
        <input type="text" id="search-input" placeholder="Search tools by name or description..." oninput="filterTools()">
    </div>
    <div class="filter-buttons">
        <button class="filter-btn active" data-filter="all" onclick="setFilter('all')">All Tools</button>
        <button class="filter-btn" data-filter="with-viz" onclick="setFilter('with-viz')">With Visualizations</button>
        <button class="filter-btn" data-filter="blueprint" onclick="setFilter('blueprint')">Blueprint Tools</button>
    </div>
</div>

<div class="main">
    <div class="sidebar">
        <h3>Categories</h3>
        <div id="categories-list"></div>
    </div>
    <div class="content">
        <h2 id="content-title">All Tools</h2>
        <div class="tools-grid" id="tools-grid"></div>
    </div>
</div>

<script>
// Initialize mermaid
mermaid.initialize({{
    startOnLoad: false,
    theme: 'dark',
    themeVariables: {{
        primaryColor: '#16213e',
        primaryTextColor: '#fff',
        primaryBorderColor: '#333',
        lineColor: '#00d4ff',
        secondaryColor: '#1a1a2e',
        tertiaryColor: '#0f0f23'
    }}
}});

// Data from Python
const tools = {toolsJson};
const categories = {categoriesJson};
const stats = {statsJson};

// Current state
let currentFilter = 'all';
let currentCategory = null;
let searchQuery = '';
let expandedCards = new Set();

// Render stats bar
function renderStats() {{
    const bar = document.getElementById('stats-bar');
    bar.innerHTML = `
        <div class="stat-item">
            <div class="stat-value">${{stats.toolCount || 0}}</div>
            <div class="stat-label">Total Tools</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">${{stats.totalStates || 0}}</div>
            <div class="stat-label">States</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">${{stats.totalTransitions || 0}}</div>
            <div class="stat-label">Transitions</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">${{stats.totalGates || 0}}</div>
            <div class="stat-label">Gates</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">${{stats.totalActions || 0}}</div>
            <div class="stat-label">Actions</div>
        </div>
        <div class="stat-item">
            <div class="stat-value">${{stats.withVisualizations || 0}}</div>
            <div class="stat-label">With Visualizations</div>
        </div>
    `;
}}

// Render categories sidebar
function renderCategories() {{
    const list = document.getElementById('categories-list');
    list.innerHTML = `
        <div class="category-item ${{currentCategory === null ? 'active' : ''}}" onclick="selectCategory(null)">
            <span>All Tools</span>
            <span class="category-count">${{tools.length}}</span>
        </div>
    `;

    Object.entries(categories).forEach(([cat, toolIds]) => {{
        list.innerHTML += `
            <div class="category-item ${{currentCategory === cat ? 'active' : ''}}" onclick="selectCategory('${{cat}}')">
                <span>${{cat}}</span>
                <span class="category-count">${{toolIds.length}}</span>
            </div>
        `;
    }});
}}

// Render tools grid
function renderTools() {{
    const grid = document.getElementById('tools-grid');
    const title = document.getElementById('content-title');

    let filteredTools = tools;

    // Apply category filter
    if (currentCategory) {{
        const catToolIds = categories[currentCategory] || [];
        filteredTools = filteredTools.filter(t => catToolIds.includes(t.id));
        title.textContent = currentCategory;
    }} else {{
        title.textContent = 'All Tools';
    }}

    // Apply search filter
    if (searchQuery) {{
        const q = searchQuery.toLowerCase();
        filteredTools = filteredTools.filter(t =>
            t.name.toLowerCase().includes(q) ||
            t.description.toLowerCase().includes(q) ||
            t.id.toLowerCase().includes(q)
        );
    }}

    // Apply type filter
    if (currentFilter === 'with-viz') {{
        filteredTools = filteredTools.filter(t =>
            Object.values(t.visualizations).some(v => v !== null)
        );
    }} else if (currentFilter === 'blueprint') {{
        filteredTools = filteredTools.filter(t => t.id.includes('blueprint'));
    }}

    if (filteredTools.length === 0) {{
        grid.innerHTML = `
            <div class="empty-state">
                <h3>No tools found</h3>
                <p>Try adjusting your search or filters</p>
            </div>
        `;
        return;
    }}

    grid.innerHTML = filteredTools.map(tool => renderToolCard(tool)).join('');

    // Initialize mermaid for expanded cards
    expandedCards.forEach(id => {{
        const card = document.querySelector(`[data-tool-id="${{id}}"]`);
        if (card && card.classList.contains('expanded')) {{
            initMermaid(id);
        }}
    }});
}}

function renderToolCard(tool) {{
    const isExpanded = expandedCards.has(tool.id);
    const stats = tool.stats || {{}};
    const vizs = tool.visualizations || {{}};

    return `
        <div class="tool-card ${{isExpanded ? 'expanded' : ''}}" data-tool-id="${{tool.id}}">
            <div class="card-header" onclick="toggleCard('${{tool.id}}')">
                <div class="card-title">
                    <h3>${{tool.name}}</h3>
                    <span class="card-version">${{tool.version || ''}}</span>
                </div>
                <div class="card-description">${{tool.description || 'No description available'}}</div>
            </div>

            <div class="card-stats">
                <div class="card-stat">
                    <div class="card-stat-value">${{stats.statesCount || 0}}</div>
                    <div class="card-stat-label">States</div>
                </div>
                <div class="card-stat">
                    <div class="card-stat-value">${{stats.transitionsCount || 0}}</div>
                    <div class="card-stat-label">Transitions</div>
                </div>
                <div class="card-stat">
                    <div class="card-stat-value">${{stats.gatesCount || 0}}</div>
                    <div class="card-stat-label">Gates</div>
                </div>
                <div class="card-stat">
                    <div class="card-stat-value">${{stats.actionsCount || 0}}</div>
                    <div class="card-stat-label">Actions</div>
                </div>
            </div>

            <div class="card-links">
                <a class="viz-link state ${{vizs.stateGraph ? '' : 'disabled'}}"
                   href="${{vizs.stateGraph || '#'}}" target="_blank">State Graph</a>
                <a class="viz-link logic ${{vizs.logicGraph ? '' : 'disabled'}}"
                   href="${{vizs.logicGraph || '#'}}" target="_blank">Logic Graph</a>
                <a class="viz-link functions ${{vizs.functionsGraph ? '' : 'disabled'}}"
                   href="${{vizs.functionsGraph || '#'}}" target="_blank">Functions</a>
                <a class="viz-link mermaid ${{vizs.mermaidDiagram ? '' : 'disabled'}}"
                   href="${{vizs.mermaidDiagram || '#'}}" target="_blank">Mermaid</a>
            </div>

            <div class="card-details">
                <div class="detail-section">
                    <h4>States</h4>
                    <div class="states-list">
                        ${{(tool.states || []).map(s => `
                            <span class="state-tag ${{s === stats.entryState ? 'entry' : ''}} ${{(stats.terminalStates || []).includes(s) ? 'terminal' : ''}}">${{s}}</span>
                        `).join('')}}
                    </div>
                </div>

                ${{tool.mermaidContent ? `
                    <div class="detail-section">
                        <h4>State Diagram</h4>
                        <div class="mermaid-preview">
                            <pre class="mermaid" id="mermaid-${{tool.id}}">${{escapeHtml(tool.mermaidContent)}}</pre>
                        </div>
                    </div>
                ` : ''}}

                <div class="detail-section">
                    <h4>Files</h4>
                    <div style="font-size: 11px; color: #666;">
                        <div>Blueprint: <a href="${{tool.blueprintPath}}" target="_blank" style="color: #00d4ff;">${{tool.blueprintPath}}</a></div>
                        <div>Directory: ${{tool.dir}}</div>
                    </div>
                </div>
            </div>
        </div>
    `;
}}

function escapeHtml(str) {{
    if (!str) return '';
    return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}}

function toggleCard(toolId) {{
    if (expandedCards.has(toolId)) {{
        expandedCards.delete(toolId);
    }} else {{
        expandedCards.add(toolId);
        setTimeout(() => initMermaid(toolId), 100);
    }}
    renderTools();
}}

function initMermaid(toolId) {{
    const elem = document.getElementById(`mermaid-${{toolId}}`);
    if (elem && !elem.dataset.processed) {{
        elem.dataset.processed = 'true';
        try {{
            mermaid.init(undefined, elem);
        }} catch(e) {{
            console.warn('Mermaid init failed for', toolId, e);
        }}
    }}
}}

function selectCategory(cat) {{
    currentCategory = cat;
    renderCategories();
    renderTools();
}}

function setFilter(filter) {{
    currentFilter = filter;
    document.querySelectorAll('.filter-btn').forEach(btn => {{
        btn.classList.toggle('active', btn.dataset.filter === filter);
    }});
    renderTools();
}}

function filterTools() {{
    searchQuery = document.getElementById('search-input').value;
    renderTools();
}}

// Initialize
renderStats();
renderCategories();
renderTools();
</script>
</body>
</html>'''


# Compute registry for L++ dispatcher
COMPUTE_REGISTRY = {
    "dashboard:scanTools": scanTools,
    "dashboard:analyzeTools": analyzeTools,
    "dashboard:categorizeTools": categorizeTools,
    "dashboard:generateDashboard": generateDashboard
}
