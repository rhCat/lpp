"""
Documentation Generator Compute Module
Generates all documentation artifacts for L++ blueprints.
"""
import os
import sys
import json
import re
import subprocess
from datetime import datetime

# State for tracking generation progress
_state = {
    "blueprints": [],
    "options": {},
    "results": {"generated": 0, "errors": []},
    "error": None
}


def init(params: dict) -> dict:
    """Initialize generator state."""
    global _state
    _state = {
        "blueprints": [],
        "options": params.get("options", {"all": True}),
        "results": {"generated": 0, "errors": []},
        "error": None
    }
    return {"initialized": True}


def discoverBlueprints(params: dict) -> dict:
    """Discover all L++ blueprints in utils directory."""
    utilsPath = params.get("utilsPath", "")
    if not utilsPath:
        # Default to utils directory relative to this file
        utilsPath = os.path.dirname(os.path.dirname(os.path.dirname(
            os.path.abspath(__file__))))

    blueprints = []

    for item in sorted(os.listdir(utilsPath)):
        toolDir = os.path.join(utilsPath, item)
        if not os.path.isdir(toolDir):
            continue
        if item.startswith("__") or item in ["results", "src"]:
            continue

        # Look for blueprint JSON
        for jsonFile in [f"{item}.json", "blueprint.json"]:
            candidate = os.path.join(toolDir, jsonFile)
            if os.path.exists(candidate):
                blueprints.append({
                    "name": item,
                    "path": candidate,
                    "dir": toolDir
                })
                break

    _state["blueprints"] = blueprints
    return {
        "blueprints": blueprints,
        "count": len(blueprints),
        "error": None if blueprints else "No blueprints found"
    }


def generateGraphs(params: dict) -> dict:
    """Generate HTML graph visualizations."""
    blueprints = _state.get("blueprints", [])
    verbose = params.get("verbose", True)

    # Import graph visualizer
    graphVizPath = os.path.join(
        os.path.dirname(os.path.dirname(
            os.path.dirname(os.path.abspath(__file__)))),
        'graph_visualizer', 'src'
    )
    sys.path.insert(0, graphVizPath)

    try:
        from graph_compute import generateGraph
    except ImportError:
        return {"generated": 0, "errors": [("import", "Could not import graph_compute")]}

    generated = 0
    errors = []

    for bp_info in blueprints:
        try:
            with open(bp_info['path']) as f:
                bp = json.load(f)

            resultsDir = os.path.join(bp_info['dir'], 'results')
            os.makedirs(resultsDir, exist_ok=True)

            result = generateGraph({
                "blueprint": bp,
                "outputPath": os.path.join(resultsDir, f"{bp_info['name']}_graph.html"),
                "title": bp.get("name", bp_info['name'])
            })

            if result.get("success"):
                generated += 1
                if verbose:
                    print(f"  [GRAPH] {bp_info['name']}")
            else:
                errors.append(
                    (bp_info['name'], result.get('error', 'Unknown')))
        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    _state["results"]["generated"] += generated
    _state["results"]["errors"].extend(errors)
    return {"generated": generated, "errors": errors}


def generateLogicGraphs(params: dict) -> dict:
    """Generate logic graphs decoded from Python source."""
    blueprints = _state.get("blueprints", [])
    verbose = params.get("verbose", True)

    # Import logic decoder
    decoderPath = os.path.join(
        os.path.dirname(os.path.dirname(
            os.path.dirname(os.path.abspath(__file__)))),
        'logic_decoder', 'src'
    )
    sys.path.insert(0, decoderPath)

    try:
        from decoder_compute import COMPUTE_REGISTRY as DECODER_REGISTRY
    except ImportError:
        return {"generated": 0, "errors": [("import", "Could not import decoder_compute")]}

    generated = 0
    errors = []

    for bp_info in blueprints:
        try:
            computePath = os.path.join(
                bp_info['dir'], 'src', f"{bp_info['name']}_compute.py")
            if not os.path.exists(computePath):
                continue

            resultsDir = os.path.join(bp_info['dir'], 'results')
            os.makedirs(resultsDir, exist_ok=True)

            # Decode Python to blueprint
            DECODER_REGISTRY["decoder:init"]({"filePath": computePath})
            DECODER_REGISTRY["decoder:parseFile"]({})
            DECODER_REGISTRY["decoder:analyzeImports"]({})
            DECODER_REGISTRY["decoder:analyzeFunctions"]({})
            DECODER_REGISTRY["decoder:analyzeControlFlow"]({})
            DECODER_REGISTRY["decoder:inferStates"]({})
            DECODER_REGISTRY["decoder:inferTransitions"]({})
            DECODER_REGISTRY["decoder:inferActions"]({})
            result = DECODER_REGISTRY["decoder:generateBlueprint"]({})

            if result.get("blueprint"):
                # Generate logic graph HTML
                outputPath = os.path.join(
                    resultsDir, f"{bp_info['name']}_logic_graph.html")
                # Use graph visualizer for rendering
                graphVizPath = os.path.join(
                    os.path.dirname(os.path.dirname(
                        os.path.dirname(os.path.abspath(__file__)))),
                    'graph_visualizer', 'src'
                )
                sys.path.insert(0, graphVizPath)
                from graph_compute import generateGraph
                generateGraph({
                    "blueprint": result["blueprint"],
                    "outputPath": outputPath,
                    "title": f"{bp_info['name']} (Decoded Logic)"
                })
                generated += 1
                if verbose:
                    print(f"  [LOGIC] {bp_info['name']}")
        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    _state["results"]["generated"] += generated
    _state["results"]["errors"].extend(errors)
    return {"generated": generated, "errors": errors}


def generateFunctionGraphs(params: dict) -> dict:
    """Generate function dependency graphs."""
    blueprints = _state.get("blueprints", [])
    verbose = params.get("verbose", True)

    # Import function decoder
    funcDecoderPath = os.path.join(
        os.path.dirname(os.path.dirname(
            os.path.dirname(os.path.abspath(__file__)))),
        'function_decoder', 'src'
    )
    sys.path.insert(0, funcDecoderPath)

    try:
        from function_decoder_compute import COMPUTE_REGISTRY as FUNC_REGISTRY
    except ImportError:
        return {"generated": 0, "errors": [("import", "Could not import function_decoder_compute")]}

    generated = 0
    errors = []

    for bp_info in blueprints:
        try:
            computePath = os.path.join(
                bp_info['dir'], 'src', f"{bp_info['name']}_compute.py")
            if not os.path.exists(computePath):
                continue

            resultsDir = os.path.join(bp_info['dir'], 'results')
            os.makedirs(resultsDir, exist_ok=True)

            FUNC_REGISTRY["funcdec:init"]({"filePath": computePath})
            FUNC_REGISTRY["funcdec:parseFile"]({})
            FUNC_REGISTRY["funcdec:analyzeFunctions"]({})
            FUNC_REGISTRY["funcdec:buildDependencies"]({})
            result = FUNC_REGISTRY["funcdec:generateVisualization"]({
                "outputPath": os.path.join(resultsDir, f"{bp_info['name']}_functions.html")
            })

            if result.get("success"):
                generated += 1
                if verbose:
                    print(f"  [FUNC] {bp_info['name']}")
        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    _state["results"]["generated"] += generated
    _state["results"]["errors"].extend(errors)
    return {"generated": generated, "errors": errors}


def _buildMermaidHtml(title: str, mermaidCode: str) -> str:
    """Build interactive HTML viewer for Mermaid diagrams."""
    return f'''<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8"/>
<title>{title} - State Diagram</title>
<script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
<style>
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{ font-family: system-ui, sans-serif; background: #1a1a2e; color: #eee; }}
.header {{ background: #16213e; padding: 15px 20px; display: flex; justify-content: space-between; align-items: center; }}
.header h1 {{ font-size: 18px; color: #00d4ff; }}
.controls {{ display: flex; gap: 8px; align-items: center; }}
.controls button {{ background: #4a4a8a; color: #fff; border: none; padding: 8px 16px; cursor: pointer; border-radius: 4px; }}
.controls button:hover {{ background: #5a5a9a; }}
.zoom-info {{ color: #888; font-size: 12px; margin-left: 15px; }}
.container {{ position: relative; width: 100%; height: calc(100vh - 110px); overflow: hidden; background: #0f0f23; }}
#diagram {{ position: absolute; transform-origin: 0 0; cursor: grab; }}
#diagram:active {{ cursor: grabbing; }}
/* Legend styling */
.legend {{ background: #16213e; padding: 10px 20px; display: flex; gap: 20px; flex-wrap: wrap; border-top: 1px solid #2a2a4e; }}
.legend-item {{ display: flex; align-items: center; gap: 6px; font-size: 12px; color: #ccc; }}
.legend-icon {{ width: 20px; height: 14px; border-radius: 3px; border: 2px solid; }}
.legend-icon.entry {{ background: #e1f5fe; border-color: #01579b; }}
.legend-icon.terminal {{ background: #c8e6c9; border-color: #2e7d32; }}
.legend-icon.error {{ background: #ffcdd2; border-color: #c62828; }}
.legend-icon.gate {{ background: #fff3e0; border-color: #e65100; border-radius: 2px; transform: rotate(45deg); width: 12px; height: 12px; }}
.legend-icon.action {{ background: #e3f2fd; border-color: #1565c0; }}
.legend-icon.state {{ background: #ffffff; border-color: #6a6aaa; }}
</style>
</head>
<body>
<div class="header">
    <h1>{title}</h1>
    <div class="controls">
        <button onclick="zoomIn()">+</button>
        <button onclick="zoomOut()">-</button>
        <button onclick="resetView()">Reset</button>
        <button onclick="fitToScreen()">Fit</button>
        <span class="zoom-info" id="zoom-level">100%</span>
    </div>
</div>
<div class="container" id="container">
    <div id="diagram"><pre class="mermaid">{mermaidCode}</pre></div>
</div>
<div class="legend">
    <div class="legend-item"><span class="legend-icon entry"></span> Entry State</div>
    <div class="legend-item"><span class="legend-icon terminal"></span> Terminal State</div>
    <div class="legend-item"><span class="legend-icon error"></span> Error State</div>
    <div class="legend-item"><span class="legend-icon gate"></span> Gate (Condition)</div>
    <div class="legend-item"><span class="legend-icon action"></span> Action</div>
    <div class="legend-item"><span class="legend-icon state"></span> State</div>
</div>
<script>
mermaid.initialize({{
    startOnLoad: true,
    theme: 'base',
    securityLevel: 'loose',
    themeVariables: {{
        primaryColor: '#2d2d5a',
        primaryTextColor: '#000000',
        primaryBorderColor: '#6a6aaa',
        lineColor: '#8888aa',
        secondaryColor: '#1a1a3e',
        tertiaryColor: '#0f0f23',
        background: 'transparent',
        mainBkg: 'transparent',
        nodeBorder: '#6a6aaa',
        clusterBkg: 'transparent',
        clusterBorder: '#4a4a8a',
        titleColor: '#ccc',
        edgeLabelBackground: 'transparent',
        fontFamily: 'system-ui, sans-serif'
    }},
    flowchart: {{
        htmlLabels: true,
        curve: 'basis'
    }}
}});

// Post-render fix for text colors and backgrounds
function fixMermaidStyles() {{
    const svg = document.querySelector('.mermaid svg');
    if (!svg) return;

    // Fix all text in nodes to be black (high contrast on colored backgrounds)
    svg.querySelectorAll('.nodeLabel, .label').forEach(el => {{
        el.style.color = '#000';
        el.style.fill = '#000';
    }});
    svg.querySelectorAll('foreignObject span, foreignObject div, foreignObject p').forEach(el => {{
        el.style.color = '#000';
    }});
    svg.querySelectorAll('text').forEach(el => {{
        // Skip edge labels (keep them light for dark background)
        if (el.closest('.edgeLabel')) {{
            el.setAttribute('fill', '#ccc');
        }}
    }});
    // Fix edge labels (HTML mode) - make them visible on dark background
    svg.querySelectorAll('.edgeLabel span, .edgeLabel p, .edgeLabel div').forEach(el => {{
        el.style.color = '#ccc';
    }});

    // Fix cluster/subgraph backgrounds - make them nearly invisible
    svg.querySelectorAll('.cluster rect, .cluster polygon').forEach(el => {{
        el.setAttribute('fill', 'rgba(74, 74, 138, 0.08)');
        el.setAttribute('stroke', '#3a3a6a');
        el.setAttribute('stroke-width', '1');
    }});

    // Fix cluster/subgraph labels - target .cluster-label specifically
    // Mermaid uses: .cluster > .cluster-label > foreignObject > div > span.nodeLabel
    svg.querySelectorAll('.cluster-label').forEach(labelGroup => {{
        // Style the foreignObject and its contents
        const fo = labelGroup.querySelector('foreignObject');
        if (fo) {{
            fo.style.overflow = 'visible';
            const div = fo.querySelector('div');
            if (div) {{
                div.style.background = '#000';
                div.style.padding = '4px 10px';
                div.style.borderRadius = '4px';
                div.style.display = 'inline-block';
            }}
            fo.querySelectorAll('span, p, .nodeLabel').forEach(el => {{
                el.style.color = '#fff';
                el.style.fontWeight = 'bold';
            }});
        }}
        // Also handle SVG text elements if present
        labelGroup.querySelectorAll('text').forEach(text => {{
            text.setAttribute('fill', '#fff');
            text.setAttribute('font-weight', 'bold');
            text.style.textShadow = '0 0 4px #000, 0 0 4px #000';
            try {{
                const bbox = text.getBBox();
                if (bbox.width > 0) {{
                    const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                    rect.setAttribute('x', bbox.x - 6);
                    rect.setAttribute('y', bbox.y - 4);
                    rect.setAttribute('width', bbox.width + 12);
                    rect.setAttribute('height', bbox.height + 8);
                    rect.setAttribute('fill', '#000');
                    rect.setAttribute('rx', '4');
                    text.parentNode.insertBefore(rect, text);
                }}
            }} catch(e) {{}}
        }});
    }});
    // Fallback: Also target g.cluster > text directly (older Mermaid)
    svg.querySelectorAll('g.cluster > text').forEach(text => {{
        text.setAttribute('fill', '#fff');
        text.setAttribute('font-weight', 'bold');
        try {{
            const bbox = text.getBBox();
            if (bbox.width > 0 && !text.previousElementSibling?.matches?.('rect[fill="#000"]')) {{
                const rect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
                rect.setAttribute('x', bbox.x - 6);
                rect.setAttribute('y', bbox.y - 4);
                rect.setAttribute('width', bbox.width + 12);
                rect.setAttribute('height', bbox.height + 8);
                rect.setAttribute('fill', '#000');
                rect.setAttribute('rx', '4');
                text.parentNode.insertBefore(rect, text);
            }}
        }} catch(e) {{}}
    }});

    // Fix SVG background
    svg.style.background = 'transparent';

    // Fix edge label backgrounds
    svg.querySelectorAll('.edgeLabel rect').forEach(el => {{
        el.setAttribute('fill', 'transparent');
    }});

    // Make ALL lines/edges more visible - use broad selectors
    svg.querySelectorAll('path').forEach(el => {{
        const stroke = el.getAttribute('stroke');
        // Skip filled shapes (nodes), only style line paths
        if (!el.classList.contains('node') && stroke && stroke !== 'none') {{
            el.setAttribute('stroke', '#88aadd');
            el.setAttribute('stroke-width', '2.5');
        }}
    }});
    svg.querySelectorAll('.edgePath path, .flowchart-link, [class*="edge"] path').forEach(el => {{
        el.setAttribute('stroke', '#88aadd');
        el.setAttribute('stroke-width', '2.5');
    }});
    svg.querySelectorAll('line').forEach(el => {{
        el.setAttribute('stroke', '#88aadd');
        el.setAttribute('stroke-width', '2.5');
    }});
    // Fix marker/arrow colors - target all markers
    svg.querySelectorAll('marker path, marker polygon').forEach(el => {{
        el.setAttribute('fill', '#88aadd');
        el.setAttribute('stroke', '#88aadd');
    }});
    svg.querySelectorAll('defs marker').forEach(marker => {{
        marker.querySelectorAll('path, polygon').forEach(el => {{
            el.setAttribute('fill', '#88aadd');
        }});
    }});
}}

let scale = 1, translateX = 50, translateY = 50, isDragging = false, startX, startY;
const container = document.getElementById('container');
const diagram = document.getElementById('diagram');
function updateTransform() {{
    diagram.style.transform = `translate(${{translateX}}px, ${{translateY}}px) scale(${{scale}})`;
    document.getElementById('zoom-level').textContent = Math.round(scale * 100) + '%';
}}
function zoomIn() {{ scale = Math.min(scale * 1.2, 5); updateTransform(); }}
function zoomOut() {{ scale = Math.max(scale / 1.2, 0.1); updateTransform(); }}
function resetView() {{ scale = 1; translateX = 50; translateY = 50; updateTransform(); }}
function fitToScreen() {{
    const svg = diagram.querySelector('svg');
    if (!svg) return;
    const svgRect = svg.getBoundingClientRect();
    const containerRect = container.getBoundingClientRect();
    scale = Math.min((containerRect.width - 100) / svgRect.width * scale, (containerRect.height - 100) / svgRect.height * scale, 1.5);
    translateX = 50; translateY = 50; updateTransform();
}}
container.addEventListener('wheel', (e) => {{
    e.preventDefault();
    const rect = container.getBoundingClientRect();
    const mouseX = e.clientX - rect.left, mouseY = e.clientY - rect.top;
    const prevScale = scale;
    scale = e.deltaY < 0 ? Math.min(scale * 1.1, 5) : Math.max(scale / 1.1, 0.1);
    translateX = mouseX - (mouseX - translateX) * (scale / prevScale);
    translateY = mouseY - (mouseY - translateY) * (scale / prevScale);
    updateTransform();
}});
container.addEventListener('mousedown', (e) => {{ isDragging = true; startX = e.clientX - translateX; startY = e.clientY - translateY; }});
document.addEventListener('mousemove', (e) => {{ if (!isDragging) return; translateX = e.clientX - startX; translateY = e.clientY - startY; updateTransform(); }});
document.addEventListener('mouseup', () => {{ isDragging = false; }});

// Run fixes after Mermaid renders
setTimeout(() => {{ fixMermaidStyles(); fitToScreen(); }}, 500);
</script>
</body>
</html>'''


def generateMermaid(params: dict) -> dict:
    """Generate Mermaid diagrams (detailed, simple, and HTML viewer)."""
    blueprints = _state.get("blueprints", [])
    verbose = params.get("verbose", True)

    # Import visualizer
    framePyPath = os.path.join(
        os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(
            os.path.abspath(__file__))))),
        'src', 'frame_py'
    )
    sys.path.insert(0, framePyPath)

    try:
        from visualizer import LppVisualizer
    except ImportError:
        return {"generated": 0, "errors": [("import", "Could not import visualizer")]}

    generated = 0
    errors = []

    for bp_info in blueprints:
        try:
            with open(bp_info['path']) as f:
                bp = json.load(f)

            viz = LppVisualizer(bp)
            resultsDir = os.path.join(bp_info['dir'], 'results')
            os.makedirs(resultsDir, exist_ok=True)

            # Detailed version
            mermaidDetailed = viz.as_mermaid_logic()
            with open(os.path.join(resultsDir, f"{bp_info['name']}.mmd"), 'w') as f:
                f.write(mermaidDetailed)

            # Simple version for README
            mermaidSimple = viz.as_mermaid_simple()
            with open(os.path.join(resultsDir, f"{bp_info['name']}_simple.mmd"), 'w') as f:
                f.write(mermaidSimple)

            # Interactive HTML viewer
            htmlContent = _buildMermaidHtml(
                bp.get('name', bp_info['name']), mermaidDetailed)
            with open(os.path.join(resultsDir, f"{bp_info['name']}_diagram.html"), 'w') as f:
                f.write(htmlContent)

            generated += 1
            if verbose:
                print(f"  [MERMAID] {bp_info['name']}")
        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    _state["results"]["generated"] += generated
    _state["results"]["errors"].extend(errors)
    return {"generated": generated, "errors": errors}


def updateReadmes(params: dict) -> dict:
    """Update README.md files with Mermaid diagrams."""
    blueprints = _state.get("blueprints", [])
    verbose = params.get("verbose", True)

    updated = 0
    errors = []

    for bp_info in blueprints:
        try:
            readmePath = os.path.join(bp_info['dir'], 'README.md')
            mermaidPath = os.path.join(
                bp_info['dir'], 'results', f"{bp_info['name']}_simple.mmd")

            if not os.path.exists(readmePath) or not os.path.exists(mermaidPath):
                continue

            with open(mermaidPath, 'r') as f:
                mermaidContent = f.read().strip()

            with open(readmePath, 'r') as f:
                readmeContent = f.read()

            # Replace mermaid block
            pattern = re.compile(
                r'(## State Diagram\s*\n+```mermaid\n)(.*?)(```)', re.DOTALL)
            if pattern.search(readmeContent):
                newReadme = pattern.sub(
                    r'\g<1>' + mermaidContent + r'\n\g<3>', readmeContent)
            else:
                simplePattern = re.compile(
                    r'(```mermaid\n)(.*?)(```)', re.DOTALL)
                if simplePattern.search(readmeContent):
                    newReadme = simplePattern.sub(
                        r'\g<1>' + mermaidContent + r'\n\g<3>', readmeContent, count=1)
                else:
                    continue

            # Add viewer link if not present
            viewerLink = f"\n> **Interactive View:** [Open zoomable diagram](results/{bp_info['name']}_diagram.html) for pan/zoom controls\n"
            if '_diagram.html' not in newReadme:
                newReadme = re.sub(r'(```mermaid\n.*?```)', r'\1' +
                                   viewerLink, newReadme, count=1, flags=re.DOTALL)

            if newReadme != readmeContent:
                with open(readmePath, 'w') as f:
                    f.write(newReadme)
                updated += 1
                if verbose:
                    print(f"  [README] {bp_info['name']}")
        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    _state["results"]["generated"] += updated
    _state["results"]["errors"].extend(errors)
    return {"updated": updated, "errors": errors}


def generateReport(params: dict) -> dict:
    """Generate analysis report."""
    utilsPath = params.get("utilsPath", "")
    if not utilsPath:
        utilsPath = os.path.dirname(os.path.dirname(
            os.path.dirname(os.path.abspath(__file__))))

    verbose = params.get("verbose", True)

    try:
        result = subprocess.run(
            [sys.executable, os.path.join(
                utilsPath, 'blueprint_analyzer', 'interactive.py')],
            capture_output=True, text=True, cwd=utilsPath
        )
        if result.returncode == 0:
            if verbose:
                print("  [REPORT] analysis_report.md")
            _state["results"]["generated"] += 1
            return {"success": True}
        else:
            return {"success": False, "error": result.stderr}
    except Exception as e:
        return {"success": False, "error": str(e)}


def generateDashboard(params: dict) -> dict:
    """Generate dashboard HTML."""
    utilsPath = params.get("utilsPath", "")
    if not utilsPath:
        utilsPath = os.path.dirname(os.path.dirname(
            os.path.dirname(os.path.abspath(__file__))))

    verbose = params.get("verbose", True)

    try:
        result = subprocess.run(
            [sys.executable, os.path.join(
                utilsPath, 'dashboard', 'interactive.py')],
            capture_output=True, text=True, cwd=utilsPath
        )
        if result.returncode == 0:
            if verbose:
                print("  [DASHBOARD] dashboard.html")
            _state["results"]["generated"] += 1
            return {"success": True}
        else:
            return {"success": False, "error": result.stderr}
    except Exception as e:
        return {"success": False, "error": str(e)}


def finalize(params: dict) -> dict:
    """Finalize generation and return summary."""
    return {
        "completed": True,
        "generated": _state["results"]["generated"],
        "errors": _state["results"]["errors"]
    }


# Compute registry for L++ dispatcher
COMPUTE_REGISTRY = {
    "docgen:init": init,
    "docgen:discoverBlueprints": discoverBlueprints,
    "docgen:generateGraphs": generateGraphs,
    "docgen:generateLogicGraphs": generateLogicGraphs,
    "docgen:generateFunctionGraphs": generateFunctionGraphs,
    "docgen:generateMermaid": generateMermaid,
    "docgen:updateReadmes": updateReadmes,
    "docgen:generateReport": generateReport,
    "docgen:generateDashboard": generateDashboard,
    "docgen:finalize": finalize,
}
