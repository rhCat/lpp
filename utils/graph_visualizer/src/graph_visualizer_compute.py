"""
Graph Visualizer Compute Module
Generates interactive HTML/SVG state machine diagrams from L++ blueprints.
Uses hierarchical/flowchart layout for easy system flow review.
"""
import json
from collections import defaultdict, deque


def process(params: dict) -> dict:
    """
    Generate an interactive HTML visualization of an L++ blueprint.
    
    Args:
        params: dict with 'blueprint' (JSON string) and optional 'html_path'
        
    Returns:
        dict with 'has_html', 'html_path', and optional 'error'
    """
    blueprint_str = params.get("blueprint", "")
    html_path = params.get("html_path", "graph_visualizer.html")
    
    try:
        blueprint = json.loads(blueprint_str)
    except Exception as e:
        return {"has_html": False, "error": f"Invalid JSON: {e}"}
    
    # L++ schema: states is a dict {name: {description: ...}}
    states_dict = blueprint.get("states", {})
    transitions = blueprint.get("transitions", [])
    gates_dict = blueprint.get("gates", {})
    entry_state = blueprint.get("entry_state", "")
    terminal_states = blueprint.get("terminal_states", [])
    skill_name = blueprint.get("name", blueprint.get("id", "L++ Skill"))
    
    # Collect valid node IDs
    valid_node_ids = set(states_dict.keys())
    
    # Build adjacency for layer calculation
    adjacency = defaultdict(set)
    back_adjacency = defaultdict(set)
    
    links = []
    for t in transitions:
        if isinstance(t, dict):
            from_state = t.get("from", "")
            to_state = t.get("to", "")
            event = t.get("on_event", "")
            gate_list = t.get("gates", [])
            gate_str = ", ".join(gate_list) if gate_list else ""
            
            # Skip invalid to_state
            if to_state == "*" or to_state not in valid_node_ids:
                continue
            
            # Expand wildcard from_state to all valid states
            if from_state == "*":
                source_states = [s for s in valid_node_ids if s != to_state]
            elif from_state not in valid_node_ids:
                continue
            else:
                source_states = [from_state]
            
            for src in source_states:
                adjacency[src].add(to_state)
                back_adjacency[to_state].add(src)
                links.append({
                    "source": src, 
                    "target": to_state, 
                    "label": event,
                    "gates": gate_str
                })
    
    # Calculate layers using BFS from entry state
    layers = _calculate_layers(entry_state, adjacency, valid_node_ids, terminal_states)
    
    nodes = []
    for state_id, state_info in states_dict.items():
        desc = state_info.get("description", "") if isinstance(state_info, dict) else str(state_info)
        is_entry = state_id == entry_state
        is_terminal = state_id in terminal_states
        layer = layers.get(state_id, 5)  # Default middle layer
        nodes.append({
            "id": state_id, 
            "label": state_id,
            "description": desc,
            "type": "state",
            "isEntry": is_entry,
            "isTerminal": is_terminal,
            "layer": layer
        })
    
    # Build the HTML
    html_content = _build_html(skill_name, nodes, links)
    
    try:
        with open(html_path, "w", encoding="utf-8") as f:
            f.write(html_content)
    except Exception as e:
        return {"has_html": False, "error": f"Failed to write HTML: {e}"}
    
    return {"has_html": True, "html_path": html_path}


def _calculate_layers(entry_state: str, adjacency: dict, all_states: set, terminal_states: list) -> dict:
    """Calculate hierarchical layers for states using BFS from entry."""
    layers = {}
    if not entry_state or entry_state not in all_states:
        # Fallback: assign all to layer 0
        return {s: 0 for s in all_states}
    
    # BFS from entry
    queue = deque([(entry_state, 0)])
    visited = {entry_state}
    layers[entry_state] = 0
    
    while queue:
        state, layer = queue.popleft()
        for next_state in adjacency.get(state, []):
            if next_state not in visited:
                visited.add(next_state)
                layers[next_state] = layer + 1
                queue.append((next_state, layer + 1))
    
    # Assign unvisited states to a middle layer
    max_layer = max(layers.values()) if layers else 0
    for s in all_states:
        if s not in layers:
            layers[s] = max_layer // 2 + 1
    
    # Push terminal states to last layer
    if terminal_states:
        max_layer = max(layers.values())
        for ts in terminal_states:
            if ts in layers:
                layers[ts] = max_layer + 1
    
    return layers


def _build_html(title: str, nodes: list, links: list) -> str:
    """Build the interactive D3.js HTML visualization with hierarchical layout."""
    nodes_json = json.dumps(nodes)
    links_json = json.dumps(links)
    
    return f'''<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8"/>
<title>{title} - State Machine</title>
<script src="https://d3js.org/d3.v7.min.js"></script>
<style>
body {{ font-family: Arial, sans-serif; margin: 0; padding: 20px; background: #1a1a2e; color: #eee; }}
h1 {{ color: #00d4ff; margin-bottom: 10px; }}
#container {{ display: flex; gap: 20px; }}
#graph {{ flex: 1; overflow: auto; }}
#info {{ width: 320px; background: #16213e; padding: 15px; border-radius: 8px; max-height: 90vh; overflow-y: auto; }}
svg {{ background: #0f0f23; border-radius: 8px; }}
.node {{ cursor: pointer; }}
.node-rect {{ rx: 8; ry: 8; }}
.node-label {{ font-size: 12px; fill: #fff; text-anchor: middle; pointer-events: none; font-weight: bold; }}
.node-desc {{ font-size: 9px; fill: #aaa; text-anchor: middle; pointer-events: none; }}
.link {{ stroke-opacity: 0.7; fill: none; }}
.link-label {{ font-size: 8px; fill: #888; pointer-events: none; }}
.gate-label {{ font-size: 7px; fill: #666; pointer-events: none; font-style: italic; }}
#tooltip {{ position: absolute; background: #16213e; border: 1px solid #00d4ff; padding: 10px; border-radius: 4px; pointer-events: none; display: none; max-width: 350px; z-index: 100; font-size: 12px; }}
.controls {{ margin-bottom: 10px; }}
.controls button {{ background: #00d4ff; color: #000; border: none; padding: 8px 16px; margin-right: 5px; cursor: pointer; border-radius: 4px; }}
.controls button:hover {{ background: #00a8cc; }}
.legend {{ margin-top: 20px; }}
.legend-item {{ display: flex; align-items: center; margin: 5px 0; font-size: 12px; }}
.legend-color {{ width: 20px; height: 20px; border-radius: 4px; margin-right: 10px; }}
h3, h4 {{ margin: 10px 0 5px 0; color: #00d4ff; }}
#details {{ font-size: 12px; line-height: 1.5; }}
#flow-list {{ font-size: 11px; max-height: 300px; overflow-y: auto; }}
#flow-list div {{ padding: 3px 0; border-bottom: 1px solid #333; }}
</style>
</head>
<body>
<h1>{title}</h1>
<div class="controls">
  <button onclick="resetZoom()">Reset View</button>
  <button onclick="centerGraph()">Center</button>
  <button onclick="fitToView()">Fit</button>
  <button id="btn-upstream" onclick="toggleUpstream()" style="background:#00d4ff">Show Upstream</button>
  <span style="margin-left:20px; color:#888">Layout:</span>
  <button onclick="setLayout('hierarchical')" id="btn-hierarchical" style="background:#00d4ff">Hierarchical</button>
  <button onclick="setLayout('horizontal')" id="btn-horizontal">Horizontal</button>
  <button onclick="setLayout('circular')" id="btn-circular">Circular</button>
  <button onclick="setLayout('grid')" id="btn-grid">Grid</button>
</div>
<div id="container">
  <div id="graph"><svg></svg></div>
  <div id="info">
    <h3>Selected Node</h3>
    <div id="details">Click a node to see details</div>
    <h4>Transitions</h4>
    <div id="flow-list"></div>
    <div class="legend">
      <h4>Legend</h4>
      <div class="legend-item"><div class="legend-color" style="background:#00d4ff"></div> Entry State</div>
      <div class="legend-item"><div class="legend-color" style="background:#ff6b6b"></div> Terminal State</div>
      <div class="legend-item"><div class="legend-color" style="background:#4a4a8a"></div> Normal State</div>
      <div class="legend-item"><div class="legend-color" style="background:#ffa500"></div> Error State</div>
    </div>
  </div>
</div>
<div id="tooltip"></div>
<script>
const nodes = {nodes_json};
const links = {links_json};

// Calculate layout dimensions based on layers
const layerMap = {{}};
nodes.forEach(n => {{
    if (!layerMap[n.layer]) layerMap[n.layer] = [];
    layerMap[n.layer].push(n);
}});
const numLayers = Object.keys(layerMap).length;
const maxNodesInLayer = Math.max(...Object.values(layerMap).map(l => l.length));

const nodeWidth = 140;
const nodeHeight = 50;
const layerGap = 120;
const nodeGap = 30;

const width = Math.max(1200, maxNodesInLayer * (nodeWidth + nodeGap) + 100);
const height = Math.max(700, numLayers * layerGap + 150);

// Layout functions
let currentLayout = 'hierarchical';

function layoutHierarchical() {{
    Object.keys(layerMap).sort((a,b) => a-b).forEach((layer, layerIdx) => {{
        const nodesInLayer = layerMap[layer];
        const totalWidth = nodesInLayer.length * nodeWidth + (nodesInLayer.length - 1) * nodeGap;
        const startX = (width - totalWidth) / 2;
        nodesInLayer.forEach((node, idx) => {{
            node.x = startX + idx * (nodeWidth + nodeGap) + nodeWidth / 2;
            node.y = 60 + layerIdx * layerGap + nodeHeight / 2;
        }});
    }});
}}

function layoutHorizontal() {{
    // Left-to-right flow based on layers
    Object.keys(layerMap).sort((a,b) => a-b).forEach((layer, layerIdx) => {{
        const nodesInLayer = layerMap[layer];
        const totalHeight = nodesInLayer.length * nodeHeight + (nodesInLayer.length - 1) * nodeGap;
        const startY = (height - totalHeight) / 2;
        nodesInLayer.forEach((node, idx) => {{
            node.x = 100 + layerIdx * (nodeWidth + layerGap);
            node.y = startY + idx * (nodeHeight + nodeGap) + nodeHeight / 2;
        }});
    }});
}}

function layoutCircular() {{
    const cx = width / 2, cy = height / 2;
    const radius = Math.min(width, height) / 2 - 100;
    const n = nodes.length;
    nodes.forEach((node, i) => {{
        const angle = (2 * Math.PI * i) / n - Math.PI / 2;
        node.x = cx + radius * Math.cos(angle);
        node.y = cy + radius * Math.sin(angle);
    }});
}}

function layoutGrid() {{
    const cols = Math.ceil(Math.sqrt(nodes.length));
    const cellW = nodeWidth + nodeGap * 2;
    const cellH = nodeHeight + layerGap;
    const startX = (width - cols * cellW) / 2 + cellW / 2;
    const startY = 80;
    nodes.forEach((node, i) => {{
        const col = i % cols;
        const row = Math.floor(i / cols);
        node.x = startX + col * cellW;
        node.y = startY + row * cellH;
    }});
}}

function setLayout(layout) {{
    currentLayout = layout;
    // Update button styles
    ['hierarchical', 'horizontal', 'circular', 'grid'].forEach(l => {{
        document.getElementById('btn-' + l).style.background = l === layout ? '#00d4ff' : '#4a4a8a';
    }});
    // Apply layout
    if (layout === 'hierarchical') layoutHierarchical();
    else if (layout === 'horizontal') layoutHorizontal();
    else if (layout === 'circular') layoutCircular();
    else if (layout === 'grid') layoutGrid();
    // Update node positions with animation
    node.transition().duration(500).attr("transform", d => `translate(${{d.x - nodeWidth/2}},${{d.y - nodeHeight/2}})`);
    // Update links
    setTimeout(updateLinks, 50);
    setTimeout(updateLinks, 250);
    setTimeout(updateLinks, 500);
}}

// Initial hierarchical layout
layoutHierarchical();

// Create node lookup
const nodeById = {{}};
nodes.forEach(n => nodeById[n.id] = n);

// Build adjacency maps for upstream tracing
const outgoing = {{}};  // node -> [links going out]
const incoming = {{}};  // node -> [links coming in]
nodes.forEach(n => {{ outgoing[n.id] = []; incoming[n.id] = []; }});

// Resolve link sources/targets to node objects
links.forEach(l => {{
    l.sourceNode = nodeById[l.source] || nodeById[l.source.id];
    l.targetNode = nodeById[l.target] || nodeById[l.target.id];
    if (l.sourceNode && l.targetNode) {{
        outgoing[l.sourceNode.id].push(l);
        incoming[l.targetNode.id].push(l);
    }}
}});

// Function to trace all upstream paths
function traceUpstream(nodeId, visited = new Set()) {{
    if (visited.has(nodeId)) return [];
    visited.add(nodeId);
    const paths = [];
    incoming[nodeId].forEach(link => {{
        const srcId = link.sourceNode.id;
        if (srcId !== nodeId) {{  // skip self-loops
            paths.push({{ from: srcId, to: nodeId, event: link.label, gates: link.gates }});
            paths.push(...traceUpstream(srcId, visited));
        }}
    }});
    return paths;
}}

const svg = d3.select("svg").attr("width", width).attr("height", height);
const g = svg.append("g");

const zoom = d3.zoom().scaleExtent([0.2, 3]).on("zoom", (e) => g.attr("transform", e.transform));
svg.call(zoom);

// Arrow markers
const defs = svg.append("defs");
defs.append("marker")
    .attr("id", "arrow").attr("viewBox", "0 -5 10 10").attr("refX", 10).attr("refY", 0)
    .attr("markerWidth", 8).attr("markerHeight", 8).attr("orient", "auto")
  .append("path").attr("d", "M0,-4L10,0L0,4").attr("fill", "#666");
defs.append("marker")
    .attr("id", "arrow-upstream").attr("viewBox", "0 -5 10 10").attr("refX", 10).attr("refY", 0)
    .attr("markerWidth", 8).attr("markerHeight", 8).attr("orient", "auto")
  .append("path").attr("d", "M0,-4L10,0L0,4").attr("fill", "#ff00ff");

// Function to update link paths
function updateLinks() {{
    link.attr("d", d => {{
        if (!d.sourceNode || !d.targetNode) return "";
        const sx = d.sourceNode.x, sy = d.sourceNode.y + nodeHeight/2;
        const tx = d.targetNode.x, ty = d.targetNode.y - nodeHeight/2;
        // Self-loop
        if (d.sourceNode.id === d.targetNode.id) {{
            return `M${{sx + nodeWidth/2}},${{sy - nodeHeight/2}} C${{sx + nodeWidth/2 + 50}},${{sy - 30}} ${{sx + nodeWidth/2 + 50}},${{sy + 30}} ${{sx + nodeWidth/2}},${{sy + nodeHeight/2 - 10}}`;
        }}
        // Curved path
        const midY = (sy + ty) / 2;
        return `M${{sx}},${{sy}} C${{sx}},${{midY}} ${{tx}},${{midY}} ${{tx}},${{ty}}`;
    }});
}}

// Draw links with curved paths
const link = g.append("g").selectAll("path").data(links).join("path")
    .attr("class", "link")
    .attr("stroke", l => l.gates && l.gates.includes("error") ? "#ff6b6b" : "#556")
    .attr("stroke-width", 2)
    .attr("marker-end", "url(#arrow)");
updateLinks();

// Drag behavior for nodes
const drag = d3.drag()
    .on("start", function(e, d) {{
        d3.select(this).raise().select("rect").attr("stroke", "#ff0").attr("stroke-width", 4);
    }})
    .on("drag", function(e, d) {{
        d.x = e.x + nodeWidth/2;
        d.y = e.y + nodeHeight/2;
        d3.select(this).attr("transform", `translate(${{e.x}},${{e.y}})`);
        updateLinks();
    }})
    .on("end", function(e, d) {{
        d3.select(this).select("rect").attr("stroke", "#fff").attr("stroke-width", 2);
    }});

// Draw nodes as rounded rectangles
const node = g.append("g").selectAll("g").data(nodes).join("g")
    .attr("class", "node")
    .attr("transform", d => `translate(${{d.x - nodeWidth/2}},${{d.y - nodeHeight/2}})`)
    .call(drag);

node.append("rect")
    .attr("class", "node-rect")
    .attr("width", nodeWidth)
    .attr("height", nodeHeight)
    .attr("fill", d => {{
        if (d.isEntry) return "#00d4ff";
        if (d.isTerminal) return "#ff6b6b";
        if (d.id === "error") return "#ffa500";
        return "#4a4a8a";
    }})
    .attr("stroke", "#fff")
    .attr("stroke-width", 2);

node.append("text")
    .attr("class", "node-label")
    .attr("x", nodeWidth/2)
    .attr("y", nodeHeight/2 - 5)
    .text(d => d.id.length > 16 ? d.id.slice(0,14) + ".." : d.id);

node.append("text")
    .attr("class", "node-desc")
    .attr("x", nodeWidth/2)
    .attr("y", nodeHeight/2 + 10)
    .text(d => {{
        if (!d.description) return "";
        return d.description.length > 22 ? d.description.slice(0,20) + ".." : d.description;
    }});

// Tooltip
const tooltip = d3.select("#tooltip");
node.on("mouseover", (e, d) => {{
    let html = "<b>" + d.id + "</b>";
    if (d.description) html += "<br><br>" + d.description;
    tooltip.style("display", "block").html(html);
}}).on("mousemove", (e) => {{
    tooltip.style("left", (e.pageX + 15) + "px").style("top", (e.pageY - 10) + "px");
}}).on("mouseout", () => tooltip.style("display", "none"));

// Track selected node for upstream view
let selectedNode = null;
let showUpstream = false;

// Click to highlight and show transitions
node.on("click", (e, d) => {{
    selectedNode = d;
    
    // Highlight selected node
    node.select("rect")
        .attr("stroke", n => n.id === d.id ? "#ff0" : "#fff")
        .attr("stroke-width", n => n.id === d.id ? 4 : 2);
    
    // Highlight connected links
    if (showUpstream) {{
        highlightUpstream(d.id);
    }} else {{
        link.attr("stroke", l => {{
            const src = l.sourceNode ? l.sourceNode.id : l.source;
            const tgt = l.targetNode ? l.targetNode.id : l.target;
            if (src === d.id) return "#00ff00";  // outgoing
            if (tgt === d.id) return "#ffaa00";  // incoming
            return "#556";
        }}).attr("stroke-width", l => {{
            const src = l.sourceNode ? l.sourceNode.id : l.source;
            const tgt = l.targetNode ? l.targetNode.id : l.target;
            return (src === d.id || tgt === d.id) ? 3 : 2;
        }}).attr("marker-end", "url(#arrow)");
    }}
    
    // Update info panel
    let info = "<b>" + d.id + "</b><br>";
    info += "<span style='color:#888'>Layer: " + d.layer + "</span><br>";
    info += d.isEntry ? "<span style='color:#00d4ff'>⬤ Entry State</span><br>" : "";
    info += d.isTerminal ? "<span style='color:#ff6b6b'>⬤ Terminal State</span><br>" : "";
    if (d.description) info += "<br>" + d.description;
    document.getElementById("details").innerHTML = info;
    
    // Show transitions
    let flowHtml = "<b style='color:#00ff00'>Outgoing →</b><br>";
    links.filter(l => (l.sourceNode ? l.sourceNode.id : l.source) === d.id).forEach(l => {{
        const tgt = l.targetNode ? l.targetNode.id : l.target;
        flowHtml += "<div>→ <b>" + tgt + "</b> [" + l.label + "]";
        if (l.gates) flowHtml += "<br><i style='color:#666;font-size:10px'>" + l.gates + "</i>";
        flowHtml += "</div>";
    }});
    flowHtml += "<br><b style='color:#ffaa00'>← Incoming</b><br>";
    links.filter(l => (l.targetNode ? l.targetNode.id : l.target) === d.id).forEach(l => {{
        const src = l.sourceNode ? l.sourceNode.id : l.source;
        flowHtml += "<div>← <b>" + src + "</b> [" + l.label + "]";
        if (l.gates) flowHtml += "<br><i style='color:#666;font-size:10px'>" + l.gates + "</i>";
        flowHtml += "</div>";
    }});
    
    // Show upstream trace
    flowHtml += "<br><b style='color:#ff00ff'>⬆ Upstream Path</b><br>";
    const upstreamPaths = traceUpstream(d.id);
    if (upstreamPaths.length === 0) {{
        flowHtml += "<div style='color:#888'>No upstream (entry point)</div>";
    }} else {{
        // Group by depth for readable output
        const seen = new Set();
        upstreamPaths.forEach(p => {{
            const key = p.from + "->" + p.to;
            if (!seen.has(key)) {{
                seen.add(key);
                flowHtml += "<div><b>" + p.from + "</b> → " + p.to + " [" + p.event + "]";
                if (p.gates) flowHtml += "<br><i style='color:#666;font-size:10px'>" + p.gates + "</i>";
                flowHtml += "</div>";
            }}
        }});
    }}
    document.getElementById("flow-list").innerHTML = flowHtml;
}});

function highlightUpstream(nodeId) {{
    const upstreamNodes = new Set([nodeId]);
    const upstreamLinks = new Set();
    
    function trace(nid) {{
        incoming[nid].forEach(link => {{
            const srcId = link.sourceNode.id;
            if (srcId !== nid && !upstreamNodes.has(srcId)) {{
                upstreamNodes.add(srcId);
                upstreamLinks.add(link);
                trace(srcId);
            }} else if (srcId !== nid) {{
                upstreamLinks.add(link);
            }}
        }});
    }}
    trace(nodeId);
    
    // Highlight upstream nodes
    node.select("rect")
        .attr("stroke", n => {{
            if (n.id === nodeId) return "#ff0";
            if (upstreamNodes.has(n.id)) return "#ff00ff";
            return "#fff";
        }})
        .attr("stroke-width", n => upstreamNodes.has(n.id) ? 3 : 2);
    
    // Highlight upstream links
    link.attr("stroke", l => {{
        if (upstreamLinks.has(l)) return "#ff00ff";
        const src = l.sourceNode ? l.sourceNode.id : l.source;
        const tgt = l.targetNode ? l.targetNode.id : l.target;
        if (src === nodeId) return "#00ff00";
        return "#556";
    }}).attr("stroke-width", l => {{
        if (upstreamLinks.has(l)) return 3;
        const src = l.sourceNode ? l.sourceNode.id : l.source;
        return src === nodeId ? 3 : 2;
    }}).attr("marker-end", l => upstreamLinks.has(l) ? "url(#arrow-upstream)" : "url(#arrow)");
}}

// Link hover for gate conditions
link.on("mouseover", (e, d) => {{
    let html = "<b>" + (d.sourceNode ? d.sourceNode.id : d.source) + " → " + (d.targetNode ? d.targetNode.id : d.target) + "</b>";
    html += "<br>Event: <b>" + d.label + "</b>";
    if (d.gates) html += "<br><br>Gates:<br><i>" + d.gates.split(", ").join("<br>") + "</i>";
    tooltip.style("display", "block").html(html);
}}).on("mousemove", (e) => {{
    tooltip.style("left", (e.pageX + 15) + "px").style("top", (e.pageY - 10) + "px");
}}).on("mouseout", () => tooltip.style("display", "none"));

function resetZoom() {{ svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity); }}
function centerGraph() {{ 
    const bounds = g.node().getBBox(); 
    const cx = bounds.x + bounds.width/2, cy = bounds.y + bounds.height/2;
    svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity.translate(width/2 - cx, height/2 - cy)); 
}}
function fitToView() {{
    const bounds = g.node().getBBox();
    const fullWidth = svg.attr("width"), fullHeight = svg.attr("height");
    const scale = Math.min(fullWidth / bounds.width, fullHeight / bounds.height) * 0.9;
    const tx = (fullWidth - bounds.width * scale) / 2 - bounds.x * scale;
    const ty = (fullHeight - bounds.height * scale) / 2 - bounds.y * scale;
    svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
}}
function toggleUpstream() {{
    showUpstream = !showUpstream;
    document.getElementById("btn-upstream").style.background = showUpstream ? "#ff00ff" : "#00d4ff";
    document.getElementById("btn-upstream").textContent = showUpstream ? "Upstream: ON" : "Show Upstream";
    if (selectedNode) {{
        if (showUpstream) {{
            highlightUpstream(selectedNode.id);
        }} else {{
            // Reset to normal highlighting
            node.select("rect").attr("stroke", n => n.id === selectedNode.id ? "#ff0" : "#fff").attr("stroke-width", n => n.id === selectedNode.id ? 4 : 2);
            link.attr("stroke", l => {{
                const src = l.sourceNode ? l.sourceNode.id : l.source;
                const tgt = l.targetNode ? l.targetNode.id : l.target;
                if (src === selectedNode.id) return "#00ff00";
                if (tgt === selectedNode.id) return "#ffaa00";
                return "#556";
            }}).attr("stroke-width", l => {{
                const src = l.sourceNode ? l.sourceNode.id : l.source;
                const tgt = l.targetNode ? l.targetNode.id : l.target;
                return (src === selectedNode.id || tgt === selectedNode.id) ? 3 : 2;
            }}).attr("marker-end", "url(#arrow)");
        }}
    }}
}}

// Auto-fit on load
fitToView();
</script>
</body>
</html>'''


COMPUTE_UNITS = {"process": process}
