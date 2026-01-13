# Function Decoder

**L++ Skill** for analyzing Python scripts to extract inbound/outbound function interfaces and build modular dependency graphs.

## Purpose

While `logic_decoder` focuses on **control flow** (states/transitions), `function_decoder` focuses on **modularity** (dependencies/interfaces):

- **Inbound Interface**: Public functions/classes that this module exports
- **Outbound Dependencies**: External calls grouped by source (stdlib, pip, local)
- **Internal Call Graph**: How internal functions call each other
- **Coupling Metrics**: Fan-in, fan-out, instability index

## Usage

```bash
cd utils/function_decoder
python interactive.py
```

### Commands

| Command | Description |
|---------|-------------|
| `decode <file.py>` | Analyze a Python file |
| `show` | Display full module graph JSON |
| `graph` | Print ASCII summary of inbound/outbound |
| `visualize [files...]` | Generate stackable HTML visualization |
| `export [file]` | Export module graph to JSON |
| `reset` | Clear analysis state |
| `quit` | Exit |

### Example

```
[idle]> decode ../logic_decoder/src/decoder_compute.py
Exports: 19 | Imports: 4
Internal edges: 44

[complete]> graph

=== decoder_compute ===

INBOUND (exports):
  function     hasValue(params) -> dict
  function     loadFile(params) -> dict
  function     parseAst(params) -> dict
  ...

OUTBOUND (imports):
  [stdlib] ast: *
  [stdlib] json: *
  [stdlib] os: *
  [stdlib] typing: Any

Coupling: fanIn=19 fanOut=4 instability=0.174
```

## Output Schema

The `moduleGraph` output contains:

```json
{
  "module": "decoder_compute",
  "filePath": "/path/to/file.py",
  "inbound": [
    {"type": "function", "name": "foo", "args": ["x"], "returns": "dict"}
  ],
  "outbound": [
    {"module": "json", "category": "stdlib", "names": []}
  ],
  "nodes": [...],
  "edges": [...],
  "coupling": {
    "fanIn": 19,
    "fanOut": 4,
    "instability": 0.174,
    "internalEdges": 44
  }
}
```

## Coupling Metrics

| Metric | Formula | Interpretation |
|--------|---------|----------------|
| **Fan-In** | # of exports | How many things depend on this |
| **Fan-Out** | # of imports | How many things this depends on |
| **Instability** | Ce/(Ca+Ce) | 0 = stable, 1 = unstable |

## Cross-Script Linking

Export module graphs from multiple scripts and link them by matching:
- Script A's `outbound.localCalls` → Script B's `inbound`

This creates a project-wide function dependency graph.

## Stackable Visualization

Generate interactive HTML visualizations that stack multiple modules together:

```bash
# Visualize current decoded module
[complete]> visualize

# Stack multiple exported module graphs
[idle]> visualize module1.json module2.json module3.json
Generated: results/function_graph.html
Nodes: 79 | Edges: 131
```

Features:
- **Force-directed layout** with drag & drop
- **Horizontal/Vertical layouts** for structured views
- **Color-coded modules** for easy differentiation
- **Edge filtering** by type (internal/external/local)
- **Coupling metrics** displayed per module
- **Click to select** nodes and see connections

## State Machine

```mermaid
stateDiagram-v2
    %% L++ State Diagram: Python Function Decoder
    [*] --> idle
    idle --> parsing : DECODE [filePath is not None and le...]
    parsing --> extracting : AUTO [ast is not None]
    extracting --> tracing : AUTO [exports is not None and imp...]
    tracing --> computing : AUTO [internalCalls is not None]
    parsing --> idle : RESET
    extracting --> idle : RESET
    tracing --> idle : RESET
    computing --> idle : RESET
```
> **Interactive View:** [Open zoomable diagram](results/function_decoder_diagram.html) for pan/zoom controls


## Files

| File | Purpose |
|------|---------|
| `function_decoder.json` | L++ Blueprint |
| `src/function_decoder_compute.py` | Compute units |
| `interactive.py` | CLI wrapper |
| `tla/function_decoder.tla` | TLA+ specification |

## State Machine Visualization

Interactive state machine diagram: [function_decoder_graph.html](results/function_decoder_graph.html)

Open the HTML file in a browser for:
- Zoom/pan navigation
- Click nodes to highlight connections
- Hover for gate conditions
- Multiple layout options (hierarchical, horizontal, circular, grid)
