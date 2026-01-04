# Documentation Generator

L++ tool for generating all documentation artifacts for L++ blueprints.

**Version:** 1.0.0  
**Schema:** L++ v0.1.2

## Overview

The Documentation Generator consolidates all documentation generation into a single L++ tool with a simple deployment script. It generates:

- **Graph Visualizations** - Interactive HTML state machine diagrams
- **Logic Graphs** - Decoded from Python source code
- **Function Graphs** - Function dependency visualizations
- **Mermaid Diagrams** - Both detailed and simplified versions
- **README Updates** - Embeds Mermaid diagrams in READMEs
- **Analysis Reports** - Aggregate statistics across all tools
- **Dashboard** - Interactive HTML dashboard

## Usage

### Quick Deploy (Recommended)

From the project root:

```bash
./deploy.sh              # Generate all documentation
./deploy.sh mermaid      # Generate only Mermaid diagrams
./deploy.sh dashboard    # Generate only dashboard
./deploy.sh clean        # Remove generated artifacts
```

### Direct CLI

```bash
cd utils/doc_generator
python interactive.py --all          # Generate everything
python interactive.py --graphs       # Only HTML graphs
python interactive.py --mermaid      # Only Mermaid diagrams
python interactive.py --readme       # Only update READMEs
```

## State Diagram

```mermaid
stateDiagram-v2
    %% L++ State Diagram: Documentation Generator
    [*] --> idle
    idle --> idle : START
    idle --> discovering : GENERATE
    discovering --> generating_graphs : DONE [blueprints is not None and ... && options.get('graphs') or op... && error is None]
    discovering --> generating_mermaid : DONE [blueprints is not None and ... && options.get('mermaid') or o... && error is None]
    discovering --> error : DONE [blueprints is None or len(b...]
    generating_graphs --> generating_logic : DONE [options.get('logic') or opt... && error is None]
    generating_graphs --> generating_mermaid : DONE [options.get('mermaid') or o... && error is None]
    generating_logic --> generating_functions : DONE [options.get('functions') or... && error is None]
    generating_logic --> generating_mermaid : DONE [options.get('mermaid') or o... && error is None]
    generating_functions --> generating_mermaid : DONE [options.get('mermaid') or o... && error is None]
    generating_mermaid --> updating_readmes : DONE [options.get('readme') or op... && error is None]
    generating_mermaid --> generating_report : DONE [options.get('report') or op... && error is None]
    updating_readmes --> generating_report : DONE [options.get('report') or op... && error is None]
    updating_readmes --> generating_dashboard : DONE [options.get('dashboard') or... && error is None]
    generating_report --> generating_dashboard : DONE [options.get('dashboard') or... && error is None]
    generating_report --> complete : DONE [error is None]
    generating_dashboard --> complete : DONE [error is None]
    idle --> error : ERROR [error is not None]
    discovering --> error : ERROR [error is not None]
    generating_graphs --> error : ERROR [error is not None]
    generating_mermaid --> error : ERROR [error is not None]
    generating_logic --> error : ERROR [error is not None]
    generating_report --> error : ERROR [error is not None]
    updating_readmes --> error : ERROR [error is not None]
    generating_functions --> error : ERROR [error is not None]
    complete --> error : ERROR [error is not None]
    generating_dashboard --> error : ERROR [error is not None]
    error --> idle : RESET
    complete --> idle : RESET
    complete --> [*]
    error --> [*]
```

## Compute Units

| Unit | Description |
|------|-------------|
| `docgen:init` | Initialize generator state |
| `docgen:discoverBlueprints` | Scan utils/ for blueprints |
| `docgen:generateGraphs` | Generate HTML graph visualizations |
| `docgen:generateLogicGraphs` | Generate logic graphs from Python |
| `docgen:generateFunctionGraphs` | Generate function dependency graphs |
| `docgen:generateMermaid` | Generate Mermaid diagrams (3 versions) |
| `docgen:updateReadmes` | Update README files with diagrams |
| `docgen:generateReport` | Generate analysis report |
| `docgen:generateDashboard` | Generate dashboard HTML |
| `docgen:finalize` | Return generation summary |

## Output Locations

| Artifact | Location |
|----------|----------|
| Graph HTML | `utils/<tool>/results/<tool>_graph.html` |
| Logic Graph | `utils/<tool>/results/<tool>_logic_graph.html` |
| Function Graph | `utils/<tool>/results/<tool>_functions.html` |
| Mermaid (detailed) | `utils/<tool>/results/<tool>.mmd` |
| Mermaid (simple) | `utils/<tool>/results/<tool>_simple.mmd` |
| Mermaid (zoomable) | `utils/<tool>/results/<tool>_diagram.html` |
| Analysis Report | `utils/analysis_report.md` |
| Dashboard | `utils/dashboard.html` |
