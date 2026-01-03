#!/usr/bin/env python3
"""
L++ Utils Documentation Regenerator

Regenerates all documentation artifacts for L++ utility blueprints:
- Graph visualizations (HTML)
- Logic graphs (decoded from Python source)
- Function dependency graphs
- Mermaid diagrams
- Analysis report
- README updates with embedded Mermaid diagrams

Usage:
    python utils/regenerate_docs.py [--graphs] [--logic] [--functions] [--mermaid] [--readme] [--report] [--all]
"""

import os
import sys
import json
import re
import argparse
from datetime import datetime

# Add paths for imports
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'graph_visualizer', 'src'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'logic_decoder', 'src'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'function_decoder', 'src'))
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'src', 'frame_py'))

UTILS_DIR = os.path.dirname(os.path.abspath(__file__))


def find_blueprints():
    """Find all blueprint JSON files in utils subdirectories."""
    blueprints = []
    for tool_dir in sorted(os.listdir(UTILS_DIR)):
        tool_path = os.path.join(UTILS_DIR, tool_dir)
        if not os.path.isdir(tool_path):
            continue
        json_file = os.path.join(tool_path, f'{tool_dir}.json')
        if os.path.exists(json_file):
            blueprints.append({
                'name': tool_dir,
                'path': json_file,
                'dir': tool_path
            })
    return blueprints


def find_compute_files():
    """Find all *_compute.py files in utils subdirectories."""
    compute_files = []
    for tool_dir in sorted(os.listdir(UTILS_DIR)):
        tool_path = os.path.join(UTILS_DIR, tool_dir)
        if not os.path.isdir(tool_path):
            continue
        src_dir = os.path.join(tool_path, 'src')
        if os.path.isdir(src_dir):
            # Find any *_compute.py file in the src directory
            for fname in os.listdir(src_dir):
                if fname.endswith('_compute.py'):
                    compute_files.append({
                        'name': tool_dir,
                        'path': os.path.join(src_dir, fname),
                        'dir': tool_path
                    })
                    break  # Only take the first compute file per tool
    return compute_files


def regenerate_graphs(blueprints, verbose=True):
    """Regenerate HTML graph visualizations for all blueprints."""
    try:
        from graph_visualizer_compute import process
    except ImportError:
        print("ERROR: Could not import graph_visualizer_compute")
        return 0, []

    generated = 0
    errors = []

    for bp_info in blueprints:
        try:
            with open(bp_info['path']) as f:
                bp_content = f.read()

            results_dir = os.path.join(bp_info['dir'], 'results')
            os.makedirs(results_dir, exist_ok=True)
            html_path = os.path.join(results_dir, f"{bp_info['name']}_graph.html")

            result = process({'blueprint': bp_content, 'html_path': html_path})

            if result.get('has_html'):
                generated += 1
                if verbose:
                    print(f"  [GRAPH] {bp_info['name']}")
            else:
                errors.append((bp_info['name'], result.get('error', 'Unknown error')))
        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    return generated, errors


def _build_mermaid_html(title: str, mermaid_code: str) -> str:
    """Build an interactive HTML viewer for Mermaid diagrams with pan/zoom."""
    # Escape for embedding in JS
    escaped_code = mermaid_code.replace('\\', '\\\\').replace('`', '\\`')

    return f'''<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8"/>
<title>{title} - State Diagram</title>
<script src="https://cdn.jsdelivr.net/npm/mermaid/dist/mermaid.min.js"></script>
<style>
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{ font-family: system-ui, -apple-system, sans-serif; background: #1a1a2e; color: #eee; }}
.header {{ background: #16213e; padding: 15px 20px; display: flex; justify-content: space-between; align-items: center; }}
.header h1 {{ font-size: 18px; color: #00d4ff; }}
.controls {{ display: flex; gap: 8px; }}
.controls button {{ background: #4a4a8a; color: #fff; border: none; padding: 8px 16px; cursor: pointer; border-radius: 4px; font-size: 12px; }}
.controls button:hover {{ background: #5a5a9a; }}
.zoom-info {{ color: #888; font-size: 12px; margin-left: 15px; }}
.container {{ position: relative; width: 100%; height: calc(100vh - 60px); overflow: hidden; background: #0f0f23; }}
#diagram {{ position: absolute; transform-origin: 0 0; cursor: grab; }}
#diagram:active {{ cursor: grabbing; }}
#diagram svg {{ max-width: none !important; }}
.mermaid {{ background: transparent; }}
</style>
</head>
<body>
<div class="header">
    <h1>{title}</h1>
    <div class="controls">
        <button onclick="zoomIn()">Zoom In (+)</button>
        <button onclick="zoomOut()">Zoom Out (-)</button>
        <button onclick="resetView()">Reset View</button>
        <button onclick="fitToScreen()">Fit to Screen</button>
        <span class="zoom-info" id="zoom-level">100%</span>
    </div>
</div>
<div class="container" id="container">
    <div id="diagram">
        <pre class="mermaid">
{mermaid_code}
        </pre>
    </div>
</div>
<script>
mermaid.initialize({{ startOnLoad: true, theme: 'dark', securityLevel: 'loose' }});

let scale = 1;
let translateX = 50;
let translateY = 50;
let isDragging = false;
let startX, startY;

const container = document.getElementById('container');
const diagram = document.getElementById('diagram');

function updateTransform() {{
    diagram.style.transform = `translate(${{translateX}}px, ${{translateY}}px) scale(${{scale}})`;
    document.getElementById('zoom-level').textContent = Math.round(scale * 100) + '%';
}}

function zoomIn() {{
    scale = Math.min(scale * 1.2, 5);
    updateTransform();
}}

function zoomOut() {{
    scale = Math.max(scale / 1.2, 0.1);
    updateTransform();
}}

function resetView() {{
    scale = 1;
    translateX = 50;
    translateY = 50;
    updateTransform();
}}

function fitToScreen() {{
    const svg = diagram.querySelector('svg');
    if (!svg) return;
    const svgRect = svg.getBoundingClientRect();
    const containerRect = container.getBoundingClientRect();
    const scaleX = (containerRect.width - 100) / svgRect.width * scale;
    const scaleY = (containerRect.height - 100) / svgRect.height * scale;
    scale = Math.min(scaleX, scaleY, 1.5);
    translateX = 50;
    translateY = 50;
    updateTransform();
}}

// Mouse wheel zoom
container.addEventListener('wheel', (e) => {{
    e.preventDefault();
    const rect = container.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;

    const prevScale = scale;
    if (e.deltaY < 0) scale = Math.min(scale * 1.1, 5);
    else scale = Math.max(scale / 1.1, 0.1);

    // Zoom toward mouse position
    translateX = mouseX - (mouseX - translateX) * (scale / prevScale);
    translateY = mouseY - (mouseY - translateY) * (scale / prevScale);
    updateTransform();
}});

// Pan with mouse drag
container.addEventListener('mousedown', (e) => {{
    isDragging = true;
    startX = e.clientX - translateX;
    startY = e.clientY - translateY;
    diagram.style.cursor = 'grabbing';
}});

document.addEventListener('mousemove', (e) => {{
    if (!isDragging) return;
    translateX = e.clientX - startX;
    translateY = e.clientY - startY;
    updateTransform();
}});

document.addEventListener('mouseup', () => {{
    isDragging = false;
    diagram.style.cursor = 'grab';
}});

// Keyboard shortcuts
document.addEventListener('keydown', (e) => {{
    if (e.key === '+' || e.key === '=') zoomIn();
    else if (e.key === '-') zoomOut();
    else if (e.key === '0') resetView();
    else if (e.key === 'f') fitToScreen();
}});

// Initial fit after render
setTimeout(fitToScreen, 500);
</script>
</body>
</html>'''


def regenerate_mermaid(blueprints, verbose=True):
    """Regenerate Mermaid diagrams for all blueprints.

    Generates three versions:
    - <name>.mmd: Detailed flowchart with gates/actions
    - <name>_simple.mmd: Simplified state diagram (for README)
    - <name>_diagram.html: Interactive viewer with pan/zoom
    """
    try:
        from visualizer import LppVisualizer
    except ImportError:
        print("ERROR: Could not import visualizer")
        return 0, []

    generated = 0
    errors = []

    for bp_info in blueprints:
        try:
            with open(bp_info['path']) as f:
                bp = json.load(f)

            viz = LppVisualizer(bp)

            results_dir = os.path.join(bp_info['dir'], 'results')
            os.makedirs(results_dir, exist_ok=True)

            # Generate detailed version
            mermaid_detailed = viz.as_mermaid_logic()
            detailed_path = os.path.join(results_dir, f"{bp_info['name']}.mmd")
            with open(detailed_path, 'w') as f:
                f.write(mermaid_detailed)

            # Generate simplified version for README
            mermaid_simple = viz.as_mermaid_simple()
            simple_path = os.path.join(results_dir, f"{bp_info['name']}_simple.mmd")
            with open(simple_path, 'w') as f:
                f.write(mermaid_simple)

            # Generate interactive HTML viewer with pan/zoom
            html_content = _build_mermaid_html(
                bp.get('name', bp_info['name']),
                mermaid_detailed
            )
            html_path = os.path.join(results_dir, f"{bp_info['name']}_diagram.html")
            with open(html_path, 'w') as f:
                f.write(html_content)

            generated += 1
            if verbose:
                print(f"  [MERMAID] {bp_info['name']}")
        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    return generated, errors


def regenerate_logic_graphs(compute_files, verbose=True):
    """Regenerate logic graphs by decoding Python files and visualizing."""
    try:
        import decoder_compute
        from graph_visualizer_compute import process as viz_process
    except ImportError as e:
        print(f"ERROR: Could not import required modules: {e}")
        return 0, []

    generated = 0
    errors = []

    for cf_info in compute_files:
        try:
            # Decode Python to blueprint using logic_decoder pipeline
            state = {'filePath': cf_info['path']}

            # Load and parse AST
            load_result = decoder_compute.loadFile({'filePath': cf_info['path']})
            if load_result.get('error'):
                errors.append((cf_info['name'], load_result['error']))
                continue

            state.update(load_result)

            parse_result = decoder_compute.parseAst({'sourceCode': state['sourceCode']})
            if parse_result.get('error'):
                errors.append((cf_info['name'], parse_result['error']))
                continue

            state.update(parse_result)

            # Analyze imports, functions, control flow
            imports_result = decoder_compute.analyzeImports({'ast': state['ast']})
            state.update(imports_result)

            functions_result = decoder_compute.analyzeFunctions({
                'ast': state['ast'],
                'imports': state['imports']
            })
            state.update(functions_result)

            cf_result = decoder_compute.analyzeControlFlow({
                'ast': state['ast'],
                'functions': state['functions']
            })
            state['controlFlow'] = cf_result

            # Infer states, transitions, actions
            states_result = decoder_compute.inferStates({
                'functions': state['functions'],
                'controlFlow': state['controlFlow']
            })
            state['inferredStates'] = states_result.get('states', [])

            trans_result = decoder_compute.inferTransitions({
                'controlFlow': state['controlFlow'],
                'inferredStates': state['inferredStates'],
                'functions': state['functions']
            })
            state['inferredTransitions'] = trans_result.get('transitions', [])
            state['inferredGates'] = trans_result.get('gates', [])

            actions_result = decoder_compute.inferActions({
                'functions': state['functions'],
                'imports': state['imports'],
                'controlFlow': state['controlFlow']
            })
            state['inferredActions'] = actions_result.get('actions', [])

            # Generate blueprint
            bp_result = decoder_compute.generateBlueprint({
                'filePath': cf_info['path'],
                'inferredStates': state['inferredStates'],
                'inferredTransitions': state['inferredTransitions'],
                'inferredGates': state['inferredGates'],
                'inferredActions': state['inferredActions'],
                'imports': state['imports']
            })

            blueprint_json = bp_result.get('json', '{}')

            # Generate HTML visualization
            results_dir = os.path.join(cf_info['dir'], 'results')
            os.makedirs(results_dir, exist_ok=True)
            html_path = os.path.join(results_dir, f"{cf_info['name']}_logic_graph.html")

            viz_result = viz_process({
                'blueprint': blueprint_json,
                'html_path': html_path
            })

            if viz_result.get('has_html'):
                generated += 1
                if verbose:
                    print(f"  [LOGIC] {cf_info['name']}")
            else:
                errors.append((cf_info['name'], viz_result.get('error', 'Unknown error')))

        except Exception as e:
            errors.append((cf_info['name'], str(e)))

    return generated, errors


def regenerate_function_graphs(compute_files, verbose=True):
    """Regenerate function dependency graphs using function_decoder."""
    try:
        import function_decoder_compute as fd
    except ImportError as e:
        print(f"ERROR: Could not import function_decoder_compute: {e}")
        return 0, [], []

    generated = 0
    errors = []
    all_module_graphs = []

    for cf_info in compute_files:
        try:
            # Load and parse
            load_result = fd.loadFile({'filePath': cf_info['path']})
            if load_result.get('error'):
                errors.append((cf_info['name'], load_result['error']))
                continue

            parse_result = fd.parseAst({'sourceCode': load_result['sourceCode']})
            if parse_result.get('error'):
                errors.append((cf_info['name'], parse_result['error']))
                continue

            tree = parse_result['ast']
            sourceCode = load_result['sourceCode']

            # Extract exports, imports, and trace calls
            exports_result = fd.extractExports({
                'ast': tree,
                'filePath': cf_info['path'],
                'sourceCode': sourceCode
            })
            exports = exports_result.get('exports', [])

            imports_result = fd.extractImports({'ast': tree})
            imports = imports_result.get('imports', [])

            internal_result = fd.traceInternalCalls({
                'ast': tree,
                'exports': exports
            })
            internal_calls = internal_result.get('internalCalls', [])

            external_result = fd.traceExternalCalls({
                'ast': tree,
                'imports': imports
            })
            external_calls = external_result.get('externalCalls', [])
            local_calls = external_result.get('localCalls', [])

            # Compute coupling metrics
            coupling_result = fd.computeCoupling({
                'exports': exports,
                'imports': imports,
                'internalCalls': internal_calls,
                'externalCalls': external_calls,
                'localCalls': local_calls
            })
            coupling = coupling_result.get('coupling', {})

            # Generate module graph
            graph_result = fd.generateModuleGraph({
                'filePath': cf_info['path'],
                'exports': exports,
                'imports': imports,
                'internalCalls': internal_calls,
                'externalCalls': external_calls,
                'localCalls': local_calls,
                'coupling': coupling
            })
            module_graph = graph_result.get('moduleGraph', {})
            all_module_graphs.append(module_graph)

            # Generate individual HTML visualization
            results_dir = os.path.join(cf_info['dir'], 'results')
            os.makedirs(results_dir, exist_ok=True)
            html_path = os.path.join(results_dir, f"{cf_info['name']}_functions.html")

            viz_result = fd.visualizeModuleGraph({
                'moduleGraphs': [module_graph],
                'outputPath': html_path,
                'title': f"Function Graph: {cf_info['name']}"
            })

            if viz_result.get('htmlPath'):
                generated += 1
                if verbose:
                    print(f"  [FUNC] {cf_info['name']}")
            else:
                errors.append((cf_info['name'], viz_result.get('error', 'Unknown')))

        except Exception as e:
            errors.append((cf_info['name'], str(e)))

    return generated, errors, all_module_graphs


def regenerate_combined_function_graph(all_module_graphs, verbose=True):
    """Generate a combined multi-module function dependency graph."""
    try:
        import function_decoder_compute as fd
    except ImportError:
        return False

    if not all_module_graphs:
        return False

    output_path = os.path.join(UTILS_DIR, 'function_dependencies.html')
    viz_result = fd.visualizeModuleGraph({
        'moduleGraphs': all_module_graphs,
        'outputPath': output_path,
        'title': 'L++ Utils - Combined Function Dependencies'
    })

    if viz_result.get('htmlPath'):
        if verbose:
            print("  [COMBINED] function_dependencies.html")
        return True
    return False


def regenerate_report(verbose=True):
    """Regenerate the analysis report using utils_inspection.py."""
    inspection_script = os.path.join(UTILS_DIR, 'utils_inspection.py')
    if not os.path.exists(inspection_script):
        print("ERROR: utils_inspection.py not found")
        return False

    try:
        import subprocess
        result = subprocess.run(
            [sys.executable, inspection_script],
            capture_output=True,
            text=True,
            cwd=os.path.dirname(UTILS_DIR)
        )
        if result.returncode == 0:
            if verbose:
                print("  [REPORT] analysis_report.md regenerated")
            return True
        else:
            print(f"ERROR: {result.stderr}")
            return False
    except Exception as e:
        print(f"ERROR: {e}")
        return False


def update_readmes(blueprints, verbose=True):
    """Update README.md files with simplified Mermaid diagrams."""
    updated = 0
    errors = []

    for bp_info in blueprints:
        try:
            readme_path = os.path.join(bp_info['dir'], 'README.md')
            # Use simplified version for README (easier to read)
            mermaid_path = os.path.join(
                bp_info['dir'], 'results', f"{bp_info['name']}_simple.mmd"
            )

            if not os.path.exists(readme_path):
                continue
            if not os.path.exists(mermaid_path):
                errors.append((bp_info['name'], 'No .mmd file found'))
                continue

            # Read the mermaid content
            with open(mermaid_path, 'r') as f:
                mermaid_content = f.read().strip()

            # Read the README
            with open(readme_path, 'r') as f:
                readme_content = f.read()

            # Pattern to match ```mermaid ... ``` blocks
            # We look for the State Diagram section and replace its mermaid block
            mermaid_pattern = re.compile(
                r'(## State Diagram\s*\n+```mermaid\n)(.*?)(```)',
                re.DOTALL
            )

            if mermaid_pattern.search(readme_content):
                # Replace existing mermaid block
                new_readme = mermaid_pattern.sub(
                    r'\g<1>' + mermaid_content + r'\n\g<3>',
                    readme_content
                )
            else:
                # Try simpler pattern - any mermaid block after "State Diagram"
                simple_pattern = re.compile(
                    r'(```mermaid\n)(.*?)(```)',
                    re.DOTALL
                )
                if simple_pattern.search(readme_content):
                    # Replace the first mermaid block
                    new_readme = simple_pattern.sub(
                        r'\g<1>' + mermaid_content + r'\n\g<3>',
                        readme_content,
                        count=1
                    )
                else:
                    # No mermaid block found, skip
                    continue

            # Add link to interactive viewer after the mermaid block
            viewer_link = f"\n> **Interactive View:** [Open zoomable diagram](results/{bp_info['name']}_diagram.html) for pan/zoom controls\n"
            # Check if link already exists
            if '_diagram.html' not in new_readme:
                # Add after the closing ``` of the mermaid block
                new_readme = re.sub(
                    r'(```mermaid\n.*?```)',
                    r'\1' + viewer_link,
                    new_readme,
                    count=1,
                    flags=re.DOTALL
                )

            # Only write if content changed
            if new_readme != readme_content:
                with open(readme_path, 'w') as f:
                    f.write(new_readme)
                updated += 1
                if verbose:
                    print(f"  [README] {bp_info['name']}")

        except Exception as e:
            errors.append((bp_info['name'], str(e)))

    return updated, errors


def main():
    parser = argparse.ArgumentParser(
        description='Regenerate L++ utils documentation'
    )
    parser.add_argument('--graphs', action='store_true',
                        help='Regenerate HTML graph visualizations')
    parser.add_argument('--logic', action='store_true',
                        help='Regenerate logic graphs (decoded from Python)')
    parser.add_argument('--functions', action='store_true',
                        help='Regenerate function dependency graphs')
    parser.add_argument('--mermaid', action='store_true',
                        help='Regenerate Mermaid diagrams')
    parser.add_argument('--readme', action='store_true',
                        help='Update README files with Mermaid diagrams')
    parser.add_argument('--report', action='store_true',
                        help='Regenerate analysis report')
    parser.add_argument('--all', action='store_true',
                        help='Regenerate all documentation (default if no flags)')
    parser.add_argument('-q', '--quiet', action='store_true',
                        help='Suppress individual file output')

    args = parser.parse_args()

    # Default to --all if no specific flags
    if not (args.graphs or args.logic or args.functions or args.mermaid or args.readme or args.report):
        args.all = True

    verbose = not args.quiet

    print("=" * 60)
    print("L++ Utils Documentation Regenerator")
    print(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 60)

    blueprints = find_blueprints()
    compute_files = find_compute_files()
    print(f"\nFound {len(blueprints)} blueprints, {len(compute_files)} compute files\n")

    total_generated = 0
    total_errors = []

    # Regenerate graphs
    if args.all or args.graphs:
        print("Generating HTML Graphs...")
        count, errors = regenerate_graphs(blueprints, verbose)
        total_generated += count
        total_errors.extend(errors)
        print(f"  Generated: {count} graphs\n")

    # Regenerate logic graphs
    if args.all or args.logic:
        print("Generating Logic Graphs (decoded from Python)...")
        count, errors = regenerate_logic_graphs(compute_files, verbose)
        total_generated += count
        total_errors.extend(errors)
        print(f"  Generated: {count} logic graphs\n")

    # Regenerate function graphs
    if args.all or args.functions:
        print("Generating Function Dependency Graphs...")
        count, errors, all_graphs = regenerate_function_graphs(compute_files, verbose)
        total_generated += count
        total_errors.extend(errors)
        print(f"  Generated: {count} function graphs")
        # Also generate combined view
        if regenerate_combined_function_graph(all_graphs, verbose):
            total_generated += 1
        print()

    # Regenerate Mermaid
    if args.all or args.mermaid:
        print("Generating Mermaid Diagrams...")
        count, errors = regenerate_mermaid(blueprints, verbose)
        total_generated += count
        total_errors.extend(errors)
        print(f"  Generated: {count} diagrams\n")

    # Update READMEs with Mermaid diagrams
    if args.all or args.readme:
        print("Updating README files with Mermaid diagrams...")
        count, errors = update_readmes(blueprints, verbose)
        total_generated += count
        total_errors.extend(errors)
        print(f"  Updated: {count} READMEs\n")

    # Regenerate report
    if args.all or args.report:
        print("Generating Analysis Report...")
        if regenerate_report(verbose):
            total_generated += 1
        print()

    # Summary
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"Total artifacts generated: {total_generated}")

    if total_errors:
        print(f"\nErrors ({len(total_errors)}):")
        for name, err in total_errors:
            print(f"  - {name}: {err}")

    print("\nOutput locations:")
    print("  - Graphs:       utils/<tool>/results/<tool>_graph.html")
    print("  - Logic Graphs: utils/<tool>/results/<tool>_logic_graph.html")
    print("  - Func Graphs:  utils/<tool>/results/<tool>_functions.html")
    print("  - Combined:     utils/function_dependencies.html")
    print("  - Mermaid:      utils/<tool>/results/<tool>.mmd (detailed)")
    print("  - Mermaid:      utils/<tool>/results/<tool>_simple.mmd")
    print("  - Diagram:      utils/<tool>/results/<tool>_diagram.html (zoomable)")
    print("  - READMEs:      utils/<tool>/README.md (uses simple diagram)")
    print("  - Report:       utils/analysis_report.md")

    return 0 if not total_errors else 1


if __name__ == '__main__':
    sys.exit(main())
