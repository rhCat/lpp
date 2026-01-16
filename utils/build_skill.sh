#!/bin/bash
# L++ Skill Build Pipeline
# Per build_rules.md: DRAFT -> VERIFY -> IMPLEMENT -> EXTRUDE -> DOCUMENT
#
# Usage: ./build_skill.sh <skill_dir> [options]
# Example: ./build_skill.sh llm_assistant --validate

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
SRC_DIR="$ROOT_DIR/src"

# Defaults
INT_MIN=-5
INT_MAX=5
MAX_HISTORY=3
DO_VALIDATE=false
DO_MERMAID=false
DO_GRAPH=false
DO_TLAPS=false

usage() {
    cat << EOF
L++ Skill Build Pipeline

Usage: $0 <skill_dir> [options]

Arguments:
    skill_dir       Path to skill directory (relative to utils/)

Options:
    --validate, -v  Run TLA+ validation
    --tlaps, -t     Run TLAPS seal certification (official tools)
    --mermaid, -m   Generate Mermaid diagram
    --graph, -g     Generate interactive HTML graph visualization
    --int-min N     TLA+ int minimum (default: $INT_MIN)
    --int-max N     TLA+ int maximum (default: $INT_MAX)
    --history N     TLA+ history depth (default: $MAX_HISTORY)
    --help, -h      Show this help

Examples:
    $0 llm_assistant
    $0 llm_assistant --validate --mermaid
    $0 llm_assistant -v -g --int-min -1 --int-max 1

Pipeline Steps:
    1. COMPILE   - Compile {skill}.json to results/{skill}_compiled.py
    2. VERIFY    - Generate TLA+ spec and optionally validate with TLC
    3. DOCUMENT  - Generate Mermaid diagram (with -m flag)
    4. VISUALIZE - Generate interactive HTML graph (with -g flag)
EOF
    exit 0
}

# Parse args
if [ $# -lt 1 ]; then
    usage
fi

SKILL_DIR="$1"
shift

while [ $# -gt 0 ]; do
    case "$1" in
        --validate|-v) DO_VALIDATE=true ;;
        --tlaps|-t) DO_TLAPS=true ;;
        --mermaid|-m) DO_MERMAID=true ;;
        --graph|-g) DO_GRAPH=true ;;
        --int-min) INT_MIN="$2"; shift ;;
        --int-max) INT_MAX="$2"; shift ;;
        --history) MAX_HISTORY="$2"; shift ;;
        --help|-h) usage ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
    shift
done

# Resolve skill path
if [ -d "$SCRIPT_DIR/$SKILL_DIR" ]; then
    SKILL_PATH="$SCRIPT_DIR/$SKILL_DIR"
elif [ -d "$SKILL_DIR" ]; then
    SKILL_PATH="$(cd "$SKILL_DIR" && pwd)"
else
    echo "Error: Skill directory not found: $SKILL_DIR"
    exit 1
fi

# Find blueprint JSON
BLUEPRINT=$(find "$SKILL_PATH" -maxdepth 1 -name "*.json" -type f | head -1)
if [ -z "$BLUEPRINT" ]; then
    echo "Error: No blueprint JSON found in $SKILL_PATH"
    exit 1
fi

SKILL_NAME=$(basename "$BLUEPRINT" .json)
echo "Building L++ Skill: $SKILL_NAME"
echo "  Blueprint: $BLUEPRINT"
echo ""

# Step 1: COMPILE
echo "[1/3] COMPILE - Generating operator..."
mkdir -p "$SKILL_PATH/results"
PYTHONPATH="$SRC_DIR:$PYTHONPATH" python3 -c "
from frame_py.compiler import compile_blueprint
compile_blueprint('$BLUEPRINT', '$SKILL_PATH/results/${SKILL_NAME}_compiled.py')
print('      Output: results/${SKILL_NAME}_compiled.py')
"

# Step 2: VERIFY - Generate TLA+ spec
echo ""
echo "[2/3] VERIFY - Generating TLA+ specification..."
mkdir -p "$SKILL_PATH/tla"
PYTHONPATH="$SRC_DIR:$PYTHONPATH" python3 -c "
import json
from frame_py.tla_validator import save_tla

with open('$BLUEPRINT') as f:
    bp = json.load(f)

tla_path, cfg_path = save_tla(
    bp,
    output_dir='$SKILL_PATH/tla',
    int_min=$INT_MIN,
    int_max=$INT_MAX,
    max_history=$MAX_HISTORY
)
print('      Bounds: INT=[$INT_MIN..$INT_MAX], HISTORY=$MAX_HISTORY')
print('      TLA+:', tla_path)
print('      Config:', cfg_path)
"

# Optional: Run TLC validation
if [ "$DO_VALIDATE" = true ]; then
    echo ""
    echo "      Running TLC validation..."
    PYTHONPATH="$SRC_DIR:$PYTHONPATH" python3 -c "
import json
from frame_py.tla_validator import validate_with_tlc

with open('$BLUEPRINT') as f:
    bp = json.load(f)

success, output = validate_with_tlc(bp, timeout=60)
if success:
    # Extract key metrics
    import re
    states = re.search(r'(\d+) states generated', output)
    distinct = re.search(r'(\d+) distinct states', output)
    depth = re.search(r'depth.*?(\d+)', output, re.IGNORECASE)
    print('      Result: PASS')
    if states: print('      States:', states.group(1))
    if distinct: print('      Distinct:', distinct.group(1))
    if depth: print('      Depth:', depth.group(1))
else:
    print('      Result: FAIL')
    print(output[:500])
    exit(1)
"

    # Run operational validation on Python files
    echo ""
    echo "      Running operational validation..."
    PYTHONPATH="$SRC_DIR:$PYTHONPATH" python3 -c "
from frame_py.operational_validator import validate_skill

# Validate Python files in skill directory
passed = validate_skill('$SKILL_PATH', verbose=True)
if not passed:
    exit(1)
"
fi

# Optional: Run TLAPS seal certification
if [ "$DO_TLAPS" = true ]; then
    echo ""
    echo "      Running TLAPS seal certification..."
    PYTHONPATH="$SRC_DIR:$PYTHONPATH" python3 -c "
import json
import sys
sys.path.insert(0, '$SCRIPT_DIR/tlaps_seal/src')
from seal_compute import (
    loadBlueprint, auditTrinity, auditFlange,
    generateTla, runTlc, runTlaps, generateCertificate
)

# Load blueprint
bp_result = loadBlueprint({'blueprintPath': '$BLUEPRINT'})
if bp_result.get('error'):
    print('      Error loading blueprint:', bp_result['error'])
    exit(1)
bp = bp_result['blueprint']

# Audit Trinity (Transitions, Gates, Actions)
trinity = auditTrinity({'blueprint': bp})
if not trinity['trinityAudit']['valid']:
    print('      Trinity audit FAILED:')
    for issue in trinity['trinityAudit']['transitions']['issues']:
        print('        -', issue)
    for issue in trinity['trinityAudit']['gates']['issues']:
        print('        -', issue)
    for issue in trinity['trinityAudit']['actions']['issues']:
        print('        -', issue)
    exit(1)
print('      Trinity audit: PASS')
print('        Transitions:', trinity['trinityAudit']['transitions']['count'])
print('        Gates:', trinity['trinityAudit']['gates']['count'])
print('        Actions:', trinity['trinityAudit']['actions']['count'])

# Audit Flange (context schema)
flange = auditFlange({'blueprint': bp})
print('      Flange audit:', 'PASS' if flange['flangeAudit']['valid'] else 'WARN')
print('        Properties:', flange['flangeAudit']['properties']['count'])
print('        Hermeticity:', f\"{flange['flangeAudit']['hermeticity']['score']:.0%}\")

# Generate TLA+ and run TLC
tla_result = generateTla({'blueprint': bp, 'blueprintPath': '$BLUEPRINT'})
if tla_result.get('error'):
    print('      TLA+ generation error:', tla_result['error'])
    exit(1)

tlc_result = runTlc({'tlaPath': tla_result['tlaPath']})
if not tlc_result['tlcResult']['passed']:
    print('      TLC verification FAILED')
    exit(1)
print('      TLC verification: PASS')

# Run TLAPS (or simulate if not installed)
tlaps_result = runTlaps({'tlaPath': tla_result['tlaPath']})
if tlaps_result['tlapsResult']['passed']:
    theorems = tlaps_result['tlapsResult']['theorems']
    print('      TLAPS certification: PASS')
    for thm, status in theorems.items():
        print(f'        {thm}: {status}')
else:
    print('      TLAPS certification: FAILED')
    exit(1)

# Generate certificate
cert = generateCertificate({
    'blueprint': bp,
    'trinityAudit': trinity['trinityAudit'],
    'flangeAudit': flange['flangeAudit'],
    'tlcResult': tlc_result['tlcResult'],
    'tlapsResult': tlaps_result['tlapsResult']
})
print('      Seal:', cert['sealCertificate']['seal'])
print('      Level:', cert['sealCertificate']['level'])
"
fi

# Step 3: DOCUMENT - Generate Mermaid
if [ "$DO_MERMAID" = true ]; then
    echo ""
    echo "[3/3] DOCUMENT - Generating Mermaid diagram..."
    PYTHONPATH="$SRC_DIR:$PYTHONPATH" python3 -c "
import json
import sys
sys.path.insert(0, '$SCRIPT_DIR/visualizer/src')
from readme_compute import mermaid

with open('$BLUEPRINT') as f:
    bp = json.load(f)

# Convert to viz format
bp_data = {
    'id': bp.get('id'),
    'name': bp.get('name'),
    'version': bp.get('version'),
    'states': bp.get('states', {}),
    'transitions': bp.get('transitions', []),
    'gates': bp.get('gates', {}),
    'entry_state': bp.get('entry_state'),
    'terminal_states': bp.get('terminal_states', [])
}

result = mermaid({'blueprint': bp_data})
print(result['mermaid'])
"
else
    echo ""
    echo "[3/4] DOCUMENT - Skipped (use -m to generate Mermaid)"
fi

# Step 4: VISUALIZE - Generate interactive HTML graph
if [ "$DO_GRAPH" = true ]; then
    echo ""
    echo "[4/4] VISUALIZE - Generating interactive HTML graph..."
    PYTHONPATH="$SRC_DIR:$PYTHONPATH" python3 -c "
import json
import sys
sys.path.insert(0, '$SCRIPT_DIR/graph_visualizer/src')
from graph_visualizer_compute import process

with open('$BLUEPRINT') as f:
    bp_str = f.read()

result = process({
    'blueprint': bp_str,
    'html_path': '$SKILL_PATH/results/${SKILL_NAME}_graph.html'
})

if result.get('has_html'):
    print('      Output: results/${SKILL_NAME}_graph.html')
else:
    print('      Error:', result.get('error', 'Unknown error'))
    exit(1)
"

    # Update README with graph link if README exists
    if [ -f "$SKILL_PATH/README.md" ]; then
        # Check if graph section already exists
        if ! grep -q "## State Machine Visualization" "$SKILL_PATH/README.md"; then
            echo "" >> "$SKILL_PATH/README.md"
            echo "## State Machine Visualization" >> "$SKILL_PATH/README.md"
            echo "" >> "$SKILL_PATH/README.md"
            echo "Interactive state machine diagram: [${SKILL_NAME}_graph.html](results/${SKILL_NAME}_graph.html)" >> "$SKILL_PATH/README.md"
            echo "" >> "$SKILL_PATH/README.md"
            echo "Open the HTML file in a browser for:" >> "$SKILL_PATH/README.md"
            echo "- Zoom/pan navigation" >> "$SKILL_PATH/README.md"
            echo "- Click nodes to highlight connections" >> "$SKILL_PATH/README.md"
            echo "- Hover for gate conditions" >> "$SKILL_PATH/README.md"
            echo "- Multiple layout options (hierarchical, horizontal, circular, grid)" >> "$SKILL_PATH/README.md"
            echo "      Updated: README.md with visualization link"
        fi
    fi
else
    echo ""
    echo "[4/4] VISUALIZE - Skipped (use -g to generate HTML graph)"
fi

echo ""
echo "Build complete: $SKILL_NAME"
