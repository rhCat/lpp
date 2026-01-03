# L++ Blueprint Diff & Merge Tool

Semantic diff and merge tool for L++ blueprints. Unlike simple JSON text diff,
this tool understands the structure of L++ blueprints and provides meaningful
comparisons at the state machine level.

## Features

### Diff Features
- **State Diff**: Detect added/removed/modified states
- **Transition Diff**: Detect added/removed/modified transitions (by ID)
- **Gate Diff**: Detect added/removed/modified gates
- **Action Diff**: Detect added/removed/modified actions
- **Context Schema Diff**: Detect added/removed/modified properties
- **Entry/Terminal State Changes**: Detect changes to entry_state or terminal_states

### Output Formats
- **Unified diff**: Color-coded unified format showing +/- changes
- **Summary**: Statistics (added/removed/modified counts by element type)
- **JSON Patch**: RFC 6902 compliant patch operations

### Merge Features
- **Auto-merge**: Automatically merge non-conflicting changes
- **Conflict detection**: Identify when both versions modify the same element
- **Conflict resolution strategies**:
  - `take_left`: Prefer first blueprint on conflicts
  - `take_right`: Prefer second blueprint on conflicts
  - `manual`: Output conflicts for user resolution
- **Three-way merge**: Use common ancestor for smarter merging

## Usage

### Interactive Mode

```bash
cd utils/blueprint_differ
python3 interactive.py
```

### Command-line Diff

```bash
python3 interactive.py path/to/left.json path/to/right.json
```

### Commands

```
Loading:
  left <path>     - Load left (base) blueprint
  right <path>    - Load right (target) blueprint
  base <path>     - Load common ancestor for 3-way merge

Diffing:
  diff            - Compute semantic diff
  summary         - Show diff summary
  unified         - Show unified diff format
  patch           - Show JSON patch (RFC 6902)
  show            - Display current diff/merge result

Merging:
  merge           - Start merge (detects conflicts)
  merge_left      - Force merge, prefer left on conflicts
  merge_right     - Force merge, prefer right on conflicts
  take_left       - Resolve conflicts by taking left
  take_right      - Resolve conflicts by taking right
  merged          - Show merged blueprint
  export <path>   - Export merged blueprint to file

Navigation:
  back            - Go back to previous state
  reset           - Reset to ready state
  clear           - Clear all loaded blueprints
  state           - Show full context state

Other:
  self            - Diff the differ against itself
  help            - Show this help
  quit            - Exit
```

## Programmatic Usage

```python
from src.differ_compute import (
    load_blueprint,
    compute_diff,
    format_diff,
    generate_json_patch,
    detect_conflicts,
    merge_blueprints,
    export_merged
)

# Load blueprints
left = load_blueprint({'path': 'original.json', 'side': 'left'})
right = load_blueprint({'path': 'modified.json', 'side': 'right'})

# Compute diff
diff = compute_diff({'left': left['blueprint'], 'right': right['blueprint']})

# Format output
result = format_diff({
    'diff': diff['diff'],
    'format': 'unified',  # or 'summary'
    'path_left': 'original.json',
    'path_right': 'modified.json'
})
print(result['output'])

# Generate JSON patch
patch = generate_json_patch({'diff': diff['diff']})
print(patch['formatted'])

# Merge
conflicts = detect_conflicts({
    'left': left['blueprint'],
    'right': right['blueprint'],
    'diff': diff['diff']
})

merged = merge_blueprints({
    'left': left['blueprint'],
    'right': right['blueprint'],
    'strategy': 'auto',
    'conflicts': conflicts['conflicts']
})

# Export
export_merged({
    'blueprint': merged['merged'],
    'path': 'merged.json'
})
```

## State Machine

```mermaid
stateDiagram-v2
    %% L++ State Diagram: L++ Blueprint Diff & Merge
    [*] --> idle
    idle --> left_loaded : LOAD_LEFT
    left_loaded --> ready : LOAD_RIGHT
    ready --> ready : LOAD_BASE
    ready --> ready : LOAD_LEFT
    ready --> ready : LOAD_RIGHT
    ready --> diffing : DIFF [blueprint_left is not None ...]
    diffing --> diff_complete : DIFF_DONE
    ready --> diff_complete : DIFF_ALL [blueprint_left is not None ...]
    diff_complete --> diff_complete : SHOW_SUMMARY [diff_result is not None]
    diff_complete --> diff_complete : SHOW_UNIFIED [diff_result is not None]
    diff_complete --> diff_complete : SHOW_PATCH [diff_result is not None]
    diff_complete --> merging : MERGE [diff_result is not None]
    merging --> merge_complete : MERGE_AUTO [conflicts is None or len(co...]
    merging --> conflict : CONFLICT_DETECTED [conflicts is not None and l...]
    conflict --> merge_complete : TAKE_LEFT
    conflict --> merge_complete : TAKE_RIGHT
    diff_complete --> merge_complete : MERGE_LEFT [diff_result is not None]
    diff_complete --> merge_complete : MERGE_RIGHT [diff_result is not None]
    merge_complete --> merge_complete : EXPORT [merged_blueprint is not None]
    merge_complete --> diff_complete : BACK
    conflict --> diff_complete : BACK
    diff_complete --> diff_complete : DIFF_ALL
    diff_complete --> ready : RESET
    ready --> idle : CLEAR
    diff_complete --> idle : CLEAR
    merge_complete --> idle : CLEAR
    error --> idle : CLEAR
    idle --> error : LOAD_FAILED
    left_loaded --> error : LOAD_FAILED
    ready --> error : LOAD_FAILED
    diff_complete --> error : LOAD_FAILED
    diffing --> error : LOAD_FAILED
    merge_complete --> error : LOAD_FAILED
    merging --> error : LOAD_FAILED
    conflict --> error : LOAD_FAILED
```
> **Interactive View:** [Open zoomable diagram](results/blueprint_differ_diagram.html) for pan/zoom controls


## State Machine Visualization

Interactive state machine diagram: [blueprint_differ_graph.html](results/blueprint_differ_graph.html)

Open the HTML file in a browser for:
- Zoom/pan navigation
- Click nodes to highlight connections
- Hover for gate conditions
- Multiple layout options (hierarchical, horizontal, circular, grid)

## Compute Functions

| Function | Description |
|----------|-------------|
| `load_blueprint` | Load an L++ blueprint from a JSON file |
| `clear_all` | Clear all loaded blueprints and diff results |
| `compute_diff` | Compute semantic diff between two blueprints |
| `format_diff` | Format diff for display (unified or summary) |
| `generate_json_patch` | Generate RFC 6902 JSON patch from diff |
| `detect_conflicts` | Detect merge conflicts between blueprints |
| `merge_blueprints` | Merge two blueprints with specified strategy |
| `export_merged` | Export merged blueprint to file |

## Element Types Compared

| Element Type | Description |
|--------------|-------------|
| `state` | State definitions in the state machine |
| `transition` | Transitions between states (matched by ID) |
| `gate` | Guard conditions for transitions |
| `action` | Side-effect definitions (SET, COMPUTE, EMIT) |
| `context_property` | Properties in context_schema |
| `entry_state` | The starting state |
| `terminal_state` | Exit states |
| `metadata` | Blueprint metadata (id, name, version, etc.) |

## File Structure

```
blueprint_differ/
  blueprint_differ.json  # L++ blueprint for the differ itself
  interactive.py         # CLI interface
  README.md              # This file
  src/
    __init__.py          # Package exports
    differ_compute.py    # Compute functions
  results/
    blueprint_differ_compiled.py  # Compiled operator
    blueprint_differ_graph.html   # Interactive visualization
  tla/
    lpp_blueprint_differ.tla      # TLA+ specification
    lpp_blueprint_differ.cfg      # TLA+ config
```

## Examples

### Diff Two Blueprints

```bash
python3 interactive.py

> left utils/visualizer/visualizer.json
> right utils/linter/blueprint_linter.json
> diff
```

### Export JSON Patch

```bash
> left original.json
> right modified.json
> diff
> patch
```

### Merge with Conflict Resolution

```bash
> left base.json
> right feature.json
> base common_ancestor.json  # Optional for 3-way merge
> diff
> merge
> take_right  # or take_left
> export merged.json
```
