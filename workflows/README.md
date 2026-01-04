# L++ Workflows

This directory contains automated workflows that use L++ tools to accomplish common tasks.

## Design Principle

**Workflows orchestrate utils tools - they do not reimplement functionality.**

Each workflow should:
1. **Use existing utils** from `utils/` via their `COMPUTE_REGISTRY`
2. **Include a DESIGN.md** documenting the architecture and utils integration
3. **Provide an interactive CLI** that orchestrates the utils calls

If a workflow needs functionality not in utils, either:
- Add the new tool to `utils/` first, then use it from the workflow
- Use basic fallback implementations while the util is being developed

## Available Workflows

| Workflow | Description |
|----------|-------------|
| [python_to_lpp](python_to_lpp/) | Refactor a Python project into L++ blueprints with full documentation |

## Workflow Structure

Each workflow follows the standard L++ tool structure:

```
workflow_name/
├── workflow_name.json    # L++ blueprint defining the workflow
├── DESIGN.md             # Architecture and utils integration docs
├── interactive.py        # CLI interface
├── src/
│   ├── __init__.py
│   └── *_compute.py      # Compute functions (calls utils)
├── results/              # Generated outputs
└── README.md             # User documentation
```

## Creating New Workflows

1. Create a new directory under `workflows/`
2. Define the workflow blueprint JSON
3. Create `DESIGN.md` documenting architecture and utils integration
4. Implement compute functions in `src/` that call utils
5. Create an interactive CLI
6. Document with README.md

### Blueprint Template

```json
{
  "$schema": "lpp/v0.1.2",
  "id": "my_workflow",
  "name": "My Workflow",
  "version": "1.0.0",
  "description": "Description of what the workflow does",

  "states": {
    "idle": { "description": "Awaiting input" },
    "processing": { "description": "Processing" },
    "complete": { "description": "Done" },
    "error": { "description": "Error" }
  },

  "entry_state": "idle",
  "terminal_states": ["complete", "error"],

  "gates": {},
  "actions": {},
  "transitions": []
}
```

### Compute Function Template

```python
"""Workflow compute functions."""
from typing import Dict, Any

_state: Dict[str, Any] = {}

def init(params: dict) -> dict:
    """Initialize the workflow."""
    global _state
    _state = {"initialized": True}
    return {"success": True}

# ... more functions ...

COMPUTE_REGISTRY = {
    "workflow:init": init,
    # ... more mappings ...
}
```

## Using Workflows

All workflows can be run via their interactive CLI:

```bash
cd workflows/workflow_name
python interactive.py --help
```

Or imported and used programmatically:

```python
from workflows.workflow_name.src.compute import COMPUTE_REGISTRY

COMPUTE_REGISTRY["workflow:init"](params)
```
