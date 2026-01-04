# Blueprint Builder

Builds L++ blueprints from extracted patterns and modules.

## Usage

```python
from src.blueprint_compute import COMPUTE_REGISTRY

# Initialize
COMPUTE_REGISTRY["blueprint:init"]({})

# Build from class module
result = COMPUTE_REGISTRY["blueprint:buildFromClass"]({
    "module": {
        "name": "OrderProcessor",
        "docstring": "Processes orders",
        "methods": [
            {"name": "validate", "docstring": "Validate order"},
            {"name": "process", "docstring": "Process order"},
            {"name": "complete", "docstring": "Complete order"}
        ],
        "states": ["validating", "processing"],
        "file": {"relpath": "src/order.py"}
    }
})

# Or build from patterns
result = COMPUTE_REGISTRY["blueprint:buildFromPatterns"]({
    "name": "PaymentHandler",
    "patterns": {
        "states": ["pending", "authorized", "captured"],
        "methods": ["authorize", "capture", "refund"],
        "conditions": ["is_authorized", "has_funds"]
    }
})

# Validate
validation = COMPUTE_REGISTRY["blueprint:validate"]({})

# Get JSON
json_result = COMPUTE_REGISTRY["blueprint:toJson"]({"indent": 2})
```

## Functions

| Function | Description |
|----------|-------------|
| `blueprint:init` | Initialize builder |
| `blueprint:buildFromClass` | Build from class module data |
| `blueprint:buildFromPatterns` | Build from extracted patterns |
| `blueprint:addStates` | Add states to current blueprint |
| `blueprint:addTransitions` | Add transitions |
| `blueprint:addGates` | Add gates |
| `blueprint:addActions` | Add actions |
| `blueprint:validate` | Validate blueprint |
| `blueprint:toJson` | Convert to JSON |
| `blueprint:getBlueprint` | Get current/specific blueprint |
| `blueprint:listBlueprints` | List all built blueprints |

## Integration

Used by workflows like `python_to_lpp` to build blueprints from extracted code patterns.
