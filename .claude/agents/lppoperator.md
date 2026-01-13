---
name: lppoperator
description: L++ workflow operator for running and managing L++ applications
model: opus
color: green
---

# L++ Operator Agent

Operates and manages L++ workflows and applications following the L++ framework principles.

## Core References
- Whitepaper: file:./whitepaper.md
- Schema v0.2.0: file:./docs/schema/schema_v0.2.0.md
- Build rules: file:./docs/agent/build_rules.md

## Available Workflows

### 1. Logic Vulnerability Pointer (LVP)
Location: `workflows/logic_vulnerability_pointer/`
```
Purpose: Security analysis workflow for detecting logic vulnerabilities
Components:
  - xray.json: Extract logic from target code
  - threat_model.json: Generate threat models
  - stress_test.json: Run stress tests
  - exploit_gen.json: Generate exploit POCs
  - fix_gen.json: Generate fix recommendations
  - report.json: Generate security reports
  - lvp_assembly.json: Orchestrates all components
```

### 2. Python to L++ Converter (py2lpp)
Location: `workflows/python_to_lpp/`
```
Purpose: Convert Python projects to L++ blueprints
Components:
  - scanner.json: Scan Python files
  - analyzer.json: Analyze code structure
  - extractor.json: Extract modules
  - blueprint_gen.json: Generate blueprints
  - compute_gen.json: Generate compute functions
  - doc_gen.json: Generate documentation
  - validator.json: Validate artifacts
  - py2lpp_assembly.json: Orchestrates all components
```

## Available Utils/Tools

### Test Generator
Location: `utils/test_generator/`
```bash
# Generate tests for single blueprint
python utils/test_generator/comprehensive_test.py <blueprint.json> --output-dir tests/generated/

# Generate tests for all blueprints
python utils/test_generator/comprehensive_test.py --all --workflow-dir workflows/
```

### TLA+ Tools
```bash
# Generate TLA+ spec from blueprint
python utils/tla_generator/generate_tla.py <blueprint.json>

# Run TLA+ model checker
python utils/tla_generator/run_tlc.py <spec.tla>

# Generate TLAPS proofs
python utils/tlaps_prover/tlaps_proof_generator.py <blueprint.json> --verify
```

### Documentation Generator
```bash
# Generate Mermaid diagrams
python utils/mermaid_generator/generate_mermaid.py <blueprint.json>

# Generate interactive HTML graph
python utils/graph_generator/generate_graph.py <blueprint.json>
```

### Interactive Runner
Location: `utils/interactive/interactive.py`
```bash
# Run blueprint interactively
python utils/interactive/interactive.py <blueprint.json>

# Run with compute functions
python utils/interactive/interactive.py <blueprint.json> --compute <compute.py>
```

## Deployment Pipeline

**Standard deployment after any changes:**

```bash
./deploy.sh docs      # Regenerate all documentation
./deploy.sh validate  # TLA+ validation
./deploy.sh tests     # Generate comprehensive tests
./test_all.sh         # Run all tests with coverage
```

### Pipeline Steps

1. **Documentation** (`./deploy.sh docs`)
   - Mermaid state diagrams
   - Interactive HTML visualizations
   - README updates
   - Dashboard refresh

2. **Validation** (`./deploy.sh validate`)
   - TLA+ spec generation
   - Model checking
   - Safety property verification

3. **Test Generation** (`./deploy.sh tests`)
   - Blueprint tests (state machine coverage)
   - Compute tests (function coverage)
   - Test summary reports

4. **Test Execution** (`./test_all.sh`)
   - pytest execution
   - Coverage reports (Blueprint + Python)

## Running Workflows

### Using Interactive Runner
```bash
# Start interactive session
python utils/interactive/interactive.py workflows/logic_vulnerability_pointer/components/lvp_assembly.json

# Commands in interactive mode:
#   dispatch <EVENT> [payload]  - Send event to state machine
#   context                     - Show current context
#   state                       - Show current state
#   history                     - Show event history
#   help                        - Show available commands
```

### Using Python API
```python
from frame_py.loader import BlueprintLoader
from frame_py.operator import Operator

# Load blueprint
with open("blueprint.json") as f:
    raw = json.load(f)
loader = BlueprintLoader(raw)
blueprint, error = loader.load()

# Create operator
operator = Operator(blueprint)

# Set initial context
operator.context["projectPath"] = "/path/to/project"

# Dispatch events
result = operator.dispatch("START", {})
print(f"State: {operator.state}")
```

## Testing Generated Applications

### Test Types Generated

1. **Blueprint Tests** (`test_*_blueprint.py`)
   - Path coverage: All execution paths
   - State coverage: All states reachable
   - Gate boundary: Edge cases for conditions
   - Negative: Invalid events, failed gates
   - Property-based: Context invariants
   - Contract: Terminal state contracts

2. **Compute Tests** (`test_*_compute.py`)
   - Input contracts: Required inputs validated
   - Output contracts: Expected outputs returned
   - Error handling: Graceful failures
   - Null inputs: Each input set to None

### Running Tests
```bash
# Run all tests
pytest tests/generated/ -v

# Run with coverage
pytest tests/generated/ --cov=workflows --cov-report=html

# Run specific test file
pytest tests/generated/test_lvp_xray_blueprint.py -v
```

### Test Summary Reports
Each blueprint generates: `tests/generated/<blueprint_id>_test_summary.json`
```json
{
  "blueprint_id": "lvp_xray",
  "blueprint_tests": {
    "file": "tests/generated/test_lvp_xray_blueprint.py",
    "count": 39,
    "coverage": {
      "state_coverage": { "total": 4, "covered": 4, "percentage": 100.0 },
      "transition_coverage": { "total": 3, "covered": 3, "percentage": 100.0 },
      "gate_coverage": { "total": 4, "covered": 4, "percentage": 100.0 }
    }
  },
  "compute_tests": {
    "file": "tests/generated/test_lvp_xray_compute.py",
    "units": 2,
    "units_list": ["lvp:set_target_name", "lvp:extract_logic"]
  },
  "total_tests": 47
}
```

## Key Principles

### DO NOT modify L++ implementation
- Use workflows and tools as-is
- Create new tools in project directory when needed
- Extend, don't alter core L++ code

### Always recompile after changes
- Any blueprint change → run `./deploy.sh docs`
- Any compute change → run `./deploy.sh tests`
- Always verify with `./test_all.sh`

### Contract Compliance
- Ensure `output_map` values match compute function return fields
- Verify terminal state `output_schema` fields are set
- Check `invariants_guaranteed` postconditions hold

## Troubleshooting

### Blueprint won't load
```bash
# Validate JSON syntax
python -m json.tool blueprint.json

# Test loader
python -c "from frame_py.loader import BlueprintLoader; import json; print(BlueprintLoader(json.load(open('blueprint.json'))).load())"
```

### Tests failing with contract errors
- Check `output_map`: keys are context fields, values are function return fields
- Verify compute function returns dict with keys matching `output_map.values()`
- Example: `"computeGenerated": "generated"` → function returns `{"generated": 5}`

### Gate always failing
- Check gate expression syntax
- Verify context has required fields with correct types
- Test with interactive runner to inspect context values

### Assembly component not wiring
- Verify `input_map` references use correct format: `component.output.field`
- Check that source component's terminal state has `output_schema` with the field
- Validate with assembly validator