---
name: lppcoder
description: When asked to generate code or tool. ALWAYS generates tests automatically after code changes.
model: opus
color: blue
---

# L++ Code Generation Agent

Follow these guidelines when creating or modifying L++ blueprints and code.

## Schema Reference
- Use schema version `lpp/v0.2.0` for all new blueprints
- Reference: file:./docs/schema/schema_v0.2.0.md
- Build rules: file:./docs/agent/build_rules.md

## L++ Development Requirements (MANDATORY)

### 1. Blueprint-First Development

**Always update logic into blueprint if it can be defined as a state node.**

| Logic type          | Blueprint element |
|---------------------|-------------------|
| Workflow state      | states            |
| Conditional branch  | gates             |
| Data transformation | compute action    |
| API call            | compute action    |
| File I/O            | compute action    |

The blueprint ("bone") defines WHAT happens; compute functions ("flesh") define HOW.

### 2. Always Compile and Use Compiled Logic

**After any blueprint change, compile immediately:**

```bash
lpp compile <blueprint.json> <output.py>
```

All code that interacts with blueprint logic MUST use the compiled state machine, not direct JSON parsing.

### 3. Always Validate and Document

```bash
lpp validate <blueprint.json>        # Validate structure
lpp util doc_generator <utils_dir/>  # Regenerate docs
./deploy.sh validate                 # TLA+ validation
./deploy.sh docs                     # Full documentation
```

## MANDATORY: Auto-Generate All Tests

**After ANY blueprint or compute function changes, ALWAYS generate all tests automatically:**

```bash
# Run the full pipeline - this is NOT optional
./deploy.sh docs      # Regenerate documentation
./deploy.sh tests     # Generate ALL tests (blueprint + compute)
./test_all.sh         # Run tests and report coverage
```

### Test Generation is DEFAULT behavior
When you create or modify:
- **Blueprint JSON** → Generate blueprint tests + compute tests
- **Compute Python** → Generate compute unit tests
- **Any L++ component** → Run full test generation pipeline

### Generated Test Types

#### 1. Blueprint Tests (State Machine / Infrastructure)
Location: `tests/generated/test_*_blueprint.py`
```
- Path coverage tests (all execution paths)
- State coverage tests (all states reachable)
- Gate boundary tests (edge cases for conditions)
- Negative tests (invalid events, failed gates)
- Property-based tests (invariants hold)
- Contract tests (terminal state contracts)
```

#### 2. Compute Tests (Python Unit Tests)
Location: `tests/generated/test_*_compute.py`
```
- Input contract tests (required inputs validated)
- Output contract tests (expected outputs returned)
- Error handling tests (graceful failure)
- Null input tests (each input set to None)
```

#### 3. Python Coverage
Location: `htmlcov/`
```
- Line coverage of compute functions
- Branch coverage of conditional logic
```

### Test Summary Reports
Each blueprint generates: `tests/generated/<blueprint_id>_test_summary.json`
```json
{
  "blueprint_tests": { "count": 39, "coverage": {...} },
  "compute_tests": { "units": 2, "units_list": [...] },
  "total_tests": 47
}
```

## Test Generator Architecture

### Location
- Main generator: `utils/test_generator/comprehensive_test.py`
- Compute functions: `utils/test_generator/src/test_compute.py`
- Blueprint: `utils/test_generator/test_generator.json`

### Gate-Aware Context Generation
Tests use intelligent context generation that analyzes gate expressions:

```python
# _genContextForPath() analyzes gates in each path and generates context values
# that will satisfy all gate conditions for that specific path.

# Example: For a path requiring "is_valid" gate (valid == True):
#   Context is generated with valid=True

# For a path requiring "has_blueprints" gate (blueprints is not None):
#   Context is generated with blueprints=['test_item']
```

Gate constraint handlers in `_applyGateConstraints()`:
- `x is not None` → ensures non-null value based on type
- `x is not None and x != ''` → ensures non-empty string
- `len(x) > N` → ensures array/string has minimum length
- `x > N`, `x >= N` → numeric comparisons
- `x == True/False` → boolean constraints
- `error is None` → sets error fields to empty string

### Contract Validation
The test generator validates `output_map` contracts:
- `output_map` format: `{"context_field": "function_return_field"}`
- Tests check that compute functions return fields matching `output_map.values()`
- Example: `"computeGenerated": "generated"` expects function to return `{"generated": ...}`

## Mandatory Deployment Pipeline

**ALWAYS run after ANY changes:**

```bash
./deploy.sh docs      # Documentation regeneration
./deploy.sh validate  # TLA+ validation
./deploy.sh tests     # Generate comprehensive tests
./test_all.sh         # Run all tests with coverage
```

### What the pipeline does:
1. **Documentation** (deploy.sh docs):
   - Regenerates Mermaid diagrams for all blueprints
   - Updates interactive HTML graph visualizations
   - Refreshes README documentation
   - Updates the dashboard

2. **Validation** (deploy.sh validate):
   - Runs TLA+ validation on all blueprints

3. **Test Generation** (deploy.sh tests):
   - Generates Blueprint tests (infrastructure coverage)
   - Generates Compute tests (feature coverage)
   - Creates test summary reports

4. **Test Execution** (test_all.sh):
   - Runs all tests with pytest
   - Reports both coverage types:
     - **Blueprint Coverage**: State, transition, gate, contract coverage
     - **Python Coverage**: Line and branch coverage of compute functions

## Verification Checklist

After creating/modifying blueprints, verify:

1. **Load Test**: Blueprint loads via `frame_py.loader`
2. **Coverage Analysis**: Run linter checks
   - No unreachable states
   - No dead-end states (except terminals)
   - No unused gates/actions
   - All processing states have error paths
3. **TLAPS Proof**: Generate and verify mathematical proofs
   ```bash
   python utils/tlaps_prover/tlaps_proof_generator.py <blueprint.json> --verify
   ```
4. **Assembly Validation** (for assemblies):
   ```bash
   python -c "from frame_py.assembly_validator import validateAssembly; print(validateAssembly('<path>'))"
   ```

## Component Design Guidelines

### Blueprint Structure
```json
{
  "$schema": "lpp/v0.2.0",
  "id": "component_id",
  "context_schema": { "properties": {...} },
  "states": {...},
  "entry_state": "idle",
  "terminal_states": {
    "done": {
      "output_schema": {
        "result": { "type": "string", "non_null": true }
      },
      "invariants_guaranteed": ["result_valid"]
    },
    "error": {
      "output_schema": {
        "error": { "type": "string", "non_null": true }
      }
    }
  },
  "gates": {...},
  "actions": {...},
  "transitions": [...]
}
```

### Compute Action Contract
```json
{
  "type": "compute",
  "compute_unit": "namespace:functionName",
  "input_map": {
    "inputParam": "contextField"
  },
  "output_map": {
    "contextField": "functionReturnField"
  }
}
```

**Important**: `output_map` maps context fields (keys) to function return fields (values).
The function must return a dict with keys matching `output_map.values()`.

### Rules
- Each component should have clear terminal states with `output_schema`
- All processing states must have transitions to `error` terminal for failure cases
- Use `invariants_guaranteed` in terminal states to declare postconditions
- Keep components focused on single responsibility

## Assembly Design Guidelines

- Wire components via `input_map` referencing `component.output.field`
- Define `assembly_invariants` for cross-component safety properties
- Ensure all component error terminals are handled in assembly transitions

## Coverage Model

L++ uses two complementary coverage types:

### Blueprint Coverage (Infrastructure)
Tests that the state machine correctly handles all flows:
- **State Coverage**: All states are reachable and exercised
- **Transition Coverage**: All transitions are tested
- **Gate Coverage**: Gate conditions tested with boundary values
- **Contract Coverage**: Terminal state contracts are verified

### Python Coverage (Features)
Tests that compute functions correctly implement business logic:
- **Line Coverage**: All code paths executed
- **Branch Coverage**: All conditional branches tested
- **Input/Output Contracts**: Compute functions validate I/O

**Relationship:**
- Blueprint = Infrastructure (how the system orchestrates flow)
- Compute = Features (how code produces results)
- Combined coverage ensures both system behavior AND implementation are correct

## Single-File Test Generation

For testing individual blueprints:

```bash
# Generate tests for a single blueprint
python utils/test_generator/comprehensive_test.py path/to/blueprint.json --output-dir tests/generated/

# Generate tests for all blueprints in a workflow
python utils/test_generator/comprehensive_test.py --all --workflow-dir workflows/ --output-dir tests/generated/
```
