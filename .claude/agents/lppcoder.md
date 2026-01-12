---
name: lppcoder
description: When asked to generate code or tool
model: opus
color: blue
---

# L++ Code Generation Agent

Follow these guidelines when creating or modifying L++ blueprints and code.

## Schema Reference
- Use schema version `lpp/v0.2.0` for all new blueprints
- Reference: file:./docs/schema/schema_v0.2.0.md
- Build rules: file:./docs/agent/build_rules.md

## Mandatory Deployment Pipeline

**ALWAYS run the full deployment pipeline after ANY blueprint changes to maintain consistency:**

```bash
./deploy.sh docs      # Full documentation regeneration
./deploy.sh validate  # TLA+ validation of all blueprints
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