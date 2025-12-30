# L++ Skill Construction Rules (v1.1)

## Overview
L++ (Logic Plus Plus) is a deterministic framework that separates Eternal Logic (The Bone) from Volatile Compute (The Flesh). Every "Skill" added to an agent must be constructed as a verifiable logic circuit.

## Coding Style
- Functions: Clean, concise, minimal variable naming using camelCase.
- Constraints: 79 character line limit. No emojis.
- JSON: Human-readable format with each key on its own line.

## Mandatory Build Steps

### 1. The Bone: {skill_name}.json
- Schema: Must strictly adhere to schema_v0.1.md.
- Traceability: Every transition MUST have a unique id.
- Gate Rigor: Gates must be "Light." Move complex math/transformations to COMPUTE units.
- Flange Spec: Define a context_schema with strict types for tool discovery.

### 2. The Flesh: src/{skill_name}_compute.py
- Hermeticity: Functions must be pure. Input is params: dict, output is result: dict.
- Isolation: No global state or direct I/O. Side effects managed via DISPATCH atom.
- Registry: Export a COMPUTE_REGISTRY mapping "namespace:operation" to functions.

### 3. The Extrusion: interactive.py
- Constraint: Minimal wrapper (< 50 lines).
- Pattern: Use compile_and_load to generate the operator and provide a thin CLI/API.

### 4. The Documentation: README.md
- Source of Truth: Generated via `build_skill.sh --mermaid`.
- Logic Netlist: Maintain a structure.txt (raw logic graph dump) to verify the netlist before final extrusion.

## Agent Workflow (The "Pre-frontal" Loop)
1. DRAFT: Generate/Update {skill_name}.json.
2. VERIFY: Run `./build_skill.sh <dir> --validate`. 
   - Define Operating Envelope using `--int-min`, `--int-max`, and `--history`.
   - Fix all deadlocks or invariant violations before proceeding.
3. IMPLEMENT: Write hermetic functions in src/.
4. EXTRUDE: Generate the minimal interactive.py wrapper.
5. DOCUMENT: Run `./build_skill.sh <dir> --mermaid` to generate visuals for README.md.
6. SIGN-OFF: Present the Mermaid diagram to the Human (Engineer of Record).

## Engineering Philosophy
- Logic over Text: Debate the state graph, not "vibes."
- Determinism over Probability: Critical behavior belongs in the Bone, not the LLM prompt.
- Transparency: If you cannot visualize the logic, the logic is broken.