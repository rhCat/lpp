# L++ Skill Construction Rules (v1.2)

## Overview
L++ (Logic Plus Plus) is a deterministic framework that separates Eternal Logic (The Bone) from Volatile Compute (The Flesh). Every "Skill" added to an agent must be constructed as a verifiable logic circuit.

## Coding Style
- Functions: Clean, concise, minimal variable naming using camelCase.
- Constraints: 79 character line limit. No emojis.
- JSON: Human-readable format with each key on its own line.

## Mandatory Build Steps

### 0. The Discovery: Skill Registry
- **Action:** Before drafting, run `utils/skill_registry/interactive.py` to `scan` and `list` existing skills.
- **Goal:** Identify existing "Flange Specs" (context schemas) to enable Logic Stacking. Do not rebuild what is already on the shelf.

### 1. The Bone: {skill_name}.json
- Schema: Must strictly adhere to `docs/schema/schema_v0.1.md`.
- Traceability: Every transition MUST have a unique id.
- **Logic Stacking:** If this skill uses another skill, its `input_map` must align with the target's `context_schema` (The Flange).
- Gate Rigor: Gates must be "Light." Move complex math/transformations to COMPUTE units.

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
1. **DISCOVER:** Scan `utils/skill_registry` to learn existing tool Flanges.
2. **DRAFT:** Generate/Update {skill_name}.json. Align I/O with existing skills for stacking.
3. **VERIFY:** Run `./build_skill.sh <dir> --validate`. 
   - Define Operating Envelope using `--int-min`, `--int-max`, and `--history`.
   - Fix all deadlocks or invariant violations before proceeding.
4. **IMPLEMENT:** Write hermetic functions in src/.
5. **EXTRUDE:** Generate the minimal interactive.py wrapper.
6. **DOCUMENT:** Run `./build_skill.sh <dir> --mermaid` for README.md.
7. **SIGN-OFF:** Present the Mermaid diagram to the Human (Engineer of Record).

## Engineering Philosophy
- **Logic Stacking:** Build small, verified unit operations and pipe them together.
- **Logic over Text:** Debate the state graph, not "vibes."
- **Determinism over Probability:** Critical behavior belongs in the Bone.