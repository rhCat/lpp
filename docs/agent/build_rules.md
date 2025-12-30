# L++ Skill Construction Rules (v1.3)

## Overview
L++ (Logic Plus Plus) is a deterministic framework that separates Eternal Logic (The Bone) from Volatile Compute (The Flesh). Every "Skill" added to an agent must be constructed as a verifiable logic circuit.

## Coding Style
- Functions: Clean, concise, minimal variable naming using camelCase.
- Constraints: 79 character line limit. No emojis.
- JSON: Human-readable format with each key on its own line.

## Mandatory Build Steps

### -1. The Archaeology: Logic Decoder
- **Action:** If the task involves legacy code (e.g., `data_utils.py`), run `utils/logic_decoder/interactive.py` to `decode` the file.
- **Goal:** Extract the existing "Bone" from the legacy "Flesh" to ensure the new blueprint respects established side effects and control flows.

### 0. The Discovery: Skill Registry
- **Action:** Run `utils/skill_registry/interactive.py` to `scan` and `list` existing skills.
- **Goal:** Identify existing "Flange Specs" (context schemas) to enable Logic Stacking.

### 0.5. The Decomposition: Task Orchestrator
- **Action:** For complex tasks, run `utils/task_orchestrator/interactive.py` to `SUBMIT` the root goal.
- **Goal:** Generate a hierarchical feature tree. This prevents "Logic Bloat" by breaking the problem into atomic sub-assemblies.

### 1. The Bone: {skill_name}.json
- Schema: Must strictly adhere to `docs/schema/schema_v0.1.2.md` (The Trinity).
- Traceability: Every transition MUST have a unique id.
- Logic Stacking: Align `input_map` with existing "Flanges" discovered in Step 0.

### 2. The Flesh: src/{skill_name}_compute.py
- Hermeticity: Functions must be pure. Input is params: dict, output is result: dict.
- Isolation: Side effects managed strictly via the Frame's DISPATCH atom.

### 3. The Extrusion: interactive.py
- Constraint: Minimal wrapper (< 50 lines). Use `compile_and_load` pattern.

### 4. The Documentation: README.md
- Source of Truth: Generated via `build_skill.sh --mermaid`.

## Agent Workflow (The "Pre-frontal" Loop)
1. **ARCHAEOLOGY:** Decode legacy code to find hidden logic.
2. **DISCOVER:** Scan registry for existing tool Flanges.
3. **DECOMPOSE:** Use Task Orchestrator to break complex goals into a feature tree.
4. **DRAFT:** Generate atomic JSON blueprints for each leaf in the tree.
5. **VERIFY:** Run `./build_skill.sh <dir> --validate`. Fix all deadlocks.
6. **IMPLEMENT:** Write hermetic functions in `src/`.
7. **EXTRUDE:** Generate the `interactive.py` wrapper.
8. **DOCUMENT:** Run `./build_skill.sh <dir> --mermaid` for `README.md`.
9. **SIGN-OFF:** Present the Mermaid diagram to the Human (Engineer of Record).
