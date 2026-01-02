# Skill Contractor v1.7.0

An autonomous L++ skill generator that continuously iterates on logic to achieve coding targets with self-evaluation.
**Two-phase workflow**: Blueprint validation before implementation.

## Overview

The Skill Contractor implements the manifesto:
> "Create an AI agent that would continuously iterate on the logic and achieve coding target when self evaluation see fit."

It operates as an autonomous loop with **two distinct phases**:

### Phase 1: Blueprint
1. **Plan** - Generate L++ blueprint JSON
2. **Validate** - Run `build_skill.sh --validate` (TLC model checking)
3. **Refine** - If validation fails, regenerate blueprint only
4. **Advance** - When validated, move to implementation phase

### Phase 2: Implementation
5. **Plan** - Generate compute + interactive steps
6. **Execute** - Write `src/<skill>_compute.py` and `interactive.py`
7. **Sanitize** - Auto-fix common LLM errors (literal newlines in strings)
8. **Validate** - Final validation (TLC + operational checks)
9. **Evaluate** - Self-assess progress against target

This two-phase approach prevents wasteful regeneration of already-validated blueprints.

### Code Sanitization

LLMs commonly generate Python with syntax errors like literal newlines inside strings:
```python
# LLM generates (BROKEN):
print("Hello
World")

# Sanitizer fixes to (VALID):
print("Hello\nWorld")
```

The `frame_py.operational_validator.sanitize_python_code()` function automatically fixes these errors before writing files to disk.

## State Machine

```mermaid
stateDiagram-v2
    [*] --> idle

    idle: idle
    planning: planning
    executing: executing
    parsing: parsing
    stepping: stepping
    validating: validating
    evaluating: evaluating
    refining: refining
    reviewing: reviewing
    complete: complete
    error: error

    idle --> planning: SUBMIT
    planning --> executing: DONE [has_plan]
    planning --> error: DONE [has_error]
    
    executing --> parsing: DONE [has_raw_output]
    executing --> error: DONE [has_error]
    
    parsing --> stepping: DONE [output_valid, has_more_steps]
    parsing --> validating: DONE [output_valid, all_steps_done, in_blueprint_phase]
    parsing --> validating: DONE [output_valid, all_steps_done, in_implementation_phase]
    parsing --> executing: DONE [output_invalid, can_repair]
    parsing --> error: DONE [output_invalid, max_repairs]
    
    stepping --> executing: DONE [has_more_steps]
    stepping --> validating: DONE [all_steps_done]
    
    validating --> planning: DONE [blueprint_validated, in_blueprint_phase] → advance_phase
    validating --> evaluating: DONE [lpp_valid, in_implementation_phase]
    validating --> refining: DONE [validation_failed, within_iterations]
    
    evaluating --> complete: DONE [is_satisfied, lpp_ok]
    evaluating --> refining: DONE [not_satisfied, within_iterations]
    evaluating --> complete: DONE [max_iterations_reached]
    
    refining --> planning: DONE
    error --> executing: DONE [step_can_retry]
    error --> reviewing: DONE [step_max_errors]
    reviewing --> stepping: DONE [review_skip]
    reviewing --> refining: DONE [review_replan]
    
    complete --> [*]
```

## Context Schema (Flange)

| Property | Type | Description |
|----------|------|-------------|
| `target` | string | Coding target to achieve |
| `phase` | string | Current phase: "blueprint" or "implementation" |
| `blueprint_validated` | boolean | True if blueprint passed TLC validation |
| `plan` | object | Decomposed execution plan |
| `step_index` | number | Current step index |
| `step_count` | number | Total steps in plan |
| `execution_log` | array | History of executed steps |
| `artifacts` | array | Generated files |
| `score` | number | Evaluation score 0-100 |
| `threshold` | number | Score threshold for completion |
| `iteration` | number | Current iteration count |
| `max_iterations` | number | Max iterations allowed |
| `is_satisfied` | boolean | Target achieved flag |
| `is_lpp_target` | boolean | True if generating L++ skill |
| `lpp_validated` | boolean | Final L++ validation status |
| `parse_error` | string | Parse/validation error if any |
| `repair_attempts` | number | Number of output repair attempts |

## Events

| Event | Payload | Description |
|-------|---------|-------------|
| `START` | - | Initialize agent configuration |
| `SUBMIT` | `{target: string}` | Submit a coding target |
| `DONE` | - | Signal step/phase completion |
| `RETRY` | - | Recover from error state |
| `RESET` | - | Reset to idle (global) |

## Usage

```bash
# Set environment variables
export OPENAI_API_KEY="your-key"
export OPENAI_API_BASE="https://api.openai.com/v1"
export OPENAI_MODEL="gpt-4o-mini"
export EVAL_THRESHOLD="80"
export MAX_ITERATIONS="5"

# Run interactive CLI
cd always_on
python interactive.py
```

### Example Session

```
Always-On Agent v1.4.0 | State: idle | Phase: blueprint

> Create a skill that searches Google and generates opinions
  [PHASE: blueprint]
  [planning] Generating blueprint...
  [executing] Step 1: Create search_opinion.json...
  [parsing] Validating output...
  [validating] ./utils/build_skill.sh --validate...
  [BLUEPRINT VALIDATED] Advancing to implementation phase
  
  [PHASE: implementation]
  [planning] Generating implementation steps...
  [executing] Step 1: Create src/search_opinion_compute.py...
  [executing] Step 2: Create interactive.py...
  [validating] Final validation...
  [evaluating] Score 90/100 | Satisfied: True

Complete! Output in: always_on/output/
```

## Compute Units

| Unit | Description |
|------|-------------|
| `agent:init` | Initialize from environment, set phase="blueprint" |
| `agent:decompose` | Break target into steps (phase-aware) |
| `agent:generate_step_output` | Execute single step via LLM |
| `agent:parse_and_sanitize` | Parse and validate LLM output |
| `agent:write_output` | Write files to disk |
| `agent:advance_step` | Move to next step |
| `agent:advance_phase` | Move from blueprint to implementation |
| `agent:validate_lpp` | Run build_skill.sh validation |
| `agent:evaluate` | Self-evaluate progress |
| `agent:review_failed_step` | Decide skip or replan |

## Files

```
always_on/
  always_on.json        # Blueprint (The Bone)
  interactive.py        # CLI wrapper (Extrusion)
  manifesto.txt         # Original requirement
  README.md             # This file
  src/
    __init__.py
    always_on_compute.py   # Compute units (The Flesh)
    prompts.py             # Externalized prompts
  results/
    always_on_compiled.py  # Generated operator
  runs/
    <timestamp>/           # Per-run logs
      run.log
      step_0.log
      stdout.log
  tla/
    always_on.tla       # TLA+ specification
    always_on.cfg       # TLC configuration
  output/               # Generated skill output
```

## Design Notes

The agent follows the L++ Trinity:
- **Transitions**: Navigate between planning, executing, validating, evaluating states
- **Gates**: Guard conditions (blueprint_validated, lpp_valid, has_more_steps, etc.)
- **Actions**: SET context, COMPUTE via LLM, advance phase/step

### Two-Phase Workflow
- **Blueprint Phase**: Only generates/refines the `.json` blueprint until TLC passes
- **Implementation Phase**: Generates compute units and interactive wrapper without regenerating blueprint

### Error Recovery
- Step-level retry with max 3 attempts
- Parse error repair with re-prompting
- Review failed steps (skip or replan)

Self-evaluation uses a score threshold (default 80) to determine satisfaction.
If unsatisfied, the agent refines its plan using feedback and iterates.

## Logic Graph (Auto-decoded from Python)

This visualization was auto-generated by analyzing the Python compute module.

**View:** [Open skill_contractor_logic_graph.html](results/skill_contractor_logic_graph.html)

| Metric | Value |
|--------|-------|
| States | 0 |
| Transitions | 0 |
| Entry | `idle` |
| Terminal | ['complete', 'error'] |
