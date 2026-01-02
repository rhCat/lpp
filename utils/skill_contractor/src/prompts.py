"""
Prompt templates for Always-On Autonomous Agent.

Separates "The Bone" (logic) from "The Flesh" (compute).
All prompts are pure string templates with {placeholders}.
"""

SYSTEM = """You are an autonomous coding agent. You help decompose,
execute, and evaluate coding tasks. Be precise, structured, and thorough.

CRITICAL: Always respond with VALID JSON only. No markdown, no explanation
outside JSON. Ensure all strings are properly escaped and terminated."""

JSON_RULES = """
JSON OUTPUT RULES (MANDATORY):
1. Response must be ONLY valid JSON - no markdown, no ```json blocks
2. All strings must use double quotes and be properly escaped
3. Escape special chars: \\n for newline, \\\\ for backslash, \\" for quote
4. No trailing commas in arrays or objects
5. No single quotes for strings
6. No comments in JSON
7. Ensure all brackets/braces are balanced
"""

LPP_RULES = """
=== L++ BUILD RULES (MANDATORY) ===
ALL outputs MUST be L++ Skills following schema v0.1.2:

1. STRUCTURE
   - <skill_name>.json - Blueprint (Trinity: Transitions, Gates, Actions)
   - src/<skill_name>_compute.py - Hermetic functions (params->result)
   - interactive.py - Minimal wrapper (<50 lines)

2. BLUEPRINT SCHEMA (EXACT FORMAT REQUIRED):
   CRITICAL: states/gates/actions are DICTIONARIES, but transitions is an ARRAY!
   
   {{
     "$schema": "lpp/v0.1.2",
     "id": "my_skill",
     "name": "My Skill",
     "version": "1.0.0",
     "description": "What this skill does",
     
     "context_schema": {{
       "properties": {{
         "query": {{"type": "string", "description": "User input"}},
         "results": {{"type": "array", "description": "Output data"}},
         "has_query": {{"type": "boolean", "default": false}},
         "has_results": {{"type": "boolean", "default": false}},
         "error": {{"type": "string"}}
       }}
     }},
     
     "states": {{
       "idle": {{"description": "Waiting for input"}},
       "processing": {{"description": "Working on task"}},
       "done": {{"description": "Task complete"}}
     }},
     
     "entry_state": "idle",
     "terminal_states": ["done"],
     
     "gates": {{
       "has_query": {{"type": "expression", "expression": "has_query == True"}},
       "has_results": {{"type": "expression", "expression": "has_results == True"}}
     }},
     
     "transitions": [
       {{"id": "t_start", "from": "idle", "to": "processing", "on_event": "start", "gates": ["has_query"], "actions": ["do_process"]}},
       {{"id": "t_done", "from": "processing", "to": "done", "on_event": "complete"}}
     ],
     
     "actions": {{
       "set_query": {{
         "type": "set",
         "target": "query",
         "value_from": "event.payload.query"
       }},
       "do_process": {{
         "type": "compute",
         "compute_unit": "my_skill:process",
         "input_map": {{"query": "query"}},
         "output_map": {{"results": "results", "has_results": "has_results"}}
       }}
     }}
   }}

3. CRITICAL RULES:
   - transitions MUST be an ARRAY of objects: [{{"id": "t1", "from": ..., "to": ...}}, ...]
   - DO NOT use transitions as a dict: {{"t1": {{}}, "t2": {{}}}} is WRONG!
   - Gate expressions MUST reference variables defined in context_schema
   - Use boolean flags (has_X) for gate conditions, not null checks
   - Actions with "type": "compute" MUST have input_map and output_map
   - compute_unit format: "<skill_id>:<function_name>"
   - DO NOT copy the example verbatim - create actual states for your task!

4. COMPUTE RULES (src/<skill_name>_compute.py):
   - Pure functions: def func_name(params: dict) -> dict
   - Register in COMPUTE_UNITS = {{"func_name": func_name}}
   - No side effects except final file write

5. VERIFICATION
   - Run ./utils/build_skill.sh <dir> --validate
   - Fix all errors before proceeding
"""

DECOMPOSE = """Decompose this coding target into concrete steps.

Target: {target}
Workspace: {workspace}
Iteration: {iteration}
Current Phase: {phase}
{failure_ctx}
L++ Framework Paths:
- LPP_ROOT: {lpp_root}
- Build script: {lpp_root}/utils/build_skill.sh
- Schema: {lpp_root}/docs/schema/schema_v0.1.2.md
{lpp_rules}

=== MANDATORY OUTPUT FORMAT ===
ALL code MUST be delivered as L++ Skills:
1. <skill_name>.json - Blueprint following schema v0.1.2
2. src/<skill_name>_compute.py - Hermetic compute functions  
3. interactive.py - Minimal CLI wrapper

=== TWO-PHASE WORKFLOW (CRITICAL) ===
PHASE 1 (BLUEPRINT): Generate and validate the L++ blueprint
- Generate <skill_name>.json blueprint ONLY
- Build/compile validates immediately
- Loop until TLC passes

PHASE 2 (IMPLEMENTATION): Only after Phase 1 passes
- DO NOT REGENERATE THE BLUEPRINT - IT IS ALREADY VALIDATED!
- Generate src/<skill_name>_compute.py - Python code with COMPUTE_UNITS dict
- Generate interactive.py - CLI wrapper

=== CURRENT PHASE: {phase} ===
{phase_instructions}

CONSTRAINTS:
- NO PAID API KEYS (use ddgs for search, env vars for LLM)
- Target audience: Non-technical users

Return JSON:
{{
  "phase": "{phase}",
  "steps": [
    {{"id": 1, "action": "description", "type": "code|file"}}
  ],
  "rationale": "brief explanation",
  "fixes": "what we're fixing from previous iteration (if any)"
}}

{json_rules}
RESPOND WITH ONLY THE JSON OBJECT."""

PHASE_BLUEPRINT_INSTRUCTIONS = """You are in BLUEPRINT phase.
Generate ONLY the <skill_name>.json blueprint file.
Step type should be "lpp" or "file".
Output should be the L++ blueprint JSON following schema v0.1.2."""

PHASE_IMPLEMENTATION_INSTRUCTIONS = """You are in IMPLEMENTATION phase.
The blueprint (<skill_name>.json) is ALREADY VALIDATED - DO NOT regenerate it!

Generate these Python files:
1. src/<skill_name>_compute.py - Contains the compute functions
2. interactive.py - CLI wrapper

Step type should be "code" or "file".
Output should be PYTHON CODE, not JSON blueprint!

=== CRITICAL: PYTHON STRING ESCAPING ===
NEVER put literal newlines inside string literals!

WRONG (causes "EOL while scanning string literal"):
  query = input("Enter query:
  ")
  print("Results:
  ")

CORRECT:
  query = input("Enter query:\\n")
  print("Results:\\n")
  print(f"Results:\\n{data}")

Always use \\n for newlines inside strings!

Example compute file structure:
```python
def process(params: dict) -> dict:
    query = params.get("query", "")
    # ... implementation ...
    return {{"results": results, "has_results": True}}

COMPUTE_UNITS = {{"process": process}}
```

Example interactive.py:
```python
from src.<skill_name>_compute import COMPUTE_UNITS
# minimal CLI loop
```"""

# Output format guidance for EXECUTE_STEP
BLUEPRINT_OUTPUT_FORMAT = """When generating a .json blueprint, VERIFY:
[ ] states/gates/actions are DICTS with string keys
[ ] transitions is an ARRAY (list): [{{...}}, {{...}}], NOT a dict!
[ ] Every action with "type": "compute" has BOTH input_map AND output_map
[ ] Gate expressions use "has_X == True" format, NOT "X is not None"
[ ] All context variables used in gates are defined in context_schema
[ ] transitions objects have: id, from, to, on_event (and optionally gates, actions)

WRONG (transitions as dict):
"transitions": {{"t_start": {{"from": "idle", "to": "x"}}, "t_done": {{"from": "x", "to": "done"}}}}

CORRECT (transitions as array):
"transitions": [
  {{"id": "t_start", "from": "idle", "to": "x", "on_event": "start"}},
  {{"id": "t_done", "from": "x", "to": "done", "on_event": "complete"}}
]

Return JSON:
{{
  "result": "generated L++ blueprint",
  "output": "<escaped JSON blueprint with $schema>",
  "filename": "<skill_name>.json",
  "files_modified": [],
  "success": true
}}"""

IMPLEMENTATION_OUTPUT_FORMAT = """Generate PYTHON code, NOT JSON blueprint.
The blueprint is DONE. Generate .py files only.

=== CRITICAL PYTHON STRING RULES ===
NEVER put literal newlines inside strings!

WRONG (will cause syntax error):
  print("Hello
  World")

CORRECT:
  print("Hello\\nWorld")
  print("Hello" + "\\n" + "World")
  print(f"Hello\\nWorld")

For multi-line output, use:
  print("Line 1\\nLine 2\\nLine 3")
  # OR
  print("Line 1")
  print("Line 2")
  # OR use triple quotes for docstrings only

Return JSON:
{{
  "result": "generated Python implementation",
  "output": "<escaped Python code>",
  "filename": "src/<skill_name>_compute.py OR interactive.py",
  "files_modified": [],
  "success": true
}}

CRITICAL: filename must end with .py, NOT .json!"""

EXECUTE_STEP = """Execute this step for the coding target.

Target: {target}

=== PHASE: {phase} ===
{phase_instructions}

=== CURRENT STEP ===
Step {progress}: {action}
Type: {step_type}
Output directory: {output_dir}
{iteration_ctx}
=== CONTEXT ===
Previous step: {prev_step}
Next step: {next_step}
Last attempt on this step: {last_attempt}

L++ Paths:
- LPP_ROOT: {lpp_root}
- Examples: {lpp_root}/examples/python/
{lpp_rules}

=== L++ FILE NAMING ===
- Blueprint: <skill_name>.json (NOT skill_blueprint.json)
- Compute: src/<skill_name>_compute.py
- Wrapper: interactive.py

=== PHASE-SPECIFIC OUTPUT ===
{phase_output_format}

CONSTRAINTS:
- NO PAID API KEYS
- ALL CODE must follow L++ schema v0.1.2

{json_rules}

Return JSON:
{{
  "result": "what was accomplished",
  "output": "generated code (escape newlines as \\\\n)",
  "filename": "filename.py or skill.json",
  "files_modified": [],
  "command": "shell command if type is command",
  "success": true
}}

RESPOND WITH ONLY THE JSON OBJECT."""

EVALUATE = """Evaluate progress toward the coding target.

Target: {target}
Iteration: {iteration}
Threshold: {threshold}
L++ Validation: {lpp_status}

=== PROGRESS SUMMARY ===
Steps: {completed}/{total_steps} completed
Pending: {pending} steps remaining

=== RECENT RESULTS ===
{results}

=== ARTIFACTS CREATED ===
{artifacts}

=== L++ COMPLIANCE (MANDATORY) ===
ALL output MUST include:
1. <skill_name>.json - Blueprint with $schema, states, transitions
2. src/<skill_name>_compute.py - Hermetic functions
3. interactive.py - Minimal wrapper

SCORING:
- Missing blueprint: max 50
- Missing compute: max 60
- L++ validation failed: max 70
- Only satisfied=true if lpp_compliance >= 80

{json_rules}

Return JSON:
{{
  "score": 75,
  "criteria": {{
    "completeness": 80,
    "correctness": 70,
    "lpp_compliance": 75
  }},
  "satisfied": false,
  "feedback": "improvements needed",
  "summary": "brief evaluation"
}}

RESPOND WITH ONLY THE JSON OBJECT."""

REVIEW_STEP = """Review this failed step and decide: skip or replan?

Target: {target}

=== FAILED STEP ===
Step {step_num}: {action}
Attempts: {attempts}
Last error: {error}

=== ATTEMPT HISTORY ===
{attempt_results}

Failed steps so far: {failed_steps}

Decide:
- "skip": Step is non-critical, continue with remaining steps
- "replan": Step is critical, need new approach

{json_rules}

Return JSON:
{{
  "decision": "skip|replan",
  "reason": "explanation",
  "alternative": "suggested fix if replan"
}}

RESPOND WITH ONLY THE JSON OBJECT."""
