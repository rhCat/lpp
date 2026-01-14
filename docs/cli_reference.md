# L++ CLI Reference

## Utilities

### Blueprint Analysis (expects: `blueprint.json`)
```bash
lpp util blueprint_linter <blueprint.json>
lpp util blueprint_debugger <blueprint.json>
lpp util compliance_checker <blueprint.json>
lpp util coverage_analyzer <blueprint.json>
lpp util event_simulator <blueprint.json>
lpp util execution_tracer <blueprint.json>
lpp util graph_visualizer <blueprint.json>
lpp util schema_migrator <blueprint.json>
lpp util test_generator <blueprint.json>
lpp util tlaps_prover <blueprint.json>
lpp util tlaps_seal <blueprint.json>
lpp util visualizer <blueprint.json>
```

### Blueprint Creation (expects: `blueprint.json` or none)
```bash
lpp util blueprint_builder [blueprint.json]
lpp util blueprint_composer [blueprint.json]
lpp util blueprint_differ <left.json> <right.json>
lpp util blueprint_playground [blueprint.json]
```

### Code Analysis (expects: `file.py`)
```bash
lpp util logic_decoder <file.py>
lpp util function_decoder <file.py>
lpp util legacy_extractor <file.py>
```

### Directory Scanning (expects: `utils_directory/`)
```bash
lpp util doc_generator <utils_dir/>
lpp util dashboard <utils_dir/>
lpp util blueprint_registry <utils_dir/>
lpp util skill_registry <utils_dir/>
```

### Search/Query (expects: `"query"`)
```bash
lpp util interactive_search "search term"
lpp util research_scraper "search query"
lpp util scholar_chat "question"
```

### No Args Required
```bash
lpp util skill_contractor
lpp util task_orchestrator
lpp util llm_assistant          # requires ANTHROPIC_API_KEY env
```

## Workflows

```bash
lpp workflow python_to_lpp <project_dir/>
lpp workflow logic_vulnerability_pointer <target_path>
lpp workflow lpp_canvas
```

## Quick Examples

```bash
# Analyze a blueprint
lpp util blueprint_linter src/lpp/util/logic_decoder/blueprint.json

# Decode Python to blueprint
lpp util logic_decoder src/lpp/__init__.py

# Generate docs for all utils
lpp util doc_generator src/lpp/util

# Run security audit
lpp workflow logic_vulnerability_pointer src/myproject

# Create new blueprint interactively
lpp workflow lpp_canvas
```
