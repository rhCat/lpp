"""
L++ Dev Suite CLI

Usage:
    lpp <command> [args]

Commands:
    init        Create new L++ skill project with build script
    build       Run full pipeline: validate → compile → tla → test → docs

    compile     Compile blueprint to Python
    visualize   Generate blueprint visualization
    validate    Validate blueprint or assembly
    docs        Generate documentation (mermaid, dashboard)
    test        Generate and run tests
    tla         Generate TLA+ specification

    util        Run a utility tool
    workflow    Run a workflow
    agent       Manage Claude Code agents
    list        List available utilities/workflows/agents
    version     Show version

Examples:
    lpp init my_skill            # Create new skill project
    lpp build .                  # Run full build pipeline
    lpp compile blueprint.json   # Compile only
    lpp docs .                   # Generate docs only
"""

import sys
import argparse
from typing import List, Optional


def cmd_compile(args: List[str]) -> int:
    """Compile a blueprint to Python."""
    from lpp.core.compiler import main as compile_main
    sys.argv = ["lpp-compile"] + args
    return compile_main() or 0


def cmd_visualize(args: List[str]) -> int:
    """Generate blueprint visualization."""
    from lpp.core.visualizer import main as visualize_main
    sys.argv = ["lpp-visualize"] + args
    return visualize_main() or 0


def cmd_validate(args: List[str]) -> int:
    """Validate a blueprint or assembly."""
    if not args:
        print("Usage: lpp validate <blueprint.json> [--assembly]")
        return 1

    blueprint_path = args[0]
    is_assembly = "--assembly" in args

    if is_assembly:
        from lpp.core.validators.assembly import loadAssembly, validateAssembly
        try:
            assembly, components = loadAssembly(blueprint_path)
            errors = validateAssembly(assembly, components)
            if errors:
                print(f"Validation failed with {len(errors)} errors:")
                for err in errors:
                    print(f"  - {err}")
                return 1
            print("Assembly validation passed!")
            return 0
        except Exception as e:
            print(f"Error: {e}")
            return 1
    else:
        from lpp.core.validators.blueprint import validate_blueprint
        import json
        try:
            with open(blueprint_path) as f:
                bp = json.load(f)
            validate_blueprint(bp)
            print("Blueprint validation passed!")
            return 0
        except Exception as e:
            print(f"Validation failed: {e}")
            return 1


def cmd_docs(args: List[str]) -> int:
    """Generate documentation for a blueprint or skill directory."""
    from pathlib import Path
    import json

    if not args:
        print("Usage: lpp docs <path> [all|mermaid|dashboard|clean]")
        return 1

    target = Path(args[0]).resolve()
    doc_type = args[1] if len(args) > 1 else "all"

    if doc_type == "clean":
        import shutil
        rd = target / "results"
        if rd.exists():
            shutil.rmtree(rd)
            print(f"Cleaned: {rd}")
        return 0

    # Find blueprint
    bp_file = None
    for p in [target / "blueprint.json", target / f"{target.name}.json"]:
        if p.exists():
            bp_file = p
            break
    if not bp_file:
        if target.suffix == ".json" and target.exists():
            bp_file = target
        else:
            for p in target.glob("*.json"):
                bp_file = p
                break
    if not bp_file:
        print(f"No blueprint found in {target}")
        return 1

    with open(bp_file) as f:
        bp = json.load(f)

    rd = (target if target.is_dir() else target.parent) / "results"
    rd.mkdir(exist_ok=True)

    if doc_type in ["all", "mermaid"]:
        from lpp.core.visualizer import generate_mermaid
        mmd = generate_mermaid(bp)
        mmd_file = rd / "diagram.mmd"
        mmd_file.write_text(mmd)
        print(f"Generated: {mmd_file}")

    if doc_type in ["all", "dashboard"]:
        from lpp.core.visualizer import generate_html
        html = generate_html(bp)
        html_file = rd / "dashboard.html"
        html_file.write_text(html)
        print(f"Generated: {html_file}")

    return 0


def cmd_test(args: List[str]) -> int:
    """Generate and run tests for a skill."""
    import subprocess
    from pathlib import Path

    if not args:
        print("Usage: lpp test <path> [--generate|--run|--coverage]")
        return 1

    target = Path(args[0]).resolve()
    gen_only = "--generate" in args
    run_only = "--run" in args
    cov = "--coverage" in args
    test_dir = target / "tests"

    if not run_only:
        # Find compute files
        compute_files = list(target.glob("*_compute.py"))
        compute_files += list(target.glob("compute.py"))
        compute_files += list(target.glob("src/*_compute.py"))
        for f in compute_files:
            test_dir.mkdir(exist_ok=True)
            tf = test_dir / f"test_{f.stem}.py"
            if not tf.exists():
                content = f'''"""Auto-generated tests for {f.name}"""
import pytest
import sys
sys.path.insert(0, str({repr(str(f.parent))}))
from {f.stem} import COMPUTE_REGISTRY

def test_registry_exists():
    assert COMPUTE_REGISTRY is not None
    assert len(COMPUTE_REGISTRY) > 0

def test_all_functions_callable():
    for name, func in COMPUTE_REGISTRY.items():
        assert callable(func), f"{{name}} is not callable"
'''
                tf.write_text(content)
                print(f"Generated: {tf}")
            break

    if not gen_only and test_dir.exists():
        cmd = ["python", "-m", "pytest", str(test_dir), "-v"]
        if cov:
            cmd.extend(["--cov", str(target)])
        return subprocess.run(cmd).returncode

    return 0


def cmd_tla(args: List[str]) -> int:
    """Generate and validate TLA+ specification."""
    from pathlib import Path
    import json

    if not args:
        print("Usage: lpp tla <blueprint.json> [--check] [--output <dir>]")
        return 1

    bp_path = Path(args[0]).resolve()
    check = "--check" in args
    out_dir = bp_path.parent / "tla"

    for i, a in enumerate(args):
        if a == "--output" and i + 1 < len(args):
            out_dir = Path(args[i + 1])

    out_dir.mkdir(exist_ok=True)

    with open(bp_path) as f:
        bp = json.load(f)

    from lpp.core.validators.tla import save_tla, validate_with_tlc

    tla_file, cfg_file = save_tla(bp, str(out_dir))
    print(f"Generated: {tla_file}")
    print(f"Generated: {cfg_file}")

    if check:
        print("Running TLC model checker...")
        success, output = validate_with_tlc(bp)
        if not success:
            print(f"  Error: {output}")
            return 1
        print("TLC: No errors found!")

    return 0


def cmd_init(args: List[str]) -> int:
    """Initialize a new L++ skill project."""
    from pathlib import Path

    if not args:
        print("Usage: lpp init <skill_name> [--path <dir>]")
        return 1

    skill_name = args[0]
    target_dir = Path.cwd()

    for i, a in enumerate(args):
        if a == "--path" and i + 1 < len(args):
            target_dir = Path(args[i + 1])

    skill_dir = target_dir / skill_name
    if skill_dir.exists():
        print(f"Error: {skill_dir} already exists")
        return 1

    skill_dir.mkdir(parents=True)
    (skill_dir / "src").mkdir()
    (skill_dir / "tests").mkdir()
    (skill_dir / "results").mkdir()
    (skill_dir / "tla").mkdir()

    # Create blueprint template
    blueprint = {
        "$schema": "lpp/v0.2.0",
        "id": skill_name,
        "name": skill_name.replace("_", " ").title(),
        "version": "1.0.0",
        "description": f"L++ skill: {skill_name}",
        "context_schema": {"properties": {}},
        "states": {
            "idle": {"description": "Initial state"},
            "processing": {"description": "Processing"},
            "done": {"description": "Completed"},
            "error": {"description": "Error occurred"}
        },
        "entry_state": "idle",
        "terminal_states": {"done": {}, "error": {}},
        "gates": {},
        "actions": {},
        "transitions": [
            {"id": "t_start", "from": "idle", "to": "processing",
             "on_event": "START"},
            {"id": "t_done", "from": "processing", "to": "done",
             "on_event": "COMPLETE"},
            {"id": "t_error", "from": "*", "to": "error", "on_event": "ERROR"}
        ]
    }

    import json
    bp_file = skill_dir / "blueprint.json"
    with open(bp_file, "w") as f:
        json.dump(blueprint, f, indent=2)

    # Create compute template
    compute_file = skill_dir / "compute.py"
    compute_file.write_text(f'''"""
{skill_name} Compute Functions

Pure functions implementing business logic.
"""

def process(params: dict) -> dict:
    """Process input and return result."""
    return {{"result": "processed", "input": params}}


COMPUTE_REGISTRY = {{
    "{skill_name}:process": process,
}}
''')

    # Create build script
    build_script = skill_dir / "build.sh"
    build_script.write_text(f'''#!/bin/bash
# L++ Build Script for {skill_name}
set -e

SKILL_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SKILL_DIR"

echo "=== L++ Build: {skill_name} ==="

# Create output directories
mkdir -p results tla tests

# 1. Validate
echo "Step 1: Validating blueprint..."
lpp validate blueprint.json

# 2. Compile
echo "Step 2: Compiling..."
lpp compile blueprint.json results/compiled.py

# 3. Generate TLA+
echo "Step 3: Generating TLA+ spec..."
lpp tla blueprint.json --output tla

# 4. Generate tests
echo "Step 4: Generating tests..."
lpp test . --generate

# 5. Run tests
echo "Step 5: Running tests..."
lpp test . --run

# 6. Generate documentation
echo "Step 6: Generating documentation..."
lpp docs .

echo ""
echo "=== Build Complete ==="
echo "Outputs:"
echo "  results/compiled.py    - Compiled operator"
echo "  results/diagram.mmd    - Mermaid diagram"
echo "  results/dashboard.html - HTML dashboard"
echo "  tla/{skill_name}.tla   - TLA+ specification"
echo "  tests/                 - Auto-generated tests"
''')
    build_script.chmod(0o755)

    # Create README
    readme = skill_dir / "README.md"
    readme.write_text(f'''# {skill_name.replace("_", " ").title()}

L++ Skill

## Quick Start

```bash
./build.sh          # Run full build pipeline
lpp validate .      # Validate only
lpp docs .          # Generate docs only
```

## Structure

```
{skill_name}/
├── blueprint.json  # State machine definition
├── compute.py      # Pure compute functions
├── build.sh        # Build pipeline script
├── results/        # Generated artifacts
├── tla/            # TLA+ specifications
└── tests/          # Auto-generated tests
```
''')

    print(f"Created L++ skill: {skill_dir}")
    print(f"  blueprint.json  - Edit to define states/transitions")
    print(f"  compute.py      - Add your compute functions")
    print(f"  build.sh        - Run to compile/test/document")
    print()
    print(f"Next: cd {skill_name} && ./build.sh")
    return 0


def cmd_build(args: List[str]) -> int:
    """Run full build pipeline: validate → compile → tla → test → docs."""
    from pathlib import Path
    import subprocess

    target = Path(args[0]).resolve() if args else Path.cwd()

    # Find blueprint
    bp_file = None
    for p in [target / "blueprint.json", target / f"{target.name}.json"]:
        if p.exists():
            bp_file = p
            break
    if not bp_file:
        for p in target.glob("*.json"):
            if "blueprint" in p.name.lower():
                bp_file = p
                break
    if not bp_file:
        print(f"No blueprint found in {target}")
        return 1

    print(f"=== L++ Build: {target.name} ===")
    steps = [
        ("Validating", ["lpp", "validate", str(bp_file)]),
        ("Compiling", ["lpp", "compile", str(bp_file),
                       str(target / "results" / "compiled.py")]),
        ("Generating TLA+", ["lpp", "tla", str(bp_file)]),
        ("Generating tests", ["lpp", "test", str(target), "--generate"]),
        ("Running tests", ["lpp", "test", str(target), "--run"]),
        ("Generating docs", ["lpp", "docs", str(target)]),
    ]

    (target / "results").mkdir(exist_ok=True)

    for i, (name, cmd) in enumerate(steps, 1):
        print(f"\nStep {i}: {name}...")
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f"  FAILED: {result.stderr or result.stdout}")
            return 1
        for line in result.stdout.strip().split("\n"):
            if line:
                print(f"  {line}")

    print("\n=== Build Complete ===")
    return 0


def cmd_util(args: List[str]) -> int:
    """Run a utility tool."""
    if not args:
        print("Usage: lpp util <utility_name> [args]")
        print("\nAvailable utilities:")
        from lpp.util import list_utilities
        for util in list_utilities():
            print(f"  {util}")
        return 1

    util_name = args[0]
    util_args = args[1:]

    from lpp.util import get_utility
    util = get_utility(util_name)
    if not util:
        print(f"Error: Unknown utility '{util_name}'")
        return 1

    # Try to run CLI if available
    try:
        from importlib import import_module
        cli_module = import_module(f"lpp.util.{util_name}.cli")
        if hasattr(cli_module, "main"):
            sys.argv = [f"lpp-{util_name}"] + util_args
            return cli_module.main() or 0
    except (ImportError, AttributeError):
        pass

    # Fall back to run function
    if hasattr(util, "run"):
        # Parse args as key=value pairs
        params = {}
        positional_args = []
        for arg in util_args:
            if "=" in arg:
                key, value = arg.split("=", 1)
                params[key] = value
            else:
                positional_args.append(arg)

        # Map positional args to expected parameter names based on utility
        if positional_args:
            first_arg = positional_args[0]
            # Utilities expecting blueprint_path
            if util_name in ["compliance_checker", "blueprint_debugger",
                             "coverage_analyzer", "event_simulator",
                             "tlaps_prover", "test_generator", "tlaps_seal",
                             "blueprint_builder", "blueprint_composer",
                             "blueprint_differ", "blueprint_linter",
                             "blueprint_playground", "schema_migrator",
                             "execution_tracer", "visualizer",
                             "graph_visualizer"]:
                params["blueprint_path"] = first_arg
            # Utilities expecting file_path
            elif util_name in ["logic_decoder", "legacy_extractor",
                               "function_decoder"]:
                params["file_path"] = first_arg
            # Utilities expecting source_path
            elif util_name in ["policy_generator"]:
                params["source_path"] = first_arg
            # Utilities expecting utilsPath
            elif util_name in ["doc_generator", "skill_registry",
                               "blueprint_registry", "dashboard"]:
                params["utilsPath"] = first_arg
                params["options"] = {"all": True}
            # Utilities expecting query
            elif util_name in ["interactive_search", "research_scraper",
                               "scholar_chat"]:
                params["query"] = first_arg
                params["search_path"] = "."
                params["source"] = "arxiv"
            # Default fallback
            else:
                params["target"] = first_arg
                params["project_path"] = first_arg
                params["blueprint_path"] = first_arg
                params["file_path"] = first_arg

        result = util.run(params)
        state = result.get("state", "unknown")
        error = result.get("error")
        if error:
            print(f"Error: {error}")
            return 1
        print(f"State: {state}")
        if result.get("context"):
            ctx = result["context"]
            # Print relevant outputs based on utility
            if "blueprint" in ctx and ctx["blueprint"]:
                print(f"Blueprint loaded: {ctx['blueprint'].get('id', 'yes')}")
            if "blueprints" in ctx:
                print(f"Total: {len(ctx.get('blueprints', []))} blueprints")
            if "results" in ctx and isinstance(ctx["results"], dict):
                print(f"Generated: {ctx['results'].get('generated', 0)}")
        return 0

    print(f"Utility '{util_name}' has no CLI or run function")
    return 1


def cmd_workflow(args: List[str]) -> int:
    """Run a workflow."""
    if not args:
        print("Usage: lpp workflow <workflow_name> [args]")
        print("\nAvailable workflows:")
        from lpp.workflow import list_workflows
        for wf in list_workflows():
            print(f"  {wf}")
        return 1

    wf_name = args[0]
    wf_args = args[1:]

    from lpp.workflow import get_workflow
    wf = get_workflow(wf_name)
    if not wf:
        print(f"Error: Unknown workflow '{wf_name}'")
        return 1

    # Try to run CLI if available
    try:
        from importlib import import_module
        cli_module = import_module(f"lpp.workflow.{wf_name}.cli")
        if hasattr(cli_module, "main"):
            sys.argv = [f"lpp-{wf_name}"] + wf_args
            return cli_module.main() or 0
    except (ImportError, AttributeError):
        pass

    # Fall back to run function
    if hasattr(wf, "run"):
        # Parse args
        project_path = wf_args[0] if wf_args else None
        output_path = wf_args[1] if len(wf_args) > 1 else None

        result = wf.run(project_path=project_path, output_path=output_path)
        print(result)
        return 0 if "error" not in result else 1

    print(f"Workflow '{wf_name}' has no CLI or run function")
    return 1


def cmd_agent(args: List[str]) -> int:
    """Manage Claude Code agents."""
    from lpp.agent.cli import main as agent_main
    sys.argv = ["lpp-agent"] + args
    return agent_main() or 0


def cmd_list(args: List[str]) -> int:
    """List available utilities, workflows, and agents."""
    show_utils = "--utils" in args or "-u" in args
    show_workflows = "--workflows" in args or "-w" in args
    show_agents = "--agents" in args or "-a" in args
    show_all = not (show_utils or show_workflows or show_agents)

    if show_utils or show_all:
        print("Utilities:")
        from lpp.util import list_utilities
        for util in list_utilities():
            print(f"  {util}")
        print()

    if show_workflows or show_all:
        print("Workflows:")
        from lpp.workflow import list_workflows
        for wf in list_workflows():
            print(f"  {wf}")
        print()

    if show_agents or show_all:
        print("Agents:")
        from lpp.agent import list_agents
        for agent in list_agents():
            print(f"  {agent}")

    return 0


def cmd_version(args: List[str]) -> int:
    """Show version information."""
    from lpp import __version__
    print(f"L++ Dev Suite v{__version__}")
    print()
    print("Packages:")
    print("  lpp.core     - Core runtime")
    print("  lpp.util     - 28 utility tools")
    print("  lpp.workflow - 3 workflows")
    print("  lpp.agent    - Claude Code agents")
    return 0


COMMANDS = {
    "init": cmd_init,
    "build": cmd_build,
    "compile": cmd_compile,
    "visualize": cmd_visualize,
    "validate": cmd_validate,
    "docs": cmd_docs,
    "test": cmd_test,
    "tla": cmd_tla,
    "util": cmd_util,
    "workflow": cmd_workflow,
    "agent": cmd_agent,
    "list": cmd_list,
    "version": cmd_version,
    "-v": cmd_version,
    "--version": cmd_version,
}


def main(argv: Optional[List[str]] = None) -> int:
    """Main entry point."""
    if argv is None:
        argv = sys.argv[1:]

    if not argv:
        print(__doc__)
        return 0

    cmd = argv[0]
    args = argv[1:]

    if cmd in COMMANDS:
        return COMMANDS[cmd](args)

    # Check if it's a utility or workflow shortcut
    from lpp.util import UTILITIES
    from lpp.workflow import WORKFLOWS

    if cmd in UTILITIES:
        return cmd_util([cmd] + args)
    if cmd in WORKFLOWS:
        return cmd_workflow([cmd] + args)

    print(f"Unknown command: {cmd}")
    print("Run 'lpp' without arguments for help.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
