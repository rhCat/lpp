"""
L++ Dev Suite CLI

Main command-line interface for the L++ development suite.

Usage:
    lpp <command> [args]

Commands:
    compile     Compile blueprint to Python
    visualize   Generate blueprint visualization
    validate    Validate blueprint or assembly

    docs        Generate documentation (mermaid, dashboard, all)
    test        Generate and run tests
    tla         TLA+ validation

    util        Run a utility tool
    workflow    Run a workflow
    agent       Manage Claude Code agents

    list        List available utilities/workflows/agents
    version     Show version information

Examples:
    lpp compile blueprint.json output.py
    lpp docs /path/to/skill          # Generate all docs
    lpp docs /path/to/skill mermaid  # Mermaid only
    lpp test /path/to/skill          # Generate and run tests
    lpp tla /path/to/blueprint.json  # TLA+ validation
    lpp util logic_decoder myfile.py
    lpp agent deploy /path/to/project
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
        for arg in util_args:
            if "=" in arg:
                key, value = arg.split("=", 1)
                params[key] = value
            else:
                # Positional arg - use as target/project_path
                params["target"] = arg
                params["project_path"] = arg

        result = util.run(params)
        print(result)
        return 0 if "error" not in result else 1

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
    "compile": cmd_compile,
    "visualize": cmd_visualize,
    "validate": cmd_validate,
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
