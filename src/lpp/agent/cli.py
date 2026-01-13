"""
L++ Agent CLI

Deploy and manage Claude Code agent documentation.

Usage:
    lpp-agent list                    List available agents
    lpp-agent show <agent>            Show agent documentation
    lpp-agent deploy <target>         Deploy agents to project
    lpp-agent deploy <target> --all   Deploy all agents
"""

import sys
import argparse
from pathlib import Path


def cmd_list(args: argparse.Namespace) -> int:
    """List available agents."""
    from lpp.agent import list_agents, get_agent_info

    print("Available L++ Agents:")
    print()

    for name in list_agents():
        info = get_agent_info(name)
        if info:
            status = "ready" if info["exists"] else "missing"
            print(f"  {name}")
            print(f"    Description: {info['description']}")
            print(f"    Model: {info['model']}")
            print(f"    Status: {status}")
            print()

    return 0


def cmd_show(args: argparse.Namespace) -> int:
    """Show agent documentation."""
    from lpp.agent import get_agent_content, get_agent_info

    agent_name = args.agent
    content = get_agent_content(agent_name)

    if content is None:
        info = get_agent_info(agent_name)
        if info is None:
            print(f"Error: Unknown agent '{agent_name}'")
        else:
            print(f"Error: Agent file not found at {info['path']}")
        return 1

    print(content)
    return 0


def cmd_deploy(args: argparse.Namespace) -> int:
    """Deploy agents to a project."""
    from lpp.agent import deploy_agents, create_claude_settings, list_agents

    target = args.target
    force = args.force

    if not Path(target).exists():
        print(f"Error: Target directory does not exist: {target}")
        return 1

    # Determine which agents to deploy
    agents = None  # All agents
    if args.agent and args.agent != "all":
        agents = [args.agent]
    elif args.all:
        agents = None  # All

    print(f"Deploying L++ agents to: {target}")
    print()

    results = deploy_agents(target, agents=agents, force=force)

    for agent, status in results.items():
        print(f"  {agent}: {status}")

    # Optionally create settings
    if args.settings:
        settings_path = create_claude_settings(target, agents=agents)
        print()
        print(f"Created settings: {settings_path}")

    print()
    print("Done!")
    return 0


def cmd_info(args: argparse.Namespace) -> int:
    """Show agent package info."""
    from lpp.agent import AGENT_DIR, list_agents

    print("L++ Agent Package")
    print()
    print(f"  Package location: {AGENT_DIR.parent}")
    print(f"  Agents directory: {AGENT_DIR}")
    print(f"  Available agents: {', '.join(list_agents())}")
    print()
    print("Deployment target:")
    print("  <project>/.claude/agents/lppcoder.md")
    print("  <project>/.claude/agents/lppoperator.md")
    return 0


def main(argv=None) -> int:
    """Main entry point."""
    parser = argparse.ArgumentParser(
        prog="lpp-agent",
        description="L++ Agent Documentation Manager",
    )

    subparsers = parser.add_subparsers(dest="command", help="Commands")

    # list command
    list_parser = subparsers.add_parser("list", help="List available agents")
    list_parser.set_defaults(func=cmd_list)

    # show command
    show_parser = subparsers.add_parser("show", help="Show agent documentation")
    show_parser.add_argument("agent", help="Agent name (e.g., lppcoder)")
    show_parser.set_defaults(func=cmd_show)

    # deploy command
    deploy_parser = subparsers.add_parser("deploy", help="Deploy agents to project")
    deploy_parser.add_argument("target", help="Target project directory")
    deploy_parser.add_argument(
        "agent",
        nargs="?",
        default="all",
        help="Agent to deploy (default: all)"
    )
    deploy_parser.add_argument(
        "--all", "-a",
        action="store_true",
        help="Deploy all agents"
    )
    deploy_parser.add_argument(
        "--force", "-f",
        action="store_true",
        help="Overwrite existing files"
    )
    deploy_parser.add_argument(
        "--settings", "-s",
        action="store_true",
        help="Also create/update .claude/settings.json"
    )
    deploy_parser.set_defaults(func=cmd_deploy)

    # info command
    info_parser = subparsers.add_parser("info", help="Show package info")
    info_parser.set_defaults(func=cmd_info)

    args = parser.parse_args(argv)

    if args.command is None:
        parser.print_help()
        return 0

    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
