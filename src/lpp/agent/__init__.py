"""
L++ Agent Documentation

Pre-configured Claude Code agents for L++ development.

Available Agents:
    lppcoder    - Code generation agent (generates tests automatically)
    lppoperator - Workflow operator agent (runs and manages workflows)

Usage:
    # List available agents
    from lpp.agent import list_agents, get_agent_info
    agents = list_agents()

    # Deploy agents to a project
    from lpp.agent import deploy_agents
    deploy_agents("/path/to/project")

    # CLI
    lpp-agent list
    lpp-agent deploy /path/to/project
    lpp-agent show lppcoder
"""

import os
import shutil
from pathlib import Path
from typing import Dict, List, Optional, Any

# Package directory containing agent definitions
AGENT_DIR = Path(__file__).parent / "agents"

# Available agents
AGENTS = {
    "lppcoder": {
        "name": "lppcoder",
        "file": "lppcoder.md",
        "description": "L++ code generation agent - generates tests automatically after code changes",
        "model": "opus",
        "color": "blue",
    },
    "lppoperator": {
        "name": "lppoperator",
        "file": "lppoperator.md",
        "description": "L++ workflow operator - runs and manages L++ workflows",
        "model": "opus",
        "color": "green",
    },
}


def list_agents() -> List[str]:
    """List all available agent names."""
    return list(AGENTS.keys())


def get_agent_info(name: str) -> Optional[Dict[str, Any]]:
    """
    Get information about an agent.

    Args:
        name: Agent name (e.g., "lppcoder")

    Returns:
        Dict with agent info or None if not found
    """
    if name not in AGENTS:
        return None

    info = AGENTS[name].copy()
    agent_path = AGENT_DIR / info["file"]
    info["path"] = str(agent_path)
    info["exists"] = agent_path.exists()

    return info


def get_agent_content(name: str) -> Optional[str]:
    """
    Get the content of an agent markdown file.

    Args:
        name: Agent name (e.g., "lppcoder")

    Returns:
        Agent markdown content or None if not found
    """
    info = get_agent_info(name)
    if not info or not info["exists"]:
        return None

    return Path(info["path"]).read_text()


def deploy_agents(
    target_dir: str,
    agents: Optional[List[str]] = None,
    force: bool = False
) -> Dict[str, str]:
    """
    Deploy agent documentation to a project's .claude/agents/ directory.

    Args:
        target_dir: Target project directory
        agents: List of agent names to deploy (default: all)
        force: Overwrite existing files

    Returns:
        Dict mapping agent name to deployment status
    """
    target = Path(target_dir)
    if not target.exists():
        raise ValueError(f"Target directory does not exist: {target_dir}")

    # Create .claude/agents/ directory
    agents_dir = target / ".claude" / "agents"
    agents_dir.mkdir(parents=True, exist_ok=True)

    # Determine which agents to deploy
    to_deploy = agents if agents else list_agents()

    results = {}
    for agent_name in to_deploy:
        info = get_agent_info(agent_name)
        if not info:
            results[agent_name] = f"error: unknown agent '{agent_name}'"
            continue

        if not info["exists"]:
            results[agent_name] = f"error: agent file not found"
            continue

        src = Path(info["path"])
        dst = agents_dir / info["file"]

        if dst.exists() and not force:
            results[agent_name] = "skipped: already exists (use force=True)"
            continue

        shutil.copy(src, dst)
        results[agent_name] = f"deployed to {dst}"

    return results


def create_claude_settings(
    target_dir: str,
    agents: Optional[List[str]] = None
) -> str:
    """
    Create or update .claude/settings.json with agent configurations.

    Args:
        target_dir: Target project directory
        agents: List of agents to configure (default: all)

    Returns:
        Path to settings file
    """
    import json

    target = Path(target_dir)
    settings_dir = target / ".claude"
    settings_dir.mkdir(parents=True, exist_ok=True)

    settings_file = settings_dir / "settings.json"

    # Load existing settings or create new
    if settings_file.exists():
        with open(settings_file) as f:
            settings = json.load(f)
    else:
        settings = {}

    # Add agent configurations
    if "agents" not in settings:
        settings["agents"] = {}

    to_configure = agents if agents else list_agents()

    for agent_name in to_configure:
        info = get_agent_info(agent_name)
        if info:
            settings["agents"][agent_name] = {
                "file": f"agents/{info['file']}",
                "model": info.get("model", "opus"),
                "description": info.get("description", ""),
            }

    with open(settings_file, "w") as f:
        json.dump(settings, f, indent=2)

    return str(settings_file)


__all__ = [
    "AGENTS",
    "list_agents",
    "get_agent_info",
    "get_agent_content",
    "deploy_agents",
    "create_claude_settings",
]
