"""
L++ Agent CLI

Deploy and manage Claude Code agent documentation.

Usage:
    lpp-agent list                    List available agents
    lpp-agent show <agent>            Show agent documentation
    lpp-agent deploy <target>         Deploy agents to project
    lpp-agent deploy <target> --all   Deploy all agents
    lpp-agent tlc <blueprint>         Run TLC model checker
    lpp-agent tlaps <blueprint>       Run TLAPS prover
    lpp-agent learn                   Show L++ essence for agents
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
    from lpp.agent import deploy_agents, create_claude_settings

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


def cmd_tlc(args: argparse.Namespace) -> int:
    """Run TLC model checker on a blueprint."""
    import json
    import subprocess
    import tempfile
    import os

    blueprint_path = Path(args.blueprint)
    if not blueprint_path.exists():
        print(f"Error: Blueprint not found: {blueprint_path}")
        return 1

    # Load blueprint
    with open(blueprint_path) as f:
        bp = json.load(f)

    if 'states' not in bp or 'transitions' not in bp:
        print("Error: Not a valid L++ blueprint (missing states/transitions)")
        return 1

    bp_id = bp.get('id', blueprint_path.stem)
    print(f"Running TLC on: {bp_id}")
    print()

    # Generate TLA+ spec
    spec = _generateTlcSpec(bp, bp_id)

    # Write to temp file and run TLC
    with tempfile.TemporaryDirectory() as tmpdir:
        spec_path = os.path.join(tmpdir, f"{bp_id}.tla")
        cfg_path = os.path.join(tmpdir, f"{bp_id}.cfg")

        with open(spec_path, 'w') as f:
            f.write(spec)

        with open(cfg_path, 'w') as f:
            f.write(_generateTlcConfig(bp))

        try:
            result = subprocess.run(
                ['tlc', '-config', cfg_path, spec_path],
                capture_output=True,
                text=True,
                timeout=120
            )
            print(result.stdout)
            if result.stderr:
                print(result.stderr)

            if result.returncode == 0:
                print("TLC: Model checking completed successfully")
                return 0
            else:
                print(f"TLC: Model checking failed (exit code {result.returncode})")
                return 1

        except FileNotFoundError:
            print("Error: TLC not found in PATH")
            print("Install TLA+ tools: https://github.com/tlaplus/tlaplus")
            return 1
        except subprocess.TimeoutExpired:
            print("Error: TLC timed out after 120 seconds")
            return 1


def cmd_tlaps(args: argparse.Namespace) -> int:
    """Run TLAPS prover on a blueprint."""
    import subprocess
    import sys as _sys

    blueprint_path = Path(args.blueprint)
    if not blueprint_path.exists():
        print(f"Error: Blueprint not found: {blueprint_path}")
        return 1

    # Use the existing tlaps_proof_generator
    from lpp.agent import AGENT_DIR
    utils = AGENT_DIR.parent.parent.parent.parent / "utils"
    prover_path = utils / "tlaps_prover" / "tlaps_proof_generator.py"

    if not prover_path.exists():
        print(f"Error: TLAPS prover not found at {prover_path}")
        return 1

    cmd = [_sys.executable, str(prover_path), str(blueprint_path)]
    if args.verify:
        cmd.append('--verify')
    if args.output:
        cmd.extend(['--output', args.output])

    result = subprocess.run(cmd)
    return result.returncode


def cmd_learn(args: argparse.Namespace) -> int:
    """Show L++ essence for agents to learn."""
    from lpp.agent import AGENT_DIR

    essence_path = AGENT_DIR / "essence.md"
    if essence_path.exists():
        print(essence_path.read_text())
    else:
        # Inline essence if file doesn't exist
        print(_getEssence())
    return 0


def _generateTlcSpec(bp: dict, moduleName: str) -> str:
    """Generate TLA+ spec for TLC model checking."""
    states = list(bp.get('states', {}).keys())
    transitions = bp.get('transitions', [])
    termStates = bp.get('terminal_states', {})
    terminals = list(termStates.keys()) if isinstance(termStates, dict) else list(termStates)
    entryState = bp.get('entry_state', states[0] if states else 'idle')

    def sanitize(s):
        return s.replace('-', '_').replace('.', '_').replace(':', '_')

    lines = []
    lines.append(f"---- MODULE {sanitize(moduleName)} ----")
    lines.append("EXTENDS Naturals")
    lines.append("")
    lines.append("VARIABLES state")
    lines.append("")
    lines.append("States == {" + ", ".join(f'"{s}"' for s in states) + "}")
    lines.append("TerminalStates == {" + ", ".join(f'"{t}"' for t in terminals) + "}")
    lines.append("")
    lines.append(f'Init == state = "{entryState}"')
    lines.append("")

    # Transitions
    for i, trans in enumerate(transitions):
        tId = sanitize(trans.get('id', f't{i}'))
        fromState = trans.get('from', '*')
        toState = trans.get('to')

        lines.append(f"{tId} ==")
        if fromState == '*':
            lines.append("    /\\ TRUE")
        else:
            lines.append(f'    /\\ state = "{fromState}"')
        lines.append(f'    /\\ state\' = "{toState}"')
        lines.append("")

    # Next
    transNames = [sanitize(t.get('id', f't{i}')) for i, t in enumerate(transitions)]
    if transNames:
        lines.append("Next == " + " \\/ ".join(transNames))
    else:
        lines.append("Next == FALSE")
    lines.append("")

    lines.append("Spec == Init /\\ [][Next]_<<state>>")
    lines.append("")
    lines.append("TypeOK == state \\in States")
    lines.append("")
    lines.append("====")

    return "\n".join(lines)


def _generateTlcConfig(bp: dict) -> str:
    """Generate TLC config file."""
    # CHECK_DEADLOCK FALSE because terminal states are valid endpoints
    return """SPECIFICATION Spec
INVARIANT TypeOK
CHECK_DEADLOCK FALSE
"""


def _getEssence() -> str:
    """Return the L++ essence document."""
    return '''# L++ Essence: The Logic CNC Machine

## What is L++?
L++ is a deterministic framework for building formally verifiable state machines.
It separates **Bone** (eternal logic) from **Flesh** (volatile compute).

## The 4 Axioms
1. **Silicon is Deterministic** - Randomness in software is engineering failure
2. **Symbolic Sovereignty** - The JSON Blueprint is the absolute source of truth
3. **Separation of Bone and Flesh** - Logic (rules) and Compute (tasks) must never intertwine
4. **The TLAPS Seal** - Production requires mathematical proof, not empirical hope

## The Trinity
All complexity reduces to three constructs:
- **TRANSITION** - The Navigator (moves state pointer)
- **GATE** - The Judge (boolean guards)
- **ACTION** - The Scribe/Messenger (mutations and I/O)

## The 4 Atoms
- **EVALUATE** - Boolean boundary checks
- **MUTATE** - Deterministic context updates
- **DISPATCH** - Hermetic I/O to external world
- **TRANSITION** - Atomic state pointer movement

## Blueprint Structure (v0.2.0)
```json
{
  "$schema": "lpp/v0.2.0",
  "id": "unique_id",
  "context_schema": { "properties": {...} },
  "states": { "idle": {}, "processing": {}, ... },
  "entry_state": "idle",
  "terminal_states": {
    "done": { "output_schema": {...}, "invariants_guaranteed": [...] },
    "error": { "output_schema": {...} }
  },
  "gates": { "gate_id": { "type": "expression", "expression": "..." } },
  "actions": { "action_id": { "type": "compute|set|emit", ... } },
  "transitions": [
    { "id": "t1", "from": "idle", "to": "processing", "on_event": "START", "gates": [], "actions": [] }
  ]
}
```

## Verification Pipeline
```bash
./deploy.sh docs      # Regenerate documentation
./deploy.sh validate  # TLA+ validation (TLC model checker)
./deploy.sh tests     # Generate comprehensive tests
./test_all.sh         # Run all tests with coverage
```

## Two Coverage Models
1. **Blueprint Coverage** - Infrastructure (state machine flows)
2. **Python Coverage** - Features (compute function logic)

## Key Principles
- Compute functions are **hermetic**: input is dict, output is dict
- Terminal states define **contracts** (output_schema, invariants_guaranteed)
- Assemblies compose components via **input_map/output_map** wiring
- TLC exhaustively checks state space; TLAPS proves mathematical properties

## Commands
- `lpp-agent tlc <blueprint.json>` - Run TLC model checker
- `lpp-agent tlaps <blueprint.json> --verify` - Run TLAPS prover
- `lpp-agent learn` - Show this essence document
'''


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

    # tlc command
    tlc_parser = subparsers.add_parser("tlc", help="Run TLC model checker")
    tlc_parser.add_argument("blueprint", help="Blueprint JSON file")
    tlc_parser.set_defaults(func=cmd_tlc)

    # tlaps command
    tlaps_parser = subparsers.add_parser("tlaps", help="Run TLAPS prover")
    tlaps_parser.add_argument("blueprint", help="Blueprint JSON file")
    tlaps_parser.add_argument(
        "--verify", "-v",
        action="store_true",
        help="Run TLAPS verification after generating"
    )
    tlaps_parser.add_argument(
        "--output", "-o",
        help="Output directory for TLA+ files"
    )
    tlaps_parser.set_defaults(func=cmd_tlaps)

    # learn command
    learn_parser = subparsers.add_parser(
        "learn",
        help="Show L++ essence for agents"
    )
    learn_parser.set_defaults(func=cmd_learn)

    args = parser.parse_args(argv)

    if args.command is None:
        parser.print_help()
        return 0

    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
