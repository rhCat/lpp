"""
COMPUTE units for the L++ Coverage Analyzer.

These are the pure computation functions for tracking runtime coverage
of L++ blueprints. Implements state, transition, gate, action, and event
coverage tracking with comprehensive reporting.
"""

import json
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

from frame_py.loader import BlueprintLoader


# =============================================================================
# Blueprint Loading
# =============================================================================

def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "path": None, "error": "No path provided"}

    try:
        path = Path(path)
        if not path.exists():
            return {"blueprint": None, "path": None,
                    "error": f"File not found: {path}"}

        with open(path) as f:
            raw = json.load(f)

        loader = BlueprintLoader(raw)
        blueprint, loadError = loader.load()

        if loadError:
            return {"blueprint": None, "path": None, "error": loadError}

        # Convert to dict structure for processing
        bpData = {
            "id": blueprint.id,
            "name": blueprint.name,
            "version": blueprint.version,
            "description": blueprint.description,
            "states": {
                sid: {"description": s.description}
                for sid, s in blueprint.states.items()
            },
            "transitions": [
                {
                    "id": t.id,
                    "from": t.from_state,
                    "to": t.to_state,
                    "on_event": t.on_event,
                    "gates": list(t.gates),
                    "actions": list(t.actions)
                }
                for t in blueprint.transitions
            ],
            "gates": {
                gid: {"type": "expression", "expression": g.expression}
                for gid, g in blueprint.gates.items()
            },
            "actions": {
                aid: {"type": a.type.value}
                for aid, a in blueprint.actions.items()
            },
            "entry_state": blueprint.entry_state,
            "terminal_states": list(blueprint.terminal_states)
        }

        return {"blueprint": bpData, "path": str(path), "error": None}

    except Exception as e:
        return {"blueprint": None, "path": None, "error": str(e)}


# =============================================================================
# Coverage Initialization
# =============================================================================

def init_coverage(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize coverage tracking for a blueprint."""
    bp = params.get("blueprint")
    if not bp:
        return {
            "coverage_data": None,
            "state_hits": {},
            "transition_hits": {},
            "gate_hits": {},
            "action_hits": {},
            "event_hits": {}
        }

    # Initialize state hits (all states start at 0)
    stateHits = {sid: 0 for sid in bp["states"]}

    # Initialize transition hits
    transHits = {t["id"]: 0 for t in bp["transitions"]}

    # Initialize gate hits with true/false breakdown
    gateHits = {
        gid: {"total": 0, "true": 0, "false": 0}
        for gid in bp.get("gates", {})
    }

    # Initialize action hits
    actionHits = {aid: 0 for aid in bp.get("actions", {})}

    # Initialize event hits (from transitions)
    events = set()
    for t in bp["transitions"]:
        events.add(t["on_event"])
    eventHits = {evt: 0 for evt in events}

    coverageData = {
        "initialized_at": datetime.now().isoformat(),
        "blueprint_id": bp["id"],
        "blueprint_version": bp["version"]
    }

    return {
        "coverage_data": coverageData,
        "state_hits": stateHits,
        "transition_hits": transHits,
        "gate_hits": gateHits,
        "action_hits": actionHits,
        "event_hits": eventHits
    }


# =============================================================================
# Coverage Recording
# =============================================================================

def record_state(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record a state visit."""
    stateHits = params.get("state_hits", {}).copy()
    stateId = params.get("state_id")

    if stateId and stateId in stateHits:
        stateHits[stateId] = stateHits.get(stateId, 0) + 1
    elif stateId:
        stateHits[stateId] = 1

    return {"state_hits": stateHits}


def record_transition(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record a transition being taken."""
    transHits = params.get("transition_hits", {}).copy()
    transId = params.get("transition_id")

    if transId and transId in transHits:
        transHits[transId] = transHits.get(transId, 0) + 1
    elif transId:
        transHits[transId] = 1

    return {"transition_hits": transHits}


def record_gate(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record a gate evaluation with its result."""
    gateHits = params.get("gate_hits", {}).copy()
    gateId = params.get("gate_id")
    result = params.get("result", True)

    if gateId:
        if gateId not in gateHits:
            gateHits[gateId] = {"total": 0, "true": 0, "false": 0}

        gateHits[gateId]["total"] += 1
        if result:
            gateHits[gateId]["true"] += 1
        else:
            gateHits[gateId]["false"] += 1

    return {"gate_hits": gateHits}


def record_action(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record an action execution."""
    actionHits = params.get("action_hits", {}).copy()
    actionId = params.get("action_id")

    if actionId and actionId in actionHits:
        actionHits[actionId] = actionHits.get(actionId, 0) + 1
    elif actionId:
        actionHits[actionId] = 1

    return {"action_hits": actionHits}


def record_event(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record an event being dispatched."""
    eventHits = params.get("event_hits", {}).copy()
    eventName = params.get("event_name")

    if eventName and eventName in eventHits:
        eventHits[eventName] = eventHits.get(eventName, 0) + 1
    elif eventName:
        eventHits[eventName] = 1

    return {"event_hits": eventHits}


# =============================================================================
# Trace Import
# =============================================================================

def import_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Import trace data from a file and update coverage."""
    path = params.get("path")
    stateHits = params.get("state_hits", {}).copy()
    transHits = params.get("transition_hits", {}).copy()
    gateHits = params.get("gate_hits", {}).copy()
    actionHits = params.get("action_hits", {}).copy()
    eventHits = params.get("event_hits", {}).copy()

    if not path:
        return {
            "trace_data": None,
            "state_hits": stateHits,
            "transition_hits": transHits,
            "gate_hits": gateHits,
            "action_hits": actionHits,
            "event_hits": eventHits,
            "error": "No path provided"
        }

    try:
        tracePath = Path(path)
        if not tracePath.exists():
            return {
                "trace_data": None,
                "state_hits": stateHits,
                "transition_hits": transHits,
                "gate_hits": gateHits,
                "action_hits": actionHits,
                "event_hits": eventHits,
                "error": f"Trace file not found: {path}"
            }

        with open(tracePath) as f:
            traceData = json.load(f)

        # Process trace entries
        entries = traceData if isinstance(traceData, list) else traceData.get(
            "entries", traceData.get("trace", []))

        for entry in entries:
            entryType = entry.get("type", "")

            if entryType == "state" or "state" in entry:
                sid = entry.get("state_id", entry.get("state"))
                if sid:
                    stateHits[sid] = stateHits.get(sid, 0) + 1

            if entryType == "transition" or "transition_id" in entry:
                tid = entry.get("transition_id", entry.get("transition"))
                if tid:
                    transHits[tid] = transHits.get(tid, 0) + 1

            if entryType == "gate" or "gate_id" in entry:
                gid = entry.get("gate_id", entry.get("gate"))
                result = entry.get("result", True)
                if gid:
                    if gid not in gateHits:
                        gateHits[gid] = {"total": 0, "true": 0, "false": 0}
                    gateHits[gid]["total"] += 1
                    if result:
                        gateHits[gid]["true"] += 1
                    else:
                        gateHits[gid]["false"] += 1

            if entryType == "action" or "action_id" in entry:
                aid = entry.get("action_id", entry.get("action"))
                if aid:
                    actionHits[aid] = actionHits.get(aid, 0) + 1

            if entryType == "event" or "event" in entry:
                evt = entry.get("event_name", entry.get("event"))
                if evt:
                    eventHits[evt] = eventHits.get(evt, 0) + 1

        return {
            "trace_data": entries,
            "state_hits": stateHits,
            "transition_hits": transHits,
            "gate_hits": gateHits,
            "action_hits": actionHits,
            "event_hits": eventHits,
            "error": None
        }

    except Exception as e:
        return {
            "trace_data": None,
            "state_hits": stateHits,
            "transition_hits": transHits,
            "gate_hits": gateHits,
            "action_hits": actionHits,
            "event_hits": eventHits,
            "error": str(e)
        }


# =============================================================================
# Metrics Computation
# =============================================================================

def compute_metrics(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compute coverage metrics from hit data."""
    bp = params.get("blueprint")
    stateHits = params.get("state_hits", {})
    transHits = params.get("transition_hits", {})
    gateHits = params.get("gate_hits", {})
    actionHits = params.get("action_hits", {})
    eventHits = params.get("event_hits", {})

    if not bp:
        return {"metrics": None}

    # State coverage
    totalStates = len(bp["states"])
    coveredStates = sum(1 for h in stateHits.values() if h > 0)
    statePct = (coveredStates / totalStates * 100) if totalStates else 0

    # Transition coverage
    totalTrans = len(bp["transitions"])
    coveredTrans = sum(1 for h in transHits.values() if h > 0)
    transPct = (coveredTrans / totalTrans * 100) if totalTrans else 0

    # Gate coverage (evaluated at least once)
    totalGates = len(bp.get("gates", {}))
    coveredGates = sum(1 for g in gateHits.values() if g.get("total", 0) > 0)
    gatePct = (coveredGates / totalGates * 100) if totalGates else 0

    # Gate branch coverage (both true and false branches)
    branchTotal = totalGates * 2  # Each gate has 2 branches
    branchCovered = sum(
        (1 if g.get("true", 0) > 0 else 0) +
        (1 if g.get("false", 0) > 0 else 0)
        for g in gateHits.values()
    )
    branchPct = (branchCovered / branchTotal * 100) if branchTotal else 0

    # Action coverage
    totalActions = len(bp.get("actions", {}))
    coveredActions = sum(1 for h in actionHits.values() if h > 0)
    actionPct = (coveredActions / totalActions * 100) if totalActions else 0

    # Event coverage
    allEvents = set(t["on_event"] for t in bp["transitions"])
    totalEvents = len(allEvents)
    coveredEvents = sum(1 for e, h in eventHits.items()
                        if h > 0 and e in allEvents)
    eventPct = (coveredEvents / totalEvents * 100) if totalEvents else 0

    # Overall coverage (weighted average)
    weights = {
        "state": 0.25,
        "transition": 0.35,
        "gate": 0.20,
        "action": 0.15,
        "event": 0.05
    }
    overallPct = (
        statePct * weights["state"] +
        transPct * weights["transition"] +
        gatePct * weights["gate"] +
        actionPct * weights["action"] +
        eventPct * weights["event"]
    )

    metrics = {
        "computed_at": datetime.now().isoformat(),
        "blueprint_id": bp["id"],
        "overall_percentage": round(overallPct, 1),
        "state_coverage": {
            "total": totalStates,
            "covered": coveredStates,
            "percentage": round(statePct, 1),
            "uncovered": [s for s, h in stateHits.items() if h == 0]
        },
        "state_percentage": round(statePct, 1),
        "transition_coverage": {
            "total": totalTrans,
            "covered": coveredTrans,
            "percentage": round(transPct, 1),
            "uncovered": [t for t, h in transHits.items() if h == 0]
        },
        "transition_percentage": round(transPct, 1),
        "gate_coverage": {
            "total": totalGates,
            "covered": coveredGates,
            "percentage": round(gatePct, 1),
            "branch_coverage": round(branchPct, 1),
            "uncovered": [g for g, h in gateHits.items() if h.get("total", 0) == 0],
            "missing_true": [g for g, h in gateHits.items() if h.get("true", 0) == 0],
            "missing_false": [g for g, h in gateHits.items() if h.get("false", 0) == 0]
        },
        "action_coverage": {
            "total": totalActions,
            "covered": coveredActions,
            "percentage": round(actionPct, 1),
            "uncovered": [a for a, h in actionHits.items() if h == 0]
        },
        "event_coverage": {
            "total": totalEvents,
            "covered": coveredEvents,
            "percentage": round(eventPct, 1),
            "uncovered": [e for e in allEvents if eventHits.get(e, 0) == 0]
        },
        "hit_counts": {
            "states": dict(stateHits),
            "transitions": dict(transHits),
            "gates": {g: h.get("total", 0) for g, h in gateHits.items()},
            "actions": dict(actionHits),
            "events": dict(eventHits)
        }
    }

    return {"metrics": metrics}


# =============================================================================
# Report Generation
# =============================================================================

def generate_summary(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate a summary coverage report."""
    bp = params.get("blueprint")
    metrics = params.get("metrics")

    if not bp or not metrics:
        return {"report": "No metrics available"}

    lines = [
        "=" * 60,
        f"  COVERAGE SUMMARY: {bp['name']}",
        "=" * 60,
        "",
        f"  Overall Coverage: {metrics['overall_percentage']}%",
        "",
        "  Component Breakdown:",
        f"    States:      {metrics['state_coverage']['covered']:3d}/"
        f"{metrics['state_coverage']['total']:3d}  "
        f"({metrics['state_coverage']['percentage']:5.1f}%)",
        f"    Transitions: {metrics['transition_coverage']['covered']:3d}/"
        f"{metrics['transition_coverage']['total']:3d}  "
        f"({metrics['transition_coverage']['percentage']:5.1f}%)",
        f"    Gates:       {metrics['gate_coverage']['covered']:3d}/"
        f"{metrics['gate_coverage']['total']:3d}  "
        f"({metrics['gate_coverage']['percentage']:5.1f}%)",
        f"    Actions:     {metrics['action_coverage']['covered']:3d}/"
        f"{metrics['action_coverage']['total']:3d}  "
        f"({metrics['action_coverage']['percentage']:5.1f}%)",
        f"    Events:      {metrics['event_coverage']['covered']:3d}/"
        f"{metrics['event_coverage']['total']:3d}  "
        f"({metrics['event_coverage']['percentage']:5.1f}%)",
        "",
        f"  Gate Branch Coverage: {metrics['gate_coverage']['branch_coverage']}%",
        "",
        "=" * 60
    ]

    return {"report": "\n".join(lines)}


def generate_detailed(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate a detailed coverage report with hit counts."""
    bp = params.get("blueprint")
    metrics = params.get("metrics")
    stateHits = params.get("state_hits", {})
    transHits = params.get("transition_hits", {})
    gateHits = params.get("gate_hits", {})
    actionHits = params.get("action_hits", {})

    if not bp or not metrics:
        return {"report": "No metrics available"}

    lines = [
        "=" * 70,
        f"  DETAILED COVERAGE REPORT: {bp['name']}",
        "=" * 70,
        "",
        "  STATES",
        "  " + "-" * 66,
    ]

    for sid, hits in sorted(stateHits.items()):
        status = "[X]" if hits > 0 else "[ ]"
        desc = bp["states"].get(sid, {}).get("description", "")[:40]
        lines.append(f"    {status} {sid:25} hits={hits:4d}  {desc}")

    lines.extend([
        "",
        "  TRANSITIONS",
        "  " + "-" * 66,
    ])

    for trans in bp["transitions"]:
        tid = trans["id"]
        hits = transHits.get(tid, 0)
        status = "[X]" if hits > 0 else "[ ]"
        arrow = f"{trans['from']} --[{trans['on_event']}]--> {trans['to']}"
        lines.append(f"    {status} {tid:20} hits={hits:4d}  {arrow[:35]}")

    lines.extend([
        "",
        "  GATES",
        "  " + "-" * 66,
    ])

    for gid, data in sorted(gateHits.items()):
        total = data.get("total", 0)
        trueHits = data.get("true", 0)
        falseHits = data.get("false", 0)
        status = "[X]" if total > 0 else "[ ]"
        branchInfo = f"T={trueHits}, F={falseHits}"
        lines.append(f"    {status} {gid:25} hits={total:4d}  ({branchInfo})")

    lines.extend([
        "",
        "  ACTIONS",
        "  " + "-" * 66,
    ])

    for aid, hits in sorted(actionHits.items()):
        status = "[X]" if hits > 0 else "[ ]"
        atype = bp.get("actions", {}).get(aid, {}).get("type", "?")
        lines.append(f"    {status} {aid:30} hits={hits:4d}  type={atype}")

    lines.extend([
        "",
        "=" * 70
    ])

    return {"report": "\n".join(lines)}


def generate_gap_report(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate a gap analysis report with suggestions."""
    bp = params.get("blueprint")
    metrics = params.get("metrics")
    stateHits = params.get("state_hits", {})
    transHits = params.get("transition_hits", {})
    gateHits = params.get("gate_hits", {})
    actionHits = params.get("action_hits", {})

    if not bp or not metrics:
        return {"report": "No metrics available"}

    lines = [
        "=" * 70,
        f"  COVERAGE GAP ANALYSIS: {bp['name']}",
        "=" * 70,
        "",
    ]

    # Uncovered states
    uncoveredStates = [s for s, h in stateHits.items() if h == 0]
    if uncoveredStates:
        lines.append("  UNCOVERED STATES")
        lines.append("  " + "-" * 66)
        for sid in uncoveredStates:
            # Find how to reach this state
            incomingTrans = [t for t in bp["transitions"]
                             if t["to"] == sid and t["from"] != "*"]
            if incomingTrans:
                suggestion = (f"Try: dispatch('{incomingTrans[0]['on_event']}') "
                              f"from state '{incomingTrans[0]['from']}'")
            else:
                suggestion = "No incoming transitions found"
            lines.append(f"    - {sid}")
            lines.append(f"      Suggestion: {suggestion}")
        lines.append("")

    # Uncovered transitions
    uncoveredTrans = [t for t, h in transHits.items() if h == 0]
    if uncoveredTrans:
        lines.append("  UNCOVERED TRANSITIONS")
        lines.append("  " + "-" * 66)
        for tid in uncoveredTrans:
            trans = next(
                (t for t in bp["transitions"] if t["id"] == tid), None)
            if trans:
                gates = trans.get("gates", [])
                gateInfo = f" (gates: {', '.join(gates)})" if gates else ""
                lines.append(f"    - {tid}")
                lines.append(f"      Path: {trans['from']} --[{trans['on_event']}]--> "
                             f"{trans['to']}{gateInfo}")
                if gates:
                    lines.append(
                        f"      Suggestion: Ensure gates pass: {gates}")
        lines.append("")

    # Gates missing branch coverage
    missingTrue = [g for g, h in gateHits.items() if h.get("true", 0) == 0]
    missingFalse = [g for g, h in gateHits.items() if h.get("false", 0) == 0]

    if missingTrue or missingFalse:
        lines.append("  INCOMPLETE GATE BRANCH COVERAGE")
        lines.append("  " + "-" * 66)
        for gid in set(missingTrue + missingFalse):
            expr = bp.get("gates", {}).get(gid, {}).get("expression", "?")
            branches = []
            if gid in missingTrue:
                branches.append("true")
            if gid in missingFalse:
                branches.append("false")
            lines.append(f"    - {gid}: missing {', '.join(branches)} branch")
            lines.append(f"      Expression: {expr[:50]}")
        lines.append("")

    # Uncovered actions
    uncoveredActions = [a for a, h in actionHits.items() if h == 0]
    if uncoveredActions:
        lines.append("  UNCOVERED ACTIONS")
        lines.append("  " + "-" * 66)
        for aid in uncoveredActions:
            # Find which transitions use this action
            usingTrans = [t["id"] for t in bp["transitions"]
                          if aid in t.get("actions", [])]
            lines.append(f"    - {aid}")
            if usingTrans:
                lines.append(f"      Used by: {', '.join(usingTrans[:3])}")
            else:
                lines.append(
                    "      Warning: Action not used by any transition")
        lines.append("")

    if not any([uncoveredStates, uncoveredTrans, missingTrue, missingFalse,
                uncoveredActions]):
        lines.append("  No coverage gaps found! 100% coverage achieved.")
        lines.append("")

    lines.extend([
        "=" * 70
    ])

    return {"report": "\n".join(lines)}


# =============================================================================
# Export Functions
# =============================================================================

def export_html(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate an interactive HTML coverage report."""
    bp = params.get("blueprint")
    metrics = params.get("metrics")
    stateHits = params.get("state_hits", {})
    transHits = params.get("transition_hits", {})
    gateHits = params.get("gate_hits", {})
    actionHits = params.get("action_hits", {})
    outPath = params.get("path")

    if not bp or not metrics:
        return {"html": None, "path": None}

    # Color coding function
    def covColor(pct):
        if pct >= 80:
            return "#4caf50"  # green
        elif pct >= 50:
            return "#ff9800"  # orange
        else:
            return "#f44336"  # red

    def hitColor(hits):
        if hits > 0:
            return "#e8f5e9"  # light green
        else:
            return "#ffebee"  # light red

    overallColor = covColor(metrics["overall_percentage"])

    html = f"""<!DOCTYPE html>
<html>
<head>
    <title>Coverage Report: {bp['name']}</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; margin: 20px; }}
        h1 {{ color: #333; }}
        .summary {{ background: #f5f5f5; padding: 20px; border-radius: 8px; margin-bottom: 20px; }}
        .overall {{ font-size: 48px; font-weight: bold; color: {overallColor}; }}
        .metrics {{ display: flex; gap: 20px; flex-wrap: wrap; }}
        .metric {{ background: white; padding: 15px; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); min-width: 150px; }}
        .metric-value {{ font-size: 24px; font-weight: bold; }}
        .metric-label {{ color: #666; font-size: 12px; text-transform: uppercase; }}
        table {{ border-collapse: collapse; width: 100%; margin: 20px 0; }}
        th, td {{ padding: 10px; text-align: left; border-bottom: 1px solid #ddd; }}
        th {{ background: #f5f5f5; }}
        .hit {{ background: #e8f5e9; }}
        .miss {{ background: #ffebee; }}
        .section {{ margin: 30px 0; }}
        .bar {{ height: 20px; border-radius: 10px; background: #eee; overflow: hidden; }}
        .bar-fill {{ height: 100%; transition: width 0.3s; }}
    </style>
</head>
<body>
    <h1>Coverage Report: {bp['name']}</h1>
    <p>Generated: {metrics['computed_at']}</p>

    <div class="summary">
        <div class="overall">{metrics['overall_percentage']}%</div>
        <div>Overall Coverage</div>
    </div>

    <div class="metrics">
        <div class="metric">
            <div class="metric-value" style="color: {covColor(metrics['state_coverage']['percentage'])}">{metrics['state_coverage']['percentage']}%</div>
            <div class="metric-label">State Coverage</div>
            <div>{metrics['state_coverage']['covered']}/{metrics['state_coverage']['total']}</div>
        </div>
        <div class="metric">
            <div class="metric-value" style="color: {covColor(metrics['transition_coverage']['percentage'])}">{metrics['transition_coverage']['percentage']}%</div>
            <div class="metric-label">Transition Coverage</div>
            <div>{metrics['transition_coverage']['covered']}/{metrics['transition_coverage']['total']}</div>
        </div>
        <div class="metric">
            <div class="metric-value" style="color: {covColor(metrics['gate_coverage']['percentage'])}">{metrics['gate_coverage']['percentage']}%</div>
            <div class="metric-label">Gate Coverage</div>
            <div>{metrics['gate_coverage']['covered']}/{metrics['gate_coverage']['total']}</div>
        </div>
        <div class="metric">
            <div class="metric-value" style="color: {covColor(metrics['action_coverage']['percentage'])}">{metrics['action_coverage']['percentage']}%</div>
            <div class="metric-label">Action Coverage</div>
            <div>{metrics['action_coverage']['covered']}/{metrics['action_coverage']['total']}</div>
        </div>
    </div>

    <div class="section">
        <h2>States</h2>
        <table>
            <tr><th>State</th><th>Hits</th><th>Description</th></tr>
"""

    for sid, hits in sorted(stateHits.items()):
        cls = "hit" if hits > 0 else "miss"
        desc = bp["states"].get(sid, {}).get("description", "")
        html += f'            <tr class="{cls}"><td>{sid}</td><td>{hits}</td><td>{desc}</td></tr>\n'

    html += """        </table>
    </div>

    <div class="section">
        <h2>Transitions</h2>
        <table>
            <tr><th>ID</th><th>From</th><th>Event</th><th>To</th><th>Hits</th></tr>
"""

    for trans in bp["transitions"]:
        tid = trans["id"]
        hits = transHits.get(tid, 0)
        cls = "hit" if hits > 0 else "miss"
        html += f'            <tr class="{cls}"><td>{tid}</td><td>{trans["from"]}</td><td>{trans["on_event"]}</td><td>{trans["to"]}</td><td>{hits}</td></tr>\n'

    html += """        </table>
    </div>

    <div class="section">
        <h2>Gates</h2>
        <table>
            <tr><th>Gate</th><th>Total Hits</th><th>True</th><th>False</th><th>Expression</th></tr>
"""

    for gid, data in sorted(gateHits.items()):
        total = data.get("total", 0)
        cls = "hit" if total > 0 else "miss"
        expr = bp.get("gates", {}).get(gid, {}).get("expression", "")[:50]
        html += f'            <tr class="{cls}"><td>{gid}</td><td>{total}</td><td>{data.get("true", 0)}</td><td>{data.get("false", 0)}</td><td>{expr}</td></tr>\n'

    html += """        </table>
    </div>

    <div class="section">
        <h2>Actions</h2>
        <table>
            <tr><th>Action</th><th>Hits</th><th>Type</th></tr>
"""

    for aid, hits in sorted(actionHits.items()):
        cls = "hit" if hits > 0 else "miss"
        atype = bp.get("actions", {}).get(aid, {}).get("type", "?")
        html += f'            <tr class="{cls}"><td>{aid}</td><td>{hits}</td><td>{atype}</td></tr>\n'

    html += """        </table>
    </div>
</body>
</html>"""

    # Write to file if path provided
    if outPath:
        try:
            outFile = Path(outPath)
            if not outFile.suffix:
                outFile = outFile.with_suffix(".html")
            outFile.parent.mkdir(parents=True, exist_ok=True)
            outFile.write_text(html)
            return {"html": html, "path": str(outFile)}
        except Exception as e:
            return {"html": html, "path": None, "error": str(e)}

    return {"html": html, "path": None}


def export_json(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export coverage data as JSON."""
    bp = params.get("blueprint")
    metrics = params.get("metrics")
    stateHits = params.get("state_hits", {})
    transHits = params.get("transition_hits", {})
    gateHits = params.get("gate_hits", {})
    actionHits = params.get("action_hits", {})
    eventHits = params.get("event_hits", {})
    outPath = params.get("path")

    if not bp or not metrics:
        return {"json": None, "path": None}

    data = {
        "coverage_report": {
            "blueprint_id": bp["id"],
            "blueprint_name": bp["name"],
            "blueprint_version": bp["version"],
            "generated_at": datetime.now().isoformat(),
            "metrics": metrics,
            "raw_data": {
                "state_hits": stateHits,
                "transition_hits": transHits,
                "gate_hits": gateHits,
                "action_hits": actionHits,
                "event_hits": eventHits
            }
        }
    }

    jsonStr = json.dumps(data, indent=2)

    # Write to file if path provided
    if outPath:
        try:
            outFile = Path(outPath)
            if not outFile.suffix:
                outFile = outFile.with_suffix(".json")
            outFile.parent.mkdir(parents=True, exist_ok=True)
            outFile.write_text(jsonStr)
            return {"json": jsonStr, "path": str(outFile)}
        except Exception as e:
            return {"json": jsonStr, "path": None, "error": str(e)}

    return {"json": jsonStr, "path": None}


# =============================================================================
# Reset Functions
# =============================================================================

def reset_coverage(params: Dict[str, Any]) -> Dict[str, Any]:
    """Reset coverage data while keeping blueprint loaded."""
    bp = params.get("blueprint")
    result = init_coverage({"blueprint": bp})
    result.update({
        "metrics": None,
        "summary_report": None,
        "detailed_report": None,
        "gap_report": None,
        "html_report": None,
        "json_report": None
    })
    return result


def clear_all(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear all state including blueprint."""
    return {
        "blueprint": None,
        "blueprint_path": None,
        "coverage_data": None,
        "state_hits": {},
        "transition_hits": {},
        "gate_hits": {},
        "action_hits": {},
        "event_hits": {},
        "metrics": None,
        "summary_report": None,
        "detailed_report": None,
        "gap_report": None,
        "html_report": None,
        "json_report": None,
        "trace_data": None,
        "error": None
    }


# =============================================================================
# COMPUTE REGISTRY
# =============================================================================

COMPUTE_REGISTRY = {
    ("cov", "load_blueprint"): load_blueprint,
    ("cov", "init_coverage"): init_coverage,
    ("cov", "record_state"): record_state,
    ("cov", "record_transition"): record_transition,
    ("cov", "record_gate"): record_gate,
    ("cov", "record_action"): record_action,
    ("cov", "record_event"): record_event,
    ("cov", "import_trace"): import_trace,
    ("cov", "compute_metrics"): compute_metrics,
    ("cov", "generate_summary"): generate_summary,
    ("cov", "generate_detailed"): generate_detailed,
    ("cov", "generate_gap_report"): generate_gap_report,
    ("cov", "export_html"): export_html,
    ("cov", "export_json"): export_json,
    ("cov", "reset_coverage"): reset_coverage,
    ("cov", "clear_all"): clear_all,
}
