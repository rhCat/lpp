"""
COMPUTE units for L++ Canvas.
Pure functions: params: dict -> result: dict.
Blueprint studio for creating, reviewing, auditing, and editing L++ blueprints.
"""

import json
import os
import re
import subprocess
import tempfile
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


def initNew(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize a new empty blueprint."""
    blueprint = {
        "$schema": "lpp/v0.1.2",
        "id": "new_blueprint",
        "name": "New Blueprint",
        "version": "1.0.0",
        "description": "",
        "context_schema": {"properties": {}},
        "states": {"idle": {"description": "Initial state"}},
        "transitions": [],
        "gates": {},
        "actions": {},
        "entry_state": "idle",
        "terminal_states": []
    }
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True,
        "mode": "create"
    }


def loadBlueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load blueprint from file."""
    path = params.get("path", "")
    if not path:
        return {"blueprint": None, "blueprint_json": None, "error": "No path"}
    try:
        p = Path(path)
        if not p.exists():
            return {"blueprint": None, "blueprint_json": None,
                    "error": f"File not found: {path}"}
        content = p.read_text()
        blueprint = json.loads(content)
        if not blueprint.get("$schema", "").startswith("lpp"):
            return {"blueprint": None, "blueprint_json": None,
                    "error": "Not a valid L++ blueprint"}
        return {"blueprint": blueprint, "blueprint_json": content,
                "error": None}
    except json.JSONDecodeError as e:
        return {"blueprint": None, "blueprint_json": None,
                "error": f"JSON parse error: {e}"}
    except Exception as e:
        return {"blueprint": None, "blueprint_json": None,
                "error": str(e)}


def createBlueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Create blueprint with given name."""
    name = params.get("name", "New Blueprint")
    blueprint = params.get("blueprint", {})
    if blueprint:
        blueprint["name"] = name
        blueprint["id"] = name.lower().replace(" ", "_")
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def selectNode(params: Dict[str, Any]) -> Dict[str, Any]:
    """Select a node for editing."""
    blueprint = params.get("blueprint", {})
    nodeId = params.get("node_id", "")
    nodeType = params.get("node_type", "state")
    nodeData = None
    if nodeType == "state":
        nodeData = blueprint.get("states", {}).get(nodeId)
        if nodeData:
            nodeData = {"id": nodeId, **nodeData}
    elif nodeType == "transition":
        for t in blueprint.get("transitions", []):
            if t.get("id") == nodeId:
                nodeData = t
                break
    elif nodeType == "gate":
        nodeData = blueprint.get("gates", {}).get(nodeId)
        if nodeData:
            nodeData = {"id": nodeId, **nodeData}
    elif nodeType == "action":
        nodeData = blueprint.get("actions", {}).get(nodeId)
        if nodeData:
            nodeData = {"id": nodeId, **nodeData}
    return {"node_data": nodeData, "edit_buffer": dict(nodeData) if nodeData
            else {}}


def applyEdit(params: Dict[str, Any]) -> Dict[str, Any]:
    """Apply edits to selected node."""
    blueprint = dict(params.get("blueprint", {}))
    nodeId = params.get("node_id", "")
    nodeType = params.get("node_type", "state")
    editBuffer = params.get("edit_buffer", {})
    if nodeType == "state":
        states = dict(blueprint.get("states", {}))
        newId = editBuffer.pop("id", nodeId)
        if newId != nodeId:
            if nodeId in states:
                del states[nodeId]
            _updateStateRefs(blueprint, nodeId, newId)
        states[newId] = editBuffer
        blueprint["states"] = states
    elif nodeType == "transition":
        transitions = list(blueprint.get("transitions", []))
        for i, t in enumerate(transitions):
            if t.get("id") == nodeId:
                transitions[i] = editBuffer
                break
        blueprint["transitions"] = transitions
    elif nodeType == "gate":
        gates = dict(blueprint.get("gates", {}))
        newId = editBuffer.pop("id", nodeId)
        if newId != nodeId and nodeId in gates:
            del gates[nodeId]
            _updateGateRefs(blueprint, nodeId, newId)
        gates[newId] = editBuffer
        blueprint["gates"] = gates
    elif nodeType == "action":
        actions = dict(blueprint.get("actions", {}))
        newId = editBuffer.pop("id", nodeId)
        if newId != nodeId and nodeId in actions:
            del actions[nodeId]
            _updateActionRefs(blueprint, nodeId, newId)
        actions[newId] = editBuffer
        blueprint["actions"] = actions
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def _updateStateRefs(bp: dict, oldId: str, newId: str):
    """Update all references to a renamed state."""
    for t in bp.get("transitions", []):
        if t.get("from") == oldId:
            t["from"] = newId
        if t.get("to") == oldId:
            t["to"] = newId
    if bp.get("entry_state") == oldId:
        bp["entry_state"] = newId
    terminals = bp.get("terminal_states", [])
    if oldId in terminals:
        terminals[terminals.index(oldId)] = newId


def _updateGateRefs(bp: dict, oldId: str, newId: str):
    """Update all references to a renamed gate."""
    for t in bp.get("transitions", []):
        gates = t.get("gates", [])
        if oldId in gates:
            gates[gates.index(oldId)] = newId


def _updateActionRefs(bp: dict, oldId: str, newId: str):
    """Update all references to a renamed action."""
    for t in bp.get("transitions", []):
        actions = t.get("actions", [])
        if oldId in actions:
            actions[actions.index(oldId)] = newId


def deleteNode(params: Dict[str, Any]) -> Dict[str, Any]:
    """Delete selected node."""
    blueprint = dict(params.get("blueprint", {}))
    nodeId = params.get("node_id", "")
    nodeType = params.get("node_type", "state")
    if nodeType == "state":
        states = dict(blueprint.get("states", {}))
        if nodeId in states:
            del states[nodeId]
        blueprint["states"] = states
        blueprint["transitions"] = [
            t for t in blueprint.get("transitions", [])
            if t.get("from") != nodeId and t.get("to") != nodeId
        ]
    elif nodeType == "transition":
        blueprint["transitions"] = [
            t for t in blueprint.get("transitions", [])
            if t.get("id") != nodeId
        ]
    elif nodeType == "gate":
        gates = dict(blueprint.get("gates", {}))
        if nodeId in gates:
            del gates[nodeId]
        blueprint["gates"] = gates
        for t in blueprint.get("transitions", []):
            if nodeId in t.get("gates", []):
                t["gates"].remove(nodeId)
    elif nodeType == "action":
        actions = dict(blueprint.get("actions", {}))
        if nodeId in actions:
            del actions[nodeId]
        blueprint["actions"] = actions
        for t in blueprint.get("transitions", []):
            if nodeId in t.get("actions", []):
                t["actions"].remove(nodeId)
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def addState(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add new state."""
    blueprint = dict(params.get("blueprint", {}))
    stateData = params.get("state_data", {})
    stateId = stateData.get("id", f"state_{len(blueprint.get('states', {}))}")
    states = dict(blueprint.get("states", {}))
    states[stateId] = {"description": stateData.get("description", "")}
    blueprint["states"] = states
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def addTransition(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add new transition."""
    blueprint = dict(params.get("blueprint", {}))
    transData = params.get("transition_data", {})
    transitions = list(blueprint.get("transitions", []))
    transId = transData.get("id",
                            f"t_{len(transitions)}")
    newTrans = {
        "id": transId,
        "from": transData.get("from", "idle"),
        "to": transData.get("to", "idle"),
        "on_event": transData.get("on_event", "EVENT"),
        "gates": transData.get("gates", []),
        "actions": transData.get("actions", [])
    }
    transitions.append(newTrans)
    blueprint["transitions"] = transitions
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def addGate(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add new gate."""
    blueprint = dict(params.get("blueprint", {}))
    gateData = params.get("gate_data", {})
    gateId = gateData.get("id", f"g_{len(blueprint.get('gates', {}))}")
    gates = dict(blueprint.get("gates", {}))
    gates[gateId] = {
        "type": gateData.get("type", "expression"),
        "expression": gateData.get("expression", "True")
    }
    blueprint["gates"] = gates
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def addAction(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add new action."""
    blueprint = dict(params.get("blueprint", {}))
    actionData = params.get("action_data", {})
    actionId = actionData.get("id", f"a_{len(blueprint.get('actions', {}))}")
    actions = dict(blueprint.get("actions", {}))
    actions[actionId] = {
        "type": actionData.get("type", "set"),
        "target": actionData.get("target", ""),
        "value": actionData.get("value")
    }
    blueprint["actions"] = actions
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def runTlc(params: Dict[str, Any]) -> Dict[str, Any]:
    """Run TLC validation on blueprint."""
    blueprint = params.get("blueprint", {})
    if not blueprint:
        return {"tlc_result": None, "tlc_errors": [], "tlc_passed": False,
                "error": "No blueprint"}
    try:
        import sys
        sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent /
                               "src"))
        from frame_py.tla_validator import validate_with_tlc
        success, output = validate_with_tlc(blueprint, timeout=60)
        errors = []
        if not success:
            errorLines = [ln for ln in output.split("\n")
                          if "Error" in ln or "error" in ln.lower()]
            errors = errorLines[:10]
        result = {
            "passed": success,
            "output": output[:2000],
            "states": None,
            "distinct": None,
            "depth": None
        }
        if success:
            statesMatch = re.search(r'(\d+) states generated', output)
            distinctMatch = re.search(r'(\d+) distinct states', output)
            depthMatch = re.search(r'depth.*?(\d+)', output, re.IGNORECASE)
            if statesMatch:
                result["states"] = int(statesMatch.group(1))
            if distinctMatch:
                result["distinct"] = int(distinctMatch.group(1))
            if depthMatch:
                result["depth"] = int(depthMatch.group(1))
        return {"tlc_result": result, "tlc_errors": errors,
                "tlc_passed": success, "error": None}
    except Exception as e:
        return {"tlc_result": None, "tlc_errors": [str(e)],
                "tlc_passed": False, "error": str(e)}


def analyzePaths(params: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze all execution paths and states."""
    blueprint = params.get("blueprint", {})
    states = list(blueprint.get("states", {}).keys())
    transitions = blueprint.get("transitions", [])
    entryState = blueprint.get("entry_state", "idle")
    terminalStates = set(blueprint.get("terminal_states", []))
    graph = defaultdict(list)
    for t in transitions:
        fromState = t.get("from", "")
        toState = t.get("to", "")
        event = t.get("on_event", "")
        if fromState == "*":
            for s in states:
                graph[s].append((toState, event, t.get("id")))
        else:
            graph[fromState].append((toState, event, t.get("id")))
    paths = []
    visited = set()

    def dfs(state: str, path: List[str], events: List[str]):
        if len(path) > 20:
            return
        if state in terminalStates:
            paths.append({"states": list(path), "events": list(events)})
            return
        if state in visited and len(path) > 1:
            return
        visited.add(state)
        for nextState, event, tId in graph.get(state, []):
            dfs(nextState, path + [nextState], events + [event])
        visited.discard(state)

    dfs(entryState, [entryState], [])
    reachable = set()

    def bfsReach(start: str):
        queue = [start]
        seen = set()
        while queue:
            s = queue.pop(0)
            if s in seen:
                continue
            seen.add(s)
            reachable.add(s)
            for nextState, _, _ in graph.get(s, []):
                if nextState not in seen:
                    queue.append(nextState)

    bfsReach(entryState)
    unreachable = [s for s in states if s not in reachable]
    deadlocks = []
    for s in states:
        if s not in terminalStates and not graph.get(s):
            deadlocks.append(s)
    reachability = {
        "reachable": list(reachable),
        "unreachable": unreachable
    }
    return {
        "paths": paths[:100],
        "path_count": len(paths),
        "states_list": states,
        "state_count": len(states),
        "reachability": reachability,
        "deadlocks": deadlocks
    }


def initSimulation(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize simulation at entry state."""
    blueprint = params.get("blueprint", {})
    entryState = blueprint.get("entry_state", "idle")
    ctxSchema = blueprint.get("context_schema", {}).get("properties", {})
    simContext = {}
    for k, v in ctxSchema.items():
        simContext[k] = v.get("default")
    availEvents = _getAvailableEvents(blueprint, entryState)
    return {
        "sim_state": entryState,
        "sim_context": simContext,
        "sim_history": [{"step": 0, "state": entryState, "event": None,
                         "context": dict(simContext)}],
        "sim_available_events": availEvents,
        "sim_step_count": 0
    }


def _getAvailableEvents(blueprint: dict, state: str) -> List[str]:
    """Get events available at given state."""
    events = []
    for t in blueprint.get("transitions", []):
        if t.get("from") == state or t.get("from") == "*":
            events.append(t.get("on_event", ""))
    return list(set(events))


def simStep(params: Dict[str, Any]) -> Dict[str, Any]:
    """Execute simulation step with given event."""
    blueprint = params.get("blueprint", {})
    simState = params.get("sim_state", "idle")
    simContext = dict(params.get("sim_context", {}))
    simHistory = list(params.get("sim_history", []))
    event = params.get("event", "")
    matchedTrans = None
    for t in blueprint.get("transitions", []):
        if (t.get("from") == simState or t.get("from") == "*"):
            if t.get("on_event") == event:
                gatesPassed = True
                for gId in t.get("gates", []):
                    gate = blueprint.get("gates", {}).get(gId, {})
                    if gate.get("type") == "expression":
                        expr = gate.get("expression", "True")
                        try:
                            if not _safeEval(expr, simContext):
                                gatesPassed = False
                                break
                        except:
                            gatesPassed = False
                            break
                if gatesPassed:
                    matchedTrans = t
                    break
    if matchedTrans:
        for aId in matchedTrans.get("actions", []):
            action = blueprint.get("actions", {}).get(aId, {})
            if action.get("type") == "set":
                target = action.get("target", "")
                value = action.get("value")
                if action.get("value_from"):
                    value = simContext.get(action["value_from"])
                simContext[target] = value
        simState = matchedTrans.get("to", simState)
    stepCount = len(simHistory)
    simHistory.append({
        "step": stepCount,
        "state": simState,
        "event": event,
        "transition": matchedTrans.get("id") if matchedTrans else None,
        "context": dict(simContext)
    })
    availEvents = _getAvailableEvents(blueprint, simState)
    return {
        "sim_state": simState,
        "sim_context": simContext,
        "sim_history": simHistory,
        "sim_available_events": availEvents,
        "sim_step_count": stepCount
    }


def simDispatch(params: Dict[str, Any]) -> Dict[str, Any]:
    """Dispatch event with payload in simulation."""
    blueprint = params.get("blueprint", {})
    simState = params.get("sim_state", "idle")
    simContext = dict(params.get("sim_context", {}))
    event = params.get("event", "")
    payload = params.get("payload", {})
    if payload:
        simContext.update(payload)
    return simStep({
        "blueprint": blueprint,
        "sim_state": simState,
        "sim_context": simContext,
        "sim_history": params.get("sim_history", []),
        "event": event
    })


def _safeEval(expr: str, ctx: dict) -> bool:
    """Safely evaluate boolean expression."""
    allowed = {"True": True, "False": False, "None": None,
               "and": None, "or": None, "not": None, "in": None,
               "is": None}
    try:
        code = compile(expr, "<expr>", "eval")
        for name in code.co_names:
            if name not in allowed and name not in ctx:
                return False
        return eval(expr, {"__builtins__": {}}, ctx)
    except:
        return False


def computeClusters(params: Dict[str, Any]) -> Dict[str, Any]:
    """Compute state clusters and dependencies."""
    blueprint = params.get("blueprint", {})
    states = list(blueprint.get("states", {}).keys())
    transitions = blueprint.get("transitions", [])
    deps = defaultdict(set)
    revDeps = defaultdict(set)
    for t in transitions:
        fromState = t.get("from", "")
        toState = t.get("to", "")
        if fromState != "*":
            deps[toState].add(fromState)
            revDeps[fromState].add(toState)
        else:
            for s in states:
                deps[toState].add(s)
                revDeps[s].add(toState)
    visited = set()
    sortedStates = []

    def topoSort(state: str):
        if state in visited:
            return
        visited.add(state)
        for dep in deps.get(state, []):
            topoSort(dep)
        sortedStates.append(state)

    for s in states:
        topoSort(s)
    clusters = []
    clusterMap = {}
    clusterIdx = 0
    for s in states:
        if s not in clusterMap:
            cluster = _findCluster(s, deps, revDeps, states)
            for cs in cluster:
                clusterMap[cs] = clusterIdx
            clusters.append({
                "id": clusterIdx,
                "states": list(cluster),
                "size": len(cluster)
            })
            clusterIdx += 1
    dependencies = {s: list(deps.get(s, [])) for s in states}
    return {
        "clusters": clusters,
        "dependencies": dependencies,
        "sorted_states": sortedStates
    }


def _findCluster(start: str, deps: dict, revDeps: dict,
                 allStates: list) -> Set[str]:
    """Find strongly connected component."""
    cluster = {start}
    queue = [start]
    while queue:
        s = queue.pop(0)
        for neighbor in list(deps.get(s, [])) + list(revDeps.get(s, [])):
            if neighbor not in cluster:
                cluster.add(neighbor)
                queue.append(neighbor)
    return cluster


def startReview(params: Dict[str, Any]) -> Dict[str, Any]:
    """Start review session."""
    blueprint = params.get("blueprint", {})
    existingNotes = params.get("review_notes") or []
    states = blueprint.get("states", {})
    transitions = blueprint.get("transitions", [])
    gates = blueprint.get("gates", {})
    actions = blueprint.get("actions", {})
    coverage = {
        "states": len(states),
        "transitions": len(transitions),
        "gates": len(gates),
        "actions": len(actions),
        "states_with_desc": sum(1 for s in states.values()
                                if s.get("description")),
        "gates_used": len(set(g for t in transitions
                              for g in t.get("gates", []))),
        "actions_used": len(set(a for t in transitions
                                for a in t.get("actions", [])))
    }
    return {
        "review_notes": existingNotes,
        "review_status": "pending",
        "coverage": coverage
    }


def addNote(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add review note."""
    notes = list(params.get("review_notes") or [])
    note = params.get("note", "")
    nodeId = params.get("node_id")
    notes.append({
        "timestamp": datetime.now().isoformat(),
        "node_id": nodeId,
        "note": note
    })
    return {"review_notes": notes}


def addAudit(params: Dict[str, Any]) -> Dict[str, Any]:
    """Add audit log entry."""
    auditLog = list(params.get("audit_log") or [])
    action = params.get("action", "")
    nodeId = params.get("node_id")
    nodeType = params.get("node_type")
    auditLog.append({
        "timestamp": datetime.now().isoformat(),
        "action": action,
        "node_id": nodeId,
        "node_type": nodeType
    })
    return {"audit_log": auditLog}


def llmQuery(params: Dict[str, Any]) -> Dict[str, Any]:
    """Query LLM for assistance."""
    apiKey = params.get("api_key", "")
    apiBase = params.get("api_base", "https://api.anthropic.com")
    model = params.get("model", "claude-sonnet-4-20250514")
    blueprint = params.get("blueprint", {})
    prompt = params.get("prompt", "")
    mode = params.get("mode", "edit")
    selectedNode = params.get("selected_node")
    if not apiKey:
        return {"llm_response": None, "suggestions": [],
                "error": "No API key"}
    try:
        import anthropic
        client = anthropic.Anthropic(api_key=apiKey, base_url=apiBase)
        systemPrompt = """You are an L++ blueprint assistant. L++ is a
deterministic state machine framework with:
- states: resting points
- transitions: movements between states triggered by events
- gates: boolean guards on transitions
- actions: side effects (set, compute, emit)

Help users design, review, and improve their blueprints.
Return suggestions as JSON array when asked to modify."""
        userPrompt = f"Mode: {mode}\n"
        if selectedNode:
            userPrompt += f"Selected node: {selectedNode}\n"
        userPrompt += f"Blueprint:\n```json\n{json.dumps(blueprint, indent=2)[:3000]}\n```\n\n"
        userPrompt += f"User request: {prompt}"
        response = client.messages.create(
            model=model,
            max_tokens=2000,
            system=systemPrompt,
            messages=[{"role": "user", "content": userPrompt}]
        )
        llmResponse = response.content[0].text
        suggestions = []
        jsonMatch = re.search(r'\[[\s\S]*?\]', llmResponse)
        if jsonMatch:
            try:
                suggestions = json.loads(jsonMatch.group())
            except:
                pass
        return {"llm_response": llmResponse, "suggestions": suggestions,
                "error": None}
    except Exception as e:
        return {"llm_response": None, "suggestions": [],
                "error": str(e)}


def applyLlm(params: Dict[str, Any]) -> Dict[str, Any]:
    """Apply LLM suggestions to blueprint."""
    blueprint = dict(params.get("blueprint", {}))
    suggestions = params.get("suggestions", [])
    for sug in suggestions:
        if not isinstance(sug, dict):
            continue
        action = sug.get("action")
        if action == "add_state":
            states = dict(blueprint.get("states", {}))
            states[sug.get("id")] = {"description": sug.get("description", "")}
            blueprint["states"] = states
        elif action == "add_transition":
            transitions = list(blueprint.get("transitions", []))
            transitions.append({
                "id": sug.get("id"),
                "from": sug.get("from"),
                "to": sug.get("to"),
                "on_event": sug.get("on_event"),
                "gates": sug.get("gates", []),
                "actions": sug.get("actions", [])
            })
            blueprint["transitions"] = transitions
        elif action == "add_gate":
            gates = dict(blueprint.get("gates", {}))
            gates[sug.get("id")] = {
                "type": sug.get("type", "expression"),
                "expression": sug.get("expression", "True")
            }
            blueprint["gates"] = gates
        elif action == "add_action":
            actions = dict(blueprint.get("actions", {}))
            actions[sug.get("id")] = {
                "type": sug.get("type", "set"),
                "target": sug.get("target", ""),
                "value": sug.get("value")
            }
            blueprint["actions"] = actions
    return {
        "blueprint": blueprint,
        "blueprint_json": json.dumps(blueprint, indent=2),
        "is_dirty": True
    }


def generateOutputs(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate graph HTML and Mermaid diagram."""
    blueprint = params.get("blueprint") or {}
    states = blueprint.get("states", {})
    transitions = blueprint.get("transitions", [])
    entryState = blueprint.get("entry_state", "idle")
    terminalStates = blueprint.get("terminal_states", [])
    mermaidLines = ["stateDiagram-v2"]
    mermaidLines.append(f"    [*] --> {entryState}")
    for sId in states:
        desc = states[sId].get("description", "")
        if desc:
            mermaidLines.append(f"    {sId}: {sId}\\n{desc[:30]}")
    for t in transitions:
        fromS = t.get("from", "")
        toS = t.get("to", "")
        event = t.get("on_event", "")
        if fromS == "*":
            fromS = "any"
        mermaidLines.append(f"    {fromS} --> {toS}: {event}")
    for ts in terminalStates:
        mermaidLines.append(f"    {ts} --> [*]")
    mermaid = "\n".join(mermaidLines)
    graphHtml = _generateGraphHtml(blueprint)
    return {"graph_html": graphHtml, "mermaid": mermaid}


def _generateGraphHtml(blueprint: dict) -> str:
    """Generate interactive graph HTML with D3.js force layout."""
    states = blueprint.get("states", {})
    transitions = blueprint.get("transitions", [])
    entryState = blueprint.get("entry_state", "idle")
    terminalStates = blueprint.get("terminal_states", [])
    gates = blueprint.get("gates", {})
    actions = blueprint.get("actions", {})

    nodes = []
    for sId, sData in states.items():
        sIdLower = sId.lower()
        if sId == entryState:
            nodeType = "entry"
        elif sId in terminalStates:
            # Differentiate terminal states by name
            if "error" in sIdLower or "fail" in sIdLower:
                nodeType = "error"
            elif "complete" in sIdLower or "done" in sIdLower or "success" in sIdLower or "secure" in sIdLower:
                nodeType = "complete"
            else:
                nodeType = "terminal"
        else:
            nodeType = "normal"
        nodes.append({
            "id": sId,
            "label": sId,
            "description": sData.get("description", ""),
            "type": nodeType
        })

    # Build node type map for edge coloring
    nodeTypeMap = {n["id"]: n["type"] for n in nodes}

    edges = []
    stateIds = set(states.keys())
    for t in transitions:
        fromState = t.get("from", "")
        toState = t.get("to", "")
        # Skip wildcard transitions or transitions to non-existent states
        if fromState == "*" or fromState not in stateIds:
            continue
        if toState not in stateIds:
            continue
        gateInfo = [f"{gId}: {gates.get(gId, {}).get('expression', '')}"
                    for gId in t.get("gates", [])]
        actionInfo = [f"{aId}: {actions.get(aId, {}).get('type', '')}"
                      for aId in t.get("actions", [])]
        edges.append({
            "id": t.get("id", ""),
            "source": fromState,
            "target": toState,
            "event": t.get("on_event", ""),
            "gates": gateInfo,
            "actions": actionInfo,
            "targetType": nodeTypeMap.get(toState, "normal")
        })

    html = f"""<!DOCTYPE html>
<html><head>
<title>L++ Canvas - {blueprint.get('name', 'Blueprint')}</title>
<script src="https://d3js.org/d3.v7.min.js"></script>
<style>
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{ font-family: system-ui, sans-serif; background: #1a1a2e; overflow: hidden; }}
#container {{ width: 100vw; height: 100vh; }}
.node {{ cursor: grab; }}
.node:active {{ cursor: grabbing; }}
.node rect {{ stroke: #fff; stroke-width: 0; transition: all 0.2s; }}
.node.selected rect {{ stroke: #ffd700; stroke-width: 3; }}
.node:hover rect {{ filter: brightness(1.2); }}
.node text {{ fill: #fff; font-size: 12px; pointer-events: none; }}
.link {{ fill: none; stroke-width: 2; opacity: 0.8; }}
.link:hover {{ stroke-width: 3; opacity: 1; filter: brightness(1.2); }}
.link.selected {{ stroke: #ffd700 !important; stroke-width: 3; opacity: 1; }}
.link-label {{ fill: #ccc; font-size: 11px; pointer-events: none; font-weight: 500; }}
#tooltip {{ position: fixed; background: #2d2d44; border: 1px solid #444;
  border-radius: 6px; padding: 10px; color: #eee; font-size: 12px;
  max-width: 300px; display: none; z-index: 1000; box-shadow: 0 4px 12px rgba(0,0,0,0.3); }}
#tooltip h4 {{ margin: 0 0 6px 0; color: #58a6ff; }}
#tooltip .info {{ color: #8b949e; margin: 2px 0; }}
#controls {{ position: fixed; top: 10px; right: 10px; display: flex; gap: 5px; }}
#controls button {{ padding: 8px 12px; background: #2d2d44; border: 1px solid #444;
  color: #eee; border-radius: 4px; cursor: pointer; }}
#controls button:hover {{ background: #3d3d54; }}
#legend {{ position: fixed; bottom: 10px; left: 10px; background: #2d2d44;
  border: 1px solid #444; border-radius: 6px; padding: 10px; font-size: 11px; color: #aaa; }}
.legend-item {{ display: flex; align-items: center; gap: 8px; margin: 4px 0; }}
.legend-dot {{ width: 12px; height: 12px; border-radius: 3px; }}
</style>
</head>
<body>
<div id="container"></div>
<div id="tooltip"></div>
<div id="controls">
  <button id="resetBtn">Reset View</button>
  <button id="layoutBtn">Auto Layout</button>
</div>
<div id="legend">
  <div class="legend-item"><div class="legend-dot" style="background:#4CAF50"></div> Entry/Complete</div>
  <div class="legend-item"><div class="legend-dot" style="background:#f44336"></div> Error</div>
  <div class="legend-item"><div class="legend-dot" style="background:#FFC107"></div> Terminal</div>
  <div class="legend-item"><div class="legend-dot" style="background:#2196F3"></div> Normal</div>
</div>
<script>
const nodesData = {json.dumps(nodes)};
const edgesData = {json.dumps(edges)};
const width = window.innerWidth;
const height = window.innerHeight;

const colorMap = {{ entry: '#4CAF50', terminal: '#FFC107', error: '#f44336', complete: '#4CAF50', normal: '#2196F3' }};
const tooltip = d3.select('#tooltip');

const svg = d3.select('#container')
  .append('svg')
  .attr('width', width)
  .attr('height', height);

const g = svg.append('g');

// Zoom behavior
const zoom = d3.zoom()
  .scaleExtent([0.1, 4])
  .on('zoom', (e) => g.attr('transform', e.transform));
svg.call(zoom);

// Arrow markers for each target type
const defs = svg.append('defs');
Object.entries(colorMap).forEach(([type, color]) => {{
  defs.append('marker')
    .attr('id', `arrow-${{type}}`)
    .attr('viewBox', '-0 -5 10 10')
    .attr('refX', 20)
    .attr('refY', 0)
    .attr('orient', 'auto')
    .attr('markerWidth', 8)
    .attr('markerHeight', 8)
    .append('path')
    .attr('d', 'M 0,-5 L 10,0 L 0,5')
    .attr('fill', color);
}});

// Force simulation
const simulation = d3.forceSimulation(nodesData)
  .force('link', d3.forceLink(edgesData).id(d => d.id).distance(180))
  .force('charge', d3.forceManyBody().strength(-400))
  .force('center', d3.forceCenter(width / 2, height / 2))
  .force('collision', d3.forceCollide().radius(80));

// Links - colored by target state type
const link = g.append('g')
  .selectAll('path')
  .data(edgesData)
  .join('path')
  .attr('class', 'link')
  .attr('stroke', d => colorMap[d.targetType] || '#888')
  .attr('marker-end', d => `url(#arrow-${{d.targetType || 'normal'}})`)
  .on('click', (e, d) => selectEdge(d))
  .on('mouseover', (e, d) => showTooltip(e, 'transition', d))
  .on('mouseout', hideTooltip);

// Link labels
const linkLabel = g.append('g')
  .selectAll('text')
  .data(edgesData)
  .join('text')
  .attr('class', 'link-label')
  .text(d => d.event);

// Nodes
const node = g.append('g')
  .selectAll('g')
  .data(nodesData)
  .join('g')
  .attr('class', 'node')
  .call(d3.drag()
    .on('start', dragStart)
    .on('drag', dragging)
    .on('end', dragEnd))
  .on('click', (e, d) => selectNode(d))
  .on('dblclick', (e, d) => editNode(d))
  .on('mouseover', (e, d) => showTooltip(e, 'state', d))
  .on('mouseout', hideTooltip);

node.append('rect')
  .attr('width', 120)
  .attr('height', 50)
  .attr('x', -60)
  .attr('y', -25)
  .attr('rx', 8)
  .attr('fill', d => colorMap[d.type]);

node.append('text')
  .attr('text-anchor', 'middle')
  .attr('dy', 5)
  .text(d => d.label.length > 14 ? d.label.slice(0, 12) + '..' : d.label);

// Update positions on tick
simulation.on('tick', () => {{
  link.attr('d', d => {{
    const dx = d.target.x - d.source.x;
    const dy = d.target.y - d.source.y;
    const dr = Math.sqrt(dx * dx + dy * dy) * 0.8;
    return `M${{d.source.x}},${{d.source.y}}A${{dr}},${{dr}} 0 0,1 ${{d.target.x}},${{d.target.y}}`;
  }});
  linkLabel
    .attr('x', d => (d.source.x + d.target.x) / 2)
    .attr('y', d => (d.source.y + d.target.y) / 2 - 8);
  node.attr('transform', d => `translate(${{d.x}},${{d.y}})`);
}});

function dragStart(e, d) {{
  if (!e.active) simulation.alphaTarget(0.3).restart();
  d.fx = d.x; d.fy = d.y;
}}
function dragging(e, d) {{ d.fx = e.x; d.fy = e.y; }}
function dragEnd(e, d) {{
  if (!e.active) simulation.alphaTarget(0);
  d.fx = null; d.fy = null;
}}

let selectedNode = null, selectedEdge = null;

function selectNode(d) {{
  // Toggle selection if already selected
  if (selectedNode && selectedNode.id === d.id) {{
    node.classed('selected', false);
    selectedNode = null;
    window.parent.postMessage({{ type: 'deselect', nodeType: 'state', nodeId: d.id }}, '*');
  }} else {{
    node.classed('selected', n => n.id === d.id);
    link.classed('selected', false);
    selectedNode = d; selectedEdge = null;
    window.parent.postMessage({{ type: 'select', nodeType: 'state', nodeId: d.id, data: d }}, '*');
  }}
}}

function selectEdge(d) {{
  // Toggle selection if already selected
  if (selectedEdge && selectedEdge.id === d.id) {{
    link.classed('selected', false);
    selectedEdge = null;
    window.parent.postMessage({{ type: 'deselect', nodeType: 'transition', nodeId: d.id }}, '*');
  }} else {{
    link.classed('selected', e => e.id === d.id);
    node.classed('selected', false);
    selectedEdge = d; selectedNode = null;
    window.parent.postMessage({{ type: 'select', nodeType: 'transition', nodeId: d.id, data: d }}, '*');
  }}
}}

function editNode(d) {{
  window.parent.postMessage({{ type: 'edit', nodeType: 'state', nodeId: d.id, data: d }}, '*');
}}

function showTooltip(e, type, d) {{
  let html = '';
  if (type === 'state') {{
    html = `<h4>${{d.label}}</h4><div class="info">${{d.description || 'No description'}}</div>
            <div class="info">Type: ${{d.type}}</div>`;
  }} else {{
    html = `<h4>${{d.event}}</h4><div class="info">ID: ${{d.id}}</div>
            <div class="info">${{d.source.id}} → ${{d.target.id}}</div>`;
    if (d.gates.length) html += `<div class="info">Gates: ${{d.gates.join(', ')}}</div>`;
    if (d.actions.length) html += `<div class="info">Actions: ${{d.actions.join(', ')}}</div>`;
  }}
  tooltip.html(html).style('display', 'block')
    .style('left', (e.pageX + 15) + 'px').style('top', (e.pageY + 15) + 'px');
}}
function hideTooltip() {{ tooltip.style('display', 'none'); }}

document.getElementById('resetBtn').onclick = () => {{
  svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity);
}};
document.getElementById('layoutBtn').onclick = () => {{
  // Clear all fixed positions and restart force simulation
  nodesData.forEach(n => {{ n.fx = null; n.fy = null; }});
  currentLayout = 'force';
  simulation.alpha(1).restart();
}};

// Hierarchical layout positions
function computeHierarchy() {{
  const entryNode = nodesData.find(n => n.type === 'entry');
  const terminalNodes = nodesData.filter(n => ['terminal', 'error', 'complete'].includes(n.type));
  const normalNodes = nodesData.filter(n => n.type === 'normal');

  // Position by layers: entry at top, normal in middle rows, terminal at bottom
  const layerHeight = height / 4;
  if (entryNode) {{
    entryNode.fx = width / 2;
    entryNode.fy = layerHeight * 0.5;
  }}

  // Arrange normal states in rows
  const cols = Math.ceil(Math.sqrt(normalNodes.length));
  normalNodes.forEach((n, i) => {{
    const row = Math.floor(i / cols);
    const col = i % cols;
    const rowWidth = Math.min(cols, normalNodes.length - row * cols);
    n.fx = (width / (rowWidth + 1)) * (col + 1);
    n.fy = layerHeight * (1.2 + row * 0.6);
  }});

  // Terminal states at bottom
  terminalNodes.forEach((n, i) => {{
    n.fx = (width / (terminalNodes.length + 1)) * (i + 1);
    n.fy = height - layerHeight * 0.5;
  }});

  simulation.alpha(0.3).restart();
}}

function releaseHierarchy() {{
  nodesData.forEach(n => {{ n.fx = null; n.fy = null; }});
  simulation.alpha(1).restart();
}}

// Circular layout - arrange nodes in a circle with entry at top
function computeCircular() {{
  const entryNode = nodesData.find(n => n.type === 'entry');
  const terminalNodes = nodesData.filter(n => ['terminal', 'error', 'complete'].includes(n.type));
  const normalNodes = nodesData.filter(n => n.type === 'normal');

  const cx = width / 2;
  const cy = height / 2;
  const radius = Math.min(width, height) * 0.35;

  // Entry at top (angle 0 = -90 degrees)
  if (entryNode) {{
    entryNode.fx = cx;
    entryNode.fy = cy - radius;
  }}

  // Arrange remaining nodes around the circle
  const otherNodes = [...normalNodes, ...terminalNodes];
  const angleStep = (2 * Math.PI) / (otherNodes.length + 1);
  let startAngle = -Math.PI / 2 + angleStep; // Start after entry node

  otherNodes.forEach((n, i) => {{
    const angle = startAngle + i * angleStep;
    n.fx = cx + radius * Math.cos(angle);
    n.fy = cy + radius * Math.sin(angle);
  }});

  simulation.alpha(0.3).restart();
}}

let currentLayout = 'force';

// Listen for messages from parent
window.addEventListener('message', (e) => {{
  if (e.data.type === 'highlight') {{
    node.classed('selected', n => n.id === e.data.nodeId);
    link.classed('selected', false);
  }} else if (e.data.type === 'highlightTransition') {{
    link.classed('selected', l => l.id === e.data.transitionId);
    node.classed('selected', false);
  }} else if (e.data.type === 'highlightMultiple') {{
    const ids = new Set(e.data.nodeIds || []);
    node.classed('selected', n => ids.has(n.id));
    link.classed('selected', false);
  }} else if (e.data.type === 'highlightMultipleTransitions') {{
    const ids = new Set(e.data.transitionIds || []);
    link.classed('selected', l => ids.has(l.id));
    node.classed('selected', false);
  }} else if (e.data.type === 'clearSelection') {{
    node.classed('selected', false);
    link.classed('selected', false);
    selectedNode = null;
    selectedEdge = null;
  }} else if (e.data.type === 'setLayout') {{
    currentLayout = e.data.layout;
    if (currentLayout === 'hierarchy') {{
      computeHierarchy();
    }} else if (currentLayout === 'circular') {{
      computeCircular();
    }} else {{
      releaseHierarchy();
    }}
  }} else if (e.data.type === 'setSpread') {{
    const spread = e.data.spread || 400;
    // Update charge strength (more negative = more repulsion)
    simulation.force('charge', d3.forceManyBody().strength(-spread));
    // Update link distance
    simulation.force('link', d3.forceLink(edgesData).id(d => d.id).distance(spread * 0.45));
    // Restart simulation with new parameters
    simulation.alpha(0.5).restart();
  }} else if (e.data.type === 'zoom') {{
    const currentTransform = d3.zoomTransform(svg.node());
    const factor = e.data.direction === 'in' ? 1.3 : 0.7;
    svg.transition().duration(200).call(zoom.scaleTo, currentTransform.k * factor);
  }}
}});

// Initial zoom to fit
setTimeout(() => {{
  const bounds = g.node().getBBox();
  const scale = Math.min(width / (bounds.width + 100), height / (bounds.height + 100), 1);
  const tx = (width - bounds.width * scale) / 2 - bounds.x * scale;
  const ty = (height - bounds.height * scale) / 2 - bounds.y * scale;
  svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
}}, 500);
</script>
</body></html>"""
    return html


def saveBlueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Save blueprint to file."""
    blueprint = params.get("blueprint", {})
    path = params.get("path", "")
    if not path:
        return {"error": "No path specified"}
    try:
        Path(path).write_text(json.dumps(blueprint, indent=2))
        return {"error": None}
    except Exception as e:
        return {"error": str(e)}


def clearAll(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear all state."""
    return {
        "blueprint": None,
        "blueprint_json": None,
        "is_dirty": False,
        "error": None
    }


COMPUTE_REGISTRY = {
    "canvas:init_new": initNew,
    "canvas:load_blueprint": loadBlueprint,
    "canvas:create_blueprint": createBlueprint,
    "canvas:select_node": selectNode,
    "canvas:apply_edit": applyEdit,
    "canvas:delete_node": deleteNode,
    "canvas:add_state": addState,
    "canvas:add_transition": addTransition,
    "canvas:add_gate": addGate,
    "canvas:add_action": addAction,
    "canvas:run_tlc": runTlc,
    "canvas:analyze_paths": analyzePaths,
    "canvas:init_simulation": initSimulation,
    "canvas:sim_step": simStep,
    "canvas:sim_dispatch": simDispatch,
    "canvas:compute_clusters": computeClusters,
    "canvas:start_review": startReview,
    "canvas:add_note": addNote,
    "canvas:add_audit": addAudit,
    "canvas:llm_query": llmQuery,
    "canvas:apply_llm": applyLlm,
    "canvas:generate_outputs": generateOutputs,
    "canvas:save_blueprint": saveBlueprint,
    "canvas:clear_all": clearAll,
}
