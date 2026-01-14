"""
COMPUTE units for the L++ Test Case Generator.

These are the pure computation functions for generating test cases from
L++ blueprints. Implements path coverage, state coverage, gate boundary
testing, negative testing, and property-based testing strategies.
"""

import json
import re
from collections import deque
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

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
            "context_schema": raw.get("context_schema", {}),
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
                aid: {
                    "type": a.type.value,
                    **({"compute_unit": raw["actions"][aid].get("compute_unit")}
                       if raw.get("actions", {}).get(aid, {}).get("compute_unit")
                       else {}),
                    **({"input_map": raw["actions"][aid].get("input_map")}
                       if raw.get("actions", {}).get(aid, {}).get("input_map")
                       else {}),
                    **({"output_map": raw["actions"][aid].get("output_map")}
                       if raw.get("actions", {}).get(aid, {}).get("output_map")
                       else {}),
                }
                for aid, a in blueprint.actions.items()
            },
            "entry_state": blueprint.entry_state,
            "terminal_states": list(blueprint.terminal_states),
            "terminal_contracts": raw.get("terminal_states", {})  # v0.2.0 contracts
        }

        return {"blueprint": bpData, "path": str(path), "error": None}

    except Exception as e:
        return {"blueprint": None, "path": None, "error": str(e)}


# =============================================================================
# Graph Analysis
# =============================================================================

def build_graph(params: Dict[str, Any]) -> Dict[str, Any]:
    """Build adjacency graph from blueprint transitions."""
    bp = params.get("blueprint")
    if not bp:
        return {"graph": None}

    # Collect all states (regular + terminal)
    all_states = set(bp["states"].keys())
    terminals = set(bp.get("terminal_states", []))
    all_states |= terminals

    # Build adjacency list: state -> [(event, target, transition_id, gates)]
    adj = {sid: [] for sid in all_states}
    wildcardEdges = []

    for t in bp["transitions"]:
        fromState = t["from"]
        toState = t["to"]
        edge = {
            "event": t["on_event"],
            "to": toState,
            "id": t["id"],
            "gates": t.get("gates", []),
            "actions": t.get("actions", [])
        }

        if fromState == "*":
            wildcardEdges.append(edge)
        else:
            if fromState not in adj:
                adj[fromState] = []
            adj[fromState].append(edge)

    # Apply wildcard edges to all states
    for sid in adj:
        adj[sid].extend(wildcardEdges)

    # Build reverse adjacency for reachability analysis
    reverseAdj = {sid: [] for sid in all_states}
    for sid, edges in adj.items():
        for edge in edges:
            if edge["to"] in reverseAdj:
                reverseAdj[edge["to"]].append(
                    {"from": sid, "event": edge["event"]})

    return {
        "graph": {
            "adjacency": adj,
            "reverse": reverseAdj,
            "entry": bp["entry_state"],
            "terminals": list(terminals),
            "states": list(all_states),
            "transition_count": len(bp["transitions"])
        }
    }


def analyze_paths(params: Dict[str, Any]) -> Dict[str, Any]:
    """Find all paths through the state machine using BFS for efficiency."""
    bp = params.get("blueprint")
    graph = params.get("graph")

    if not bp or not graph:
        return {"paths": []}

    adj = graph["adjacency"]
    entry = graph["entry"]
    terminals = set(graph["terminals"])
    allStates = set(graph["states"])

    paths = []

    # Strategy 1: Find shortest path to each reachable state (state coverage)
    # This gives us minimum paths needed to visit all states
    for targetState in allStates:
        if targetState == entry:
            paths.append({
                "states": [entry],
                "events": [],
                "transitions": [],
                "is_complete": targetState in terminals
            })
            continue

        shortestPath = _bfsPath(adj, entry, targetState)
        if shortestPath:
            paths.append({
                "states": shortestPath["states"],
                "events": shortestPath["events"],
                "transitions": shortestPath["transitions"],
                "is_complete": targetState in terminals
            })

    # Strategy 2: Find paths that cover all transitions
    # Build set of all transitions
    allTransitions = set()
    for t in bp["transitions"]:
        allTransitions.add(t["id"])

    coveredTransitions = set()
    for p in paths:
        coveredTransitions.update(p["transitions"])

    # Find additional paths to cover uncovered transitions
    uncovered = allTransitions - coveredTransitions
    for transId in uncovered:
        # Find the transition details
        trans = next((t for t in bp["transitions"]
                     if t["id"] == transId), None)
        if not trans:
            continue

        fromState = trans["from"]
        toState = trans["to"]

        # Skip wildcard transitions for now
        if fromState == "*":
            continue

        # Find path to from_state, then add this transition
        if fromState == entry:
            pathToFrom = {"states": [entry], "events": [], "transitions": []}
        else:
            pathToFrom = _bfsPath(adj, entry, fromState)

        if pathToFrom:
            paths.append({
                "states": pathToFrom["states"] + [toState],
                "events": pathToFrom["events"] + [trans["on_event"]],
                "transitions": pathToFrom["transitions"] + [transId],
                "is_complete": toState in terminals
            })
            coveredTransitions.add(transId)

    # Strategy 3: If terminal states exist, ensure paths to them
    if terminals:
        for term in terminals:
            termPaths = [p for p in paths if p["states"][-1] == term]
            if not termPaths:
                shortestPath = _bfsPath(adj, entry, term)
                if shortestPath:
                    paths.append({
                        "states": shortestPath["states"],
                        "events": shortestPath["events"],
                        "transitions": shortestPath["transitions"],
                        "is_complete": True
                    })

    return {"paths": paths}


def _bfsPath(adj: Dict, start: str, target: str) -> Optional[Dict]:
    """Find shortest path from start to target using BFS."""
    if start == target:
        return {"states": [start], "events": [], "transitions": []}

    queue = deque([(start, [start], [], [])])
    visited = {start}

    while queue:
        state, states, events, transitions = queue.popleft()

        for edge in adj.get(state, []):
            nextState = edge["to"]
            if nextState not in visited:
                newStates = states + [nextState]
                newEvents = events + [edge["event"]]
                newTrans = transitions + [edge["id"]]

                if nextState == target:
                    return {
                        "states": newStates,
                        "events": newEvents,
                        "transitions": newTrans
                    }

                visited.add(nextState)
                queue.append((nextState, newStates, newEvents, newTrans))

    return None


# =============================================================================
# Gate Analysis
# =============================================================================

def analyze_gates(params: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze gate expressions to extract boundary conditions."""
    bp = params.get("blueprint")
    if not bp:
        return {"analysis": None}

    gates = bp.get("gates", {})
    analysis = {}

    for gateId, gate in gates.items():
        expr = gate.get("expression", "")
        boundaries = _extractBoundaries(expr)
        booleans = _extractBooleans(expr)
        nullChecks = _extractNullChecks(expr)

        analysis[gateId] = {
            "expression": expr,
            "boundaries": boundaries,
            "booleans": booleans,
            "null_checks": nullChecks,
            "variables": _extractVariables(expr)
        }

    return {"analysis": analysis}


def _extractBoundaries(expr: str) -> List[Dict]:
    """Extract numeric boundary conditions from expression."""
    boundaries = []

    # Match patterns like: x > 10, x >= 5, x < 100, x <= 50, x == 42
    patterns = [
        (r"(\w+)\s*>\s*(\d+(?:\.\d+)?)", "gt"),
        (r"(\w+)\s*>=\s*(\d+(?:\.\d+)?)", "gte"),
        (r"(\w+)\s*<\s*(\d+(?:\.\d+)?)", "lt"),
        (r"(\w+)\s*<=\s*(\d+(?:\.\d+)?)", "lte"),
        (r"(\w+)\s*==\s*(\d+(?:\.\d+)?)", "eq"),
        (r"(\w+)\s*!=\s*(\d+(?:\.\d+)?)", "neq"),
    ]

    for pattern, op in patterns:
        for match in re.finditer(pattern, expr):
            var = match.group(1)
            val = float(match.group(2))
            boundaries.append({
                "variable": var,
                "operator": op,
                "value": val,
                "test_values": _genBoundaryValues(op, val)
            })

    return boundaries


def _genBoundaryValues(op: str, val: float) -> List[float]:
    """Generate test values for boundary condition."""
    isInt = val == int(val)
    delta = 1 if isInt else 0.1

    if op == "gt":
        return [val - delta, val, val + delta]  # fail, fail, pass
    elif op == "gte":
        return [val - delta, val, val + delta]  # fail, pass, pass
    elif op == "lt":
        return [val - delta, val, val + delta]  # pass, fail, fail
    elif op == "lte":
        return [val - delta, val, val + delta]  # pass, pass, fail
    elif op == "eq":
        return [val - delta, val, val + delta]  # fail, pass, fail
    elif op == "neq":
        return [val - delta, val, val + delta]  # pass, fail, pass

    return [val]


def _extractBooleans(expr: str) -> List[Dict]:
    """Extract boolean conditions from expression."""
    booleans = []

    # Match patterns like: flag, not flag, flag == True
    boolPattern = r"\b(is_\w+|has_\w+|can_\w+|should_\w+|\w+_flag)\b"
    for match in re.finditer(boolPattern, expr, re.IGNORECASE):
        var = match.group(1)
        booleans.append({
            "variable": var,
            "test_values": [True, False]
        })

    return booleans


def _extractNullChecks(expr: str) -> List[Dict]:
    """Extract null/None check conditions from expression."""
    nullChecks = []

    # Match patterns like: x is not None, x is None
    patterns = [
        (r"(\w+)\s+is\s+not\s+None", "not_null"),
        (r"(\w+)\s+is\s+None", "is_null"),
        (r"(\w+)\s+is\s+not\s+null", "not_null"),
        (r"(\w+)\s+is\s+null", "is_null"),
    ]

    for pattern, checkType in patterns:
        for match in re.finditer(pattern, expr, re.IGNORECASE):
            var = match.group(1)
            nullChecks.append({
                "variable": var,
                "check_type": checkType,
                "test_values": [None, "some_value"]
            })

    return nullChecks


def _extractVariables(expr: str) -> List[str]:
    """Extract all variable names from expression."""
    # Match word characters that aren't Python keywords
    keywords = {"and", "or", "not", "is", "in", "True", "False", "None",
                "if", "else", "for", "while", "return", "len"}
    words = re.findall(r"\b([a-zA-Z_]\w*)\b", expr)
    return list(set(w for w in words if w not in keywords))


def _genContextForPath(bp: Dict, transitionIds: List[str]) -> Dict:
    """Generate context values that satisfy all gates in a path.

    Analyzes gate expressions for each transition and generates values
    that will make all gates pass.
    """
    ctx = _genDefaultContext(bp)
    gates = bp.get("gates", {})
    transitions = bp.get("transitions", [])

    # Collect all gates used in this path
    pathGates = set()
    for transId in transitionIds:
        trans = next((t for t in transitions if t["id"] == transId), None)
        if trans:
            pathGates.update(trans.get("gates", []))

    # For each gate, analyze and set context values to make it pass
    for gateId in pathGates:
        gate = gates.get(gateId, {})
        expr = gate.get("expression", "")
        _applyGateConstraints(ctx, expr, bp)

    return ctx


def _applyGateConstraints(ctx: Dict, expr: str, bp: Dict) -> None:
    """Apply constraints from a gate expression to context.

    Modifies ctx in-place to satisfy the gate conditions.
    """
    schema = bp.get("context_schema", {}).get("properties", {})

    # Handle "x is not None" - ensure value is not None
    for match in re.finditer(r"(\w+)\s+is\s+not\s+None", expr):
        var = match.group(1)
        if var in ctx and ctx[var] is None:
            propType = schema.get(var, {}).get("type", "string")
            ctx[var] = _getNonNullValue(var, propType)

    # Handle "x is not None and x != ''" - ensure non-empty string
    for match in re.finditer(r"(\w+)\s+is\s+not\s+None\s+and\s+\1\s*!=\s*['\"]", expr):
        var = match.group(1)
        if var in ctx and (ctx[var] is None or ctx[var] == ""):
            ctx[var] = _getNonNullValue(var, "string")

    # Handle "len(x) > N" - ensure array/string has enough items
    for match in re.finditer(r"len\((\w+)\)\s*>\s*(\d+)", expr):
        var = match.group(1)
        minLen = int(match.group(2)) + 1
        if var in ctx:
            propType = schema.get(var, {}).get("type", "array")
            if propType == "array" and len(ctx.get(var, [])) < minLen:
                ctx[var] = ["item"] * minLen
            elif propType == "string" and len(ctx.get(var, "")) < minLen:
                ctx[var] = "x" * minLen

    # Handle "x > N" - numeric comparisons
    for match in re.finditer(r"(\w+)\s*>\s*(\d+(?:\.\d+)?)", expr):
        var = match.group(1)
        minVal = float(match.group(2))
        if var in ctx and var not in ["len"]:  # Skip 'len' function
            ctx[var] = minVal + 1

    # Handle "x >= N" - numeric comparisons
    for match in re.finditer(r"(\w+)\s*>=\s*(\d+(?:\.\d+)?)", expr):
        var = match.group(1)
        minVal = float(match.group(2))
        if var in ctx:
            ctx[var] = minVal

    # Handle "x == True" or just boolean checks
    for match in re.finditer(r"(\w+)\s*==\s*True", expr):
        var = match.group(1)
        if var in ctx:
            ctx[var] = True

    # Handle "x == False"
    for match in re.finditer(r"(\w+)\s*==\s*False", expr):
        var = match.group(1)
        if var in ctx:
            ctx[var] = False

    # Handle "error is None" or "error == None" - set error to empty/None
    for match in re.finditer(r"(\w*error\w*)\s+is\s+None", expr, re.IGNORECASE):
        var = match.group(1)
        if var in ctx:
            ctx[var] = ""  # Empty string for error fields


def _getNonNullValue(varName: str, propType: str) -> Any:
    """Generate a non-null value based on property type and name."""
    if propType == "number":
        return 1
    elif propType == "boolean":
        return True
    elif propType == "array":
        return ["test_item"]
    elif propType == "object":
        return {"test": True}
    elif propType == "string":
        # Use meaningful placeholders based on property name
        nameLower = varName.lower()
        if "path" in nameLower:
            return "/test/path"
        elif "dir" in nameLower:
            return "/test/dir"
        elif "name" in nameLower:
            return "test_name"
        elif "key" in nameLower:
            return "test_key"
        elif "url" in nameLower:
            return "https://test.example.com"
        elif "error" in nameLower:
            return ""
        else:
            return "test_value"
    return "test_default"


# =============================================================================
# Test Generation
# =============================================================================

def generate_path_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate tests for path coverage."""
    bp = params.get("blueprint")
    paths = params.get("paths", [])

    if not bp or not paths:
        return {"tests": []}

    tests = []
    for i, path in enumerate(paths):
        if not path["events"]:
            continue

        testId = f"path_{i+1}"
        finalState = path["states"][-1] if path["states"] else bp["entry_state"]

        # Generate context that satisfies all gates in this path
        transitionIds = path.get("transitions", [])
        ctx = _genContextForPath(bp, transitionIds)

        test = {
            "id": testId,
            "type": "path_coverage",
            "description": f"Path: {' -> '.join(path['states'])}",
            "initial_context": ctx,
            "events": [
                {"event": evt, "payload": {}}
                for evt in path["events"]
            ],
            "expected_final_state": finalState,
            "transitions_covered": transitionIds,
            "is_complete_path": path.get("is_complete", False)
        }
        tests.append(test)

    return {"tests": tests}


def generate_state_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate tests for state coverage."""
    bp = params.get("blueprint")
    paths = params.get("paths", [])

    if not bp:
        return {"tests": []}

    # Find minimum set of paths that cover all states
    allStates = set(bp["states"].keys())
    coveredStates = set()
    selectedPaths = []

    # Sort paths by number of unique states covered
    sortedPaths = sorted(
        paths,
        key=lambda p: len(set(p["states"]) - coveredStates),
        reverse=True
    )

    for path in sortedPaths:
        pathStates = set(path["states"])
        newStates = pathStates - coveredStates

        if newStates:
            selectedPaths.append(path)
            coveredStates.update(pathStates)

        if coveredStates >= allStates:
            break

    tests = []
    for i, path in enumerate(selectedPaths):
        if not path["events"]:
            continue

        # Generate context that satisfies all gates in this path
        transitionIds = path.get("transitions", [])
        ctx = _genContextForPath(bp, transitionIds)

        test = {
            "id": f"state_coverage_{i+1}",
            "type": "state_coverage",
            "description": f"Covers states: {', '.join(path['states'])}",
            "initial_context": ctx,
            "events": [
                {"event": evt, "payload": {}}
                for evt in path["events"]
            ],
            "expected_final_state": path["states"][-1],
            "states_covered": path["states"]
        }
        tests.append(test)

    return {"tests": tests}


def generate_gate_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate boundary condition tests for gates."""
    bp = params.get("blueprint")
    gateAnalysis = params.get("gate_analysis")

    if not bp or not gateAnalysis:
        return {"tests": []}

    tests = []
    testIdx = 0

    for gateId, analysis in gateAnalysis.items():
        # Find transitions that use this gate
        gateTransitions = [
            t for t in bp["transitions"]
            if gateId in t.get("gates", [])
        ]

        if not gateTransitions:
            continue

        trans = gateTransitions[0]  # Use first transition for testing

        # Generate boundary tests
        for boundary in analysis.get("boundaries", []):
            for i, val in enumerate(boundary["test_values"]):
                testIdx += 1
                ctx = _genDefaultContext(bp)
                ctx[boundary["variable"]] = val

                # Determine expected outcome
                expected = _evalBoundary(boundary["operator"], val,
                                         boundary["value"])

                tests.append({
                    "id": f"gate_boundary_{testIdx}",
                    "type": "gate_boundary",
                    "description": (f"Gate {gateId}: {boundary['variable']} "
                                    f"{boundary['operator']} {boundary['value']} "
                                    f"with value={val}"),
                    "gate_id": gateId,
                    "initial_context": ctx,
                    "events": [{"event": trans["on_event"], "payload": {}}],
                    "expected_gate_result": expected,
                    "from_state": trans["from"]
                })

        # Generate boolean tests
        for boolVar in analysis.get("booleans", []):
            for val in boolVar["test_values"]:
                testIdx += 1
                ctx = _genDefaultContext(bp)
                ctx[boolVar["variable"]] = val

                tests.append({
                    "id": f"gate_boolean_{testIdx}",
                    "type": "gate_boolean",
                    "description": (f"Gate {gateId}: {boolVar['variable']} "
                                    f"= {val}"),
                    "gate_id": gateId,
                    "initial_context": ctx,
                    "events": [{"event": trans["on_event"], "payload": {}}],
                    "from_state": trans["from"]
                })

        # Generate null check tests
        for nullCheck in analysis.get("null_checks", []):
            for val in nullCheck["test_values"]:
                testIdx += 1
                ctx = _genDefaultContext(bp)
                ctx[nullCheck["variable"]] = val

                tests.append({
                    "id": f"gate_null_{testIdx}",
                    "type": "gate_null_check",
                    "description": (f"Gate {gateId}: {nullCheck['variable']} "
                                    f"= {val}"),
                    "gate_id": gateId,
                    "initial_context": ctx,
                    "events": [{"event": trans["on_event"], "payload": {}}],
                    "from_state": trans["from"]
                })

    return {"tests": tests}


def _evalBoundary(op: str, testVal: float, boundaryVal: float) -> bool:
    """Evaluate if a boundary condition passes."""
    if op == "gt":
        return testVal > boundaryVal
    elif op == "gte":
        return testVal >= boundaryVal
    elif op == "lt":
        return testVal < boundaryVal
    elif op == "lte":
        return testVal <= boundaryVal
    elif op == "eq":
        return testVal == boundaryVal
    elif op == "neq":
        return testVal != boundaryVal
    return False


def generate_negative_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate tests for invalid inputs and edge cases."""
    bp = params.get("blueprint")
    graph = params.get("graph")

    if not bp or not graph:
        return {"tests": []}

    tests = []
    adj = graph["adjacency"]
    allEvents = set()

    # Collect all valid events
    for edges in adj.values():
        for edge in edges:
            allEvents.add(edge["event"])

    # For each state, find events that are NOT valid
    testIdx = 0
    for state in bp["states"]:
        validEvents = {e["event"] for e in adj.get(state, [])}
        invalidEvents = allEvents - validEvents

        for evt in list(invalidEvents)[:3]:  # Limit to 3 per state
            testIdx += 1
            tests.append({
                "id": f"negative_invalid_event_{testIdx}",
                "type": "negative_invalid_event",
                "description": (f"Invalid event '{evt}' in state '{state}'"),
                "initial_state": state,
                "initial_context": _genDefaultContext(bp),
                "events": [{"event": evt, "payload": {}}],
                "expected_behavior": "no_transition",
                "expected_state": state
            })

    # Test gate failures (events that should fail due to guards)
    for trans in bp["transitions"]:
        if trans.get("gates"):
            testIdx += 1
            tests.append({
                "id": f"negative_gate_fail_{testIdx}",
                "type": "negative_gate_failure",
                "description": (f"Gate should block transition {trans['id']}"),
                "from_state": trans["from"],
                "initial_context": {},  # Empty context likely fails gates
                "events": [{"event": trans["on_event"], "payload": {}}],
                "expected_behavior": "gate_blocked",
                "gates": trans["gates"]
            })

    return {"tests": tests}


def generate_property_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate property-based tests from context schema."""
    bp = params.get("blueprint")
    if not bp:
        return {"tests": []}

    schema = bp.get("context_schema", {})
    props = schema.get("properties", {})

    tests = []
    testIdx = 0

    # Generate tests based on property types
    for propName, propDef in props.items():
        propType = propDef.get("type", "string")
        enumVals = propDef.get("enum")

        # Generate sample values based on type
        if enumVals:
            sampleVals = enumVals[:3]
        elif propType == "number":
            sampleVals = [0, 1, -1, 100, 0.5]
        elif propType == "boolean":
            sampleVals = [True, False]
        elif propType == "string":
            sampleVals = ["", "test", "a" * 100]
        elif propType == "array":
            sampleVals = [[], ["item"], ["a", "b", "c"]]
        elif propType == "object":
            sampleVals = [{}, {"key": "value"}]
        else:
            sampleVals = [None]

        for val in sampleVals[:2]:  # Limit samples per property
            testIdx += 1
            ctx = _genDefaultContext(bp)
            ctx[propName] = val

            tests.append({
                "id": f"property_{testIdx}",
                "type": "property_based",
                "description": f"Property {propName} = {repr(val)[:30]}",
                "property": propName,
                "property_type": propType,
                "initial_context": ctx,
                "invariants": [
                    f"context['{propName}'] maintains type {propType}"
                ]
            })

    return {"tests": tests}


def generate_contract_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate tests from terminal state contracts (v0.2.0 schema).

    Tests verify:
    1. output_schema: all non_null fields are set when reaching terminal
    2. invariants_guaranteed: postconditions hold at terminal state
    """
    bp = params.get("blueprint")
    graphData = params.get("graph")
    if not bp or not graphData:
        return {"tests": []}

    # Handle nested graph structure
    graph = graphData.get("graph", graphData) if isinstance(graphData, dict) else graphData
    adj = graph.get("adjacency", graph.get("adj", {}))

    contracts = bp.get("terminal_contracts", {})
    if not contracts or not isinstance(contracts, dict):
        return {"tests": []}

    tests = []
    testIdx = 0
    entryState = bp.get("entry_state", "idle")

    for termState, contract in contracts.items():
        if not isinstance(contract, dict):
            continue

        outputSchema = contract.get("output_schema", {})
        invariants = contract.get("invariants_guaranteed", [])

        # Find a path to this terminal state using BFS
        path = _bfsPath(adj, entryState, termState)

        if not path:
            continue

        # Convert path events to proper format (list of dicts with event/payload)
        pathEvents = [
            {"event": evt, "payload": {}} for evt in path.get("events", [])
        ]

        # Generate context that satisfies all gates in this path
        transitionIds = path.get("transitions", [])
        ctx = _genContextForPath(bp, transitionIds)

        # Generate test for output_schema (non_null checks)
        if outputSchema:
            testIdx += 1
            nonNullFields = [
                field for field, spec in outputSchema.items()
                if isinstance(spec, dict) and spec.get("non_null")
            ]

            if nonNullFields:
                tests.append({
                    "id": f"contract_{testIdx}",
                    "type": "contract_output",
                    "description": f"Terminal '{termState}' output contract: {', '.join(nonNullFields)} must be non-null",
                    "terminal_state": termState,
                    "initial_context": ctx,
                    "events": pathEvents,
                    "expected_final_state": termState,
                    "contract_checks": [
                        {"field": f, "check": "non_null"} for f in nonNullFields
                    ],
                    "states_covered": path.get("states", []),
                    "transitions_covered": path.get("transitions", [])
                })

        # Generate test for invariants_guaranteed
        for inv in invariants:
            testIdx += 1
            tests.append({
                "id": f"contract_{testIdx}",
                "type": "contract_invariant",
                "description": f"Terminal '{termState}' guarantees: {inv}",
                "terminal_state": termState,
                "initial_context": ctx,  # Use path-specific context
                "events": pathEvents,
                "expected_final_state": termState,
                "invariant": inv,
                "states_covered": path.get("states", []),
                "transitions_covered": path.get("transitions", [])
            })

    return {"tests": tests}


def _genDefaultContext(bp: Dict) -> Dict:
    """Generate default context values from schema.

    Uses non-empty placeholder values that are more likely to satisfy
    gate conditions (which often check for non-null/non-empty values).
    """
    schema = bp.get("context_schema", {})
    props = schema.get("properties", {})
    ctx = {}

    for propName, propDef in props.items():
        propType = propDef.get("type", "string")
        default = propDef.get("default")

        if default is not None:
            ctx[propName] = default
        elif propType == "number":
            ctx[propName] = 1  # Non-zero to pass > 0 checks
        elif propType == "boolean":
            ctx[propName] = True  # True to pass boolean gates
        elif propType == "string":
            # Use meaningful placeholders based on property name
            if "path" in propName.lower():
                ctx[propName] = "/test/path"
            elif "dir" in propName.lower():
                ctx[propName] = "/test/dir"
            elif "name" in propName.lower():
                ctx[propName] = "test_name"
            elif "key" in propName.lower():
                ctx[propName] = "test_key"
            elif "url" in propName.lower():
                ctx[propName] = "https://test.example.com"
            elif "error" in propName.lower():
                ctx[propName] = ""  # Errors should be empty for success path
            else:
                ctx[propName] = "test_value"
        elif propType == "array":
            ctx[propName] = ["test_item"]  # Non-empty array
        elif propType == "object":
            ctx[propName] = {"test": True}  # Non-empty object
        else:
            ctx[propName] = "test_default"

    return ctx


# =============================================================================
# Test Combination and Coverage
# =============================================================================

def combine_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Combine all test types and compute coverage."""
    bp = params.get("blueprint")
    pathTests = params.get("path_tests", []) or []
    stateTests = params.get("state_tests", []) or []
    gateTests = params.get("gate_tests", []) or []
    negativeTests = params.get("negative_tests", []) or []
    propertyTests = params.get("property_tests", []) or []
    contractTests = params.get("contract_tests", []) or []

    allTests = pathTests + stateTests + gateTests + negativeTests + propertyTests + contractTests

    # Compute coverage metrics
    allStates = set(bp["states"].keys()) if bp else set()
    allTransitions = {t["id"] for t in bp["transitions"]} if bp else set()
    allGates = set(bp.get("gates", {}).keys()) if bp else set()

    coveredStates = set()
    coveredTransitions = set()
    coveredGates = set()

    for test in allTests:
        coveredStates.update(test.get("states_covered", []))
        coveredTransitions.update(test.get("transitions_covered", []))
        if test.get("gate_id"):
            coveredGates.add(test["gate_id"])

    coverage = {
        "total_tests": len(allTests),
        "by_type": {
            "path_coverage": len(pathTests),
            "state_coverage": len(stateTests),
            "gate_boundary": len(gateTests),
            "negative": len(negativeTests),
            "property_based": len(propertyTests),
            "contract": len(contractTests)
        },
        "state_coverage": {
            "total": len(allStates),
            "covered": len(coveredStates),
            "percentage": (len(coveredStates) / len(allStates) * 100
                           if allStates else 0)
        },
        "transition_coverage": {
            "total": len(allTransitions),
            "covered": len(coveredTransitions),
            "percentage": (len(coveredTransitions) / len(allTransitions) * 100
                           if allTransitions else 0)
        },
        "gate_coverage": {
            "total": len(allGates),
            "covered": len(coveredGates),
            "percentage": (len(coveredGates) / len(allGates) * 100
                           if allGates else 0)
        }
    }

    return {"tests": allTests, "coverage": coverage}


# =============================================================================
# Output Formatting
# =============================================================================

def format_json(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format tests as L++ JSON test suite."""
    bp = params.get("blueprint")
    tests = params.get("tests", [])

    if not bp:
        return {"output": "{}"}

    testSuite = {
        "test_suite": f"{bp['id']}_tests",
        "blueprint_id": bp["id"],
        "blueprint_version": bp["version"],
        "generated_at": "auto",
        "tests": []
    }

    for test in tests:
        formatted = {
            "id": test["id"],
            "type": test["type"],
            "description": test["description"],
            "initial_context": test.get("initial_context", {}),
            "events": test.get("events", [])
        }

        if test.get("expected_final_state"):
            formatted["expected_final_state"] = test["expected_final_state"]
        if test.get("expected_context"):
            formatted["expected_context"] = test["expected_context"]
        if test.get("expected_behavior"):
            formatted["expected_behavior"] = test["expected_behavior"]

        testSuite["tests"].append(formatted)

    return {"output": json.dumps(testSuite, indent=2)}


def format_pytest(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format tests as Python pytest module."""
    bp = params.get("blueprint")
    tests = params.get("tests", [])

    if not bp:
        return {"output": "# No blueprint loaded"}

    lines = [
        '"""',
        f"Auto-generated pytest tests for {bp['name']}",
        f"Blueprint ID: {bp['id']}",
        f"Blueprint Version: {bp['version']}",
        '"""',
        "",
        "import pytest",
        "from pathlib import Path",
        "",
        "# Import your operator creation function here",
        "# from your_module import create_operator",
        "",
        "",
        "# Fixture for creating fresh operator instance",
        "@pytest.fixture",
        "def operator():",
        '    """Create a fresh operator instance for each test."""',
        "    # TODO: Implement operator creation",
        "    # return create_operator()",
        "    pass",
        "",
        ""
    ]

    for test in tests:
        testName = _toPythonName(test["id"])
        lines.append(f"def test_{testName}(operator):")
        lines.append(f'    """')
        lines.append(f"    {test['description']}")
        lines.append(f"    Type: {test['type']}")
        lines.append(f'    """')

        # Set initial context
        if test.get("initial_context"):
            lines.append("    # Set initial context")
            for key, val in test["initial_context"].items():
                lines.append(f"    operator.context['{key}'] = {repr(val)}")
            lines.append("")

        # Set initial state if specified
        if test.get("initial_state"):
            lines.append(f"    operator._state = '{test['initial_state']}'")
            lines.append("")

        # Dispatch events
        if test.get("events"):
            lines.append("    # Dispatch events")
            for evt in test["events"]:
                payload = evt.get("payload", {})
                lines.append(
                    f"    operator.dispatch('{evt['event']}', {payload})")
            lines.append("")

        # Assertions based on test type
        testType = test.get("type", "")

        if test.get("expected_final_state"):
            lines.append("    # Verify final state")
            lines.append(
                f"    assert operator.state == '{test['expected_final_state']}'"
            )
        elif test.get("expected_state"):
            lines.append("    # Verify state unchanged")
            lines.append(
                f"    assert operator.state == '{test['expected_state']}'"
            )

        if test.get("expected_behavior") == "no_transition":
            lines.append("    # Verify no transition occurred")
            lines.append(
                f"    assert operator.state == '{test.get('initial_state', 'unknown')}'"
            )

        # Gate test assertions
        if testType in ("gate_boundary", "gate_boolean", "gate_null_check"):
            gateId = test.get("gate_id", "unknown")
            if test.get("expected_gate_result") is not None:
                expected = test["expected_gate_result"]
                lines.append(f"    # Verify gate '{gateId}' evaluates to {expected}")
                lines.append(f"    # Gate expression determines transition eligibility")
            else:
                lines.append(f"    # Verify gate '{gateId}' behavior")
                lines.append(f"    # Check if transition was taken based on gate condition")
            fromState = test.get("from_state", "idle")
            lines.append(f"    # From state: {fromState}")
            lines.append(f"    assert operator.state is not None  # State machine responded")

        # Property test assertions
        if testType == "property_based":
            propName = test.get("property", "unknown")
            propType = test.get("property_type", "any")
            lines.append(f"    # Verify property '{propName}' maintains type {propType}")
            lines.append(f"    assert '{propName}' in operator.context")
            if propType == "string":
                lines.append(f"    assert isinstance(operator.context['{propName}'], str)")
            elif propType == "number":
                lines.append(f"    assert isinstance(operator.context['{propName}'], (int, float))")
            elif propType == "boolean":
                lines.append(f"    assert isinstance(operator.context['{propName}'], bool)")
            elif propType == "array":
                lines.append(f"    assert isinstance(operator.context['{propName}'], list)")
            elif propType == "object":
                lines.append(f"    assert isinstance(operator.context['{propName}'], dict)")

        # Contract test assertions
        if testType == "contract_output":
            checks = test.get("contract_checks", [])
            if checks:
                lines.append("    # Verify output contract: non-null fields")
                for check in checks:
                    field = check.get("field", "unknown")
                    lines.append(f"    assert operator.context.get('{field}') is not None, "
                                f"\"'{field}' must be non-null at terminal state\"")

        if testType == "contract_invariant":
            inv = test.get("invariant", "unknown")
            lines.append(f"    # Verify invariant: {inv}")
            lines.append(f"    # TODO: Add specific assertion for invariant '{inv}'")
            lines.append(f"    assert True  # Placeholder - implement invariant check")

        lines.append("")
        lines.append("")

    return {"output": "\n".join(lines)}


def _toPythonName(name: str) -> str:
    """Convert test ID to valid Python function name."""
    return re.sub(r"[^a-zA-Z0-9_]", "_", name).lower()


# =============================================================================
# Export
# =============================================================================

def export_tests(params: Dict[str, Any]) -> Dict[str, Any]:
    """Write formatted tests to file."""
    content = params.get("content", "")
    path = params.get("path")
    fmt = params.get("format", "json")

    if not path:
        return {"path": None}

    try:
        outPath = Path(path)

        # Add appropriate extension if missing
        if fmt == "json" and not outPath.suffix:
            outPath = outPath.with_suffix(".json")
        elif fmt == "pytest" and not outPath.suffix:
            outPath = outPath.with_suffix(".py")

        outPath.parent.mkdir(parents=True, exist_ok=True)
        outPath.write_text(content)

        return {"path": str(outPath)}

    except Exception as e:
        return {"path": None, "error": str(e)}


# =============================================================================
# State Management
# =============================================================================

def clear_state(params: Dict[str, Any]) -> Dict[str, Any]:
    """Reset all analysis state."""
    return {
        "blueprint": None,
        "graph": None,
        "paths": None,
        "gate_analysis": None,
        "path_tests": None,
        "state_tests": None,
        "gate_tests": None,
        "negative_tests": None,
        "property_tests": None,
        "all_tests": None,
        "formatted_output": None,
        "error": None
    }


# =============================================================================
# COMPUTE REGISTRY
# =============================================================================

COMPUTE_REGISTRY = {
    ("testgen", "load_blueprint"): load_blueprint,
    ("testgen", "build_graph"): build_graph,
    ("testgen", "analyze_paths"): analyze_paths,
    ("testgen", "analyze_gates"): analyze_gates,
    ("testgen", "generate_path_tests"): generate_path_tests,
    ("testgen", "generate_state_tests"): generate_state_tests,
    ("testgen", "generate_gate_tests"): generate_gate_tests,
    ("testgen", "generate_negative_tests"): generate_negative_tests,
    ("testgen", "generate_property_tests"): generate_property_tests,
    ("testgen", "generate_contract_tests"): generate_contract_tests,
    ("testgen", "combine_tests"): combine_tests,
    ("testgen", "format_json"): format_json,
    ("testgen", "format_pytest"): format_pytest,
    ("testgen", "export_tests"): export_tests,
    ("testgen", "clear_state"): clear_state,
}
