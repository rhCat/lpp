"""
L++ Legacy Code Extractor - Compute Units
Extract state machine patterns from legacy Python code.
"""
import ast
import json
import os
import re
from typing import Any, Dict, List, Optional, Set, Tuple


# Pattern markers for annotated mode
ANNOTATION_MARKERS = {
    "state": ["@state", "# STATE:", "# lpp:state"],
    "transition": ["@transition", "# TRANSITION:", "# lpp:transition"],
    "gate": ["@gate", "# GATE:", "# lpp:gate"],
    "action": ["@action", "# ACTION:", "# lpp:action"],
    "event": ["@event", "# EVENT:", "# lpp:event"],
}

# Keywords indicating state variables
STATE_KEYWORDS = ["state", "status", "mode", "phase", "stage", "step"]

# Keywords indicating state values
STATE_VALUE_KEYWORDS = {
    "initial": ["init", "initial", "start", "begin", "idle", "ready"],
    "processing": ["processing", "running", "active", "busy", "working"],
    "waiting": ["waiting", "pending", "queued", "blocked"],
    "terminal": ["done", "complete", "finished", "end", "final", "closed"],
    "error": ["error", "failed", "invalid", "rejected", "cancelled"],
}

# Event method prefixes
EVENT_PREFIXES = ["on_", "handle_", "do_", "process_", "when_"]


def loadSource(params: dict) -> dict:
    """Load Python source file from disk."""
    filePath = params.get("filePath")
    if not filePath:
        return {"sourceCode": None, "error": "No file path provided"}
    try:
        with open(filePath, "r", encoding="utf-8") as f:
            return {"sourceCode": f.read(), "error": None}
    except FileNotFoundError:
        return {"sourceCode": None, "error": f"File not found: {filePath}"}
    except Exception as e:
        return {"sourceCode": None, "error": str(e)}


def parseAst(params: dict) -> dict:
    """Parse Python source into AST."""
    source = params.get("sourceCode")
    if not source:
        return {"ast": None, "error": "No source code"}
    try:
        tree = ast.parse(source)
        astDict = _astToDict(tree)
        return {"ast": astDict, "error": None}
    except SyntaxError as e:
        return {"ast": None, "error": f"Syntax error: {e}"}


def _astToDict(node: ast.AST) -> dict:
    """Convert AST node to serializable dict."""
    if isinstance(node, ast.AST):
        result = {"_type": node.__class__.__name__}
        for field, value in ast.iter_fields(node):
            result[field] = _astToDict(value)
        if hasattr(node, "lineno"):
            result["lineno"] = node.lineno
        if hasattr(node, "col_offset"):
            result["col_offset"] = node.col_offset
        return result
    elif isinstance(node, list):
        return [_astToDict(x) for x in node]
    else:
        return node


def findStatePatterns(params: dict) -> dict:
    """Detect state machine patterns in code."""
    astDict = params.get("ast", {})
    mode = params.get("analysisMode", "heuristic")

    patterns = {
        "mode": mode,
        "stateClasses": [],
        "stateVariables": [],
        "ifChains": [],
        "matchStatements": [],
        "eventHandlers": [],
        "enumDefinitions": [],
        "constantDefinitions": [],
        "annotations": []
    }

    def walk(node, parent=None, className=None):
        if not isinstance(node, dict):
            return

        ntype = node.get("_type")

        # Pattern 1: Class with state attribute OR Enum
        if ntype == "ClassDef":
            clsName = node.get("name", "")
            bases = [_getName(b) for b in node.get("bases", [])]

            # Check if this is an Enum class (Pattern 6)
            isEnum = any("Enum" in b for b in bases)
            if isEnum:
                members = []
                for item in node.get("body", []):
                    if isinstance(item, dict) and item.get("_type") == "Assign":
                        for t in item.get("targets", []):
                            members.append({
                                "name": _getName(t),
                                "line": item.get("lineno")
                            })
                patterns["enumDefinitions"].append({
                    "name": clsName,
                    "members": members,
                    "line": node.get("lineno")
                })
                # Don't process enum as state class
                for item in node.get("body", []):
                    walk(item, node, clsName)
                return

            # Regular class - check for state attribute
            hasStateAttr = False
            stateAttrName = None
            methods = []

            for item in node.get("body", []):
                if isinstance(item, dict):
                    # Check for state attribute assignments at class level
                    if item.get("_type") == "Assign":
                        for target in item.get("targets", []):
                            tname = _getName(target).lower()
                            if any(kw in tname for kw in STATE_KEYWORDS):
                                hasStateAttr = True
                                stateAttrName = _getName(target)
                    # Collect methods and check __init__ for self.state
                    if item.get("_type") in ("FunctionDef", "AsyncFunctionDef"):
                        methodName = item.get("name")
                        methods.append({
                            "name": methodName,
                            "line": item.get("lineno"),
                            "isAsync": item.get("_type") == "AsyncFunctionDef"
                        })
                        # Check __init__ for self.state assignments
                        if methodName == "__init__":
                            for stmt in item.get("body", []):
                                if stmt.get("_type") == "Assign":
                                    for t in stmt.get("targets", []):
                                        if t.get("_type") == "Attribute":
                                            attr = t.get("attr", "").lower()
                                            if any(kw in attr for kw in
                                                   STATE_KEYWORDS):
                                                hasStateAttr = True
                                                stateAttrName = f"self.{t.get('attr')}"

            if hasStateAttr:
                patterns["stateClasses"].append({
                    "name": clsName,
                    "stateAttr": stateAttrName,
                    "methods": methods,
                    "line": node.get("lineno")
                })

            for item in node.get("body", []):
                walk(item, node, clsName)
            return

        # Pattern 2: Module-level state variables
        if ntype == "Assign" and parent and parent.get("_type") == "Module":
            for target in node.get("targets", []):
                tname = _getName(target).lower()
                if any(kw in tname for kw in STATE_KEYWORDS):
                    val = node.get("value", {})
                    patterns["stateVariables"].append({
                        "name": _getName(target),
                        "value": _getValue(val),
                        "line": node.get("lineno")
                    })

        # Pattern 3: If-elif chains checking state
        if ntype == "If":
            chain = _extractIfChain(node)
            if chain and len(chain) >= 2:
                stateVar = _findStateVarInChain(chain)
                if stateVar:
                    patterns["ifChains"].append({
                        "stateVar": stateVar,
                        "branches": chain,
                        "line": node.get("lineno"),
                        "className": className
                    })

        # Pattern 4: Match/case statements
        if ntype == "Match":
            subject = _getName(node.get("subject", {}))
            if any(kw in subject.lower() for kw in STATE_KEYWORDS):
                cases = []
                for case in node.get("cases", []):
                    pattern = case.get("pattern", {})
                    cases.append({
                        "pattern": _getPatternValue(pattern),
                        "line": case.get("lineno") if hasattr(case, "lineno") else
                        node.get("lineno")
                    })
                patterns["matchStatements"].append({
                    "subject": subject,
                    "cases": cases,
                    "line": node.get("lineno"),
                    "className": className
                })

        # Pattern 5: Event handlers
        if ntype in ("FunctionDef", "AsyncFunctionDef"):
            fname = node.get("name", "")
            if any(fname.startswith(p) for p in EVENT_PREFIXES):
                eventName = fname
                for p in EVENT_PREFIXES:
                    if fname.startswith(p):
                        eventName = fname[len(p):]
                        break
                patterns["eventHandlers"].append({
                    "name": fname,
                    "event": eventName.upper(),
                    "line": node.get("lineno"),
                    "className": className,
                    "args": [a.get("arg") for a in node.get("args", {}).get(
                        "args", [])]
                })

        # Pattern 6: Enum definitions - handled in Pattern 1 above

        # Pattern 7: Constants (uppercase) that might be states
        if ntype == "Assign" and parent and parent.get("_type") == "Module":
            for target in node.get("targets", []):
                tname = _getName(target)
                if tname.isupper() and isinstance(node.get("value"), dict):
                    val = node.get("value")
                    if val.get("_type") == "Constant" and isinstance(
                            val.get("value"), str):
                        patterns["constantDefinitions"].append({
                            "name": tname,
                            "value": val.get("value"),
                            "line": node.get("lineno")
                        })

        # Walk children
        for key, value in node.items():
            if isinstance(value, dict):
                walk(value, node, className)
            elif isinstance(value, list):
                for item in value:
                    if isinstance(item, dict):
                        walk(item, node, className)

    walk(astDict)

    # In annotated mode, also scan for comment markers
    if mode in ("annotated", "hybrid"):
        patterns["annotations"] = _findAnnotations(
            params.get("sourceCode", ""))

    return {"patterns": patterns}


def _extractIfChain(node: dict) -> List[dict]:
    """Extract all branches from an if-elif-else chain."""
    chain = []

    test = node.get("test", {})
    chain.append({
        "condition": _exprToStr(test),
        "testNode": test,
        "line": node.get("lineno"),
        "body": node.get("body", [])
    })

    orelse = node.get("orelse", [])
    if orelse and len(orelse) == 1 and orelse[0].get("_type") == "If":
        chain.extend(_extractIfChain(orelse[0]))
    elif orelse:
        chain.append({
            "condition": "else",
            "testNode": None,
            "line": node.get("lineno"),
            "body": orelse
        })

    return chain


def _findStateVarInChain(chain: List[dict]) -> Optional[str]:
    """Find state variable being checked in if-elif chain."""
    for branch in chain:
        test = branch.get("testNode")
        if not test:
            continue

        # Check for state == 'value' pattern
        if test.get("_type") == "Compare":
            left = _getName(test.get("left", {}))
            if any(kw in left.lower() for kw in STATE_KEYWORDS):
                return left

        # Check for self.state == 'value' pattern
        if test.get("_type") == "Compare":
            left = test.get("left", {})
            if left.get("_type") == "Attribute":
                attr = left.get("attr", "")
                if any(kw in attr.lower() for kw in STATE_KEYWORDS):
                    return f"self.{attr}"

    return None


def _findAnnotations(source: str) -> List[dict]:
    """Find annotation markers in source code."""
    annotations = []
    lines = source.split("\n")

    for i, line in enumerate(lines):
        for annType, markers in ANNOTATION_MARKERS.items():
            for marker in markers:
                if marker in line:
                    # Extract value after marker
                    idx = line.index(marker)
                    value = line[idx + len(marker):].strip()
                    annotations.append({
                        "type": annType,
                        "value": value,
                        "line": i + 1
                    })

    return annotations


def extractStates(params: dict) -> dict:
    """Extract state definitions from code."""
    astDict = params.get("ast", {})
    patterns = params.get("patterns", {})

    states = []
    uncertainties = []
    seenStates: Set[str] = set()

    def addState(stateId: str, name: str, desc: str, source: str, line: int,
                 confidence: float = 1.0):
        if stateId in seenStates:
            return
        seenStates.add(stateId)

        state = {
            "id": stateId,
            "name": name,
            "description": desc,
            "source": source,
            "line": line,
            "confidence": confidence
        }
        states.append(state)

        if confidence < 0.8:
            uncertainties.append({
                "type": "state",
                "element": state,
                "reason": f"Low confidence ({confidence:.0%}) - needs review"
            })

    # Extract from enum definitions (highest confidence)
    for enum in patterns.get("enumDefinitions", []):
        enumName = enum.get("name", "")
        if any(kw in enumName.lower() for kw in STATE_KEYWORDS):
            for member in enum.get("members", []):
                mname = member.get("name", "")
                stateId = mname.lower()
                stateName = _toTitleCase(mname)
                addState(stateId, stateName, f"From enum {enumName}.{mname}",
                         f"enum:{enumName}", member.get("line"), 1.0)

    # Extract from state class assignments
    for cls in patterns.get("stateClasses", []):
        clsName = cls.get("name", "")
        stateAttr = cls.get("stateAttr", "")

        # Find initial state value
        for body in _getClassBody(astDict, clsName):
            if body.get("_type") == "Assign":
                for target in body.get("targets", []):
                    if _getName(target) == stateAttr:
                        val = _getValue(body.get("value", {}))
                        if val:
                            stateId = str(val).lower().replace("'", "").replace(
                                '"', '')
                            addState(stateId, _toTitleCase(stateId),
                                     f"Initial state of {clsName}",
                                     f"class:{clsName}", body.get("lineno"), 0.95)

    # Extract from if-chain comparisons
    for chain in patterns.get("ifChains", []):
        for branch in chain.get("branches", []):
            test = branch.get("testNode")
            if test and test.get("_type") == "Compare":
                comparators = test.get("comparators", [])
                for comp in comparators:
                    val = _getValue(comp)
                    if val and isinstance(val, str):
                        stateId = val.lower()
                        addState(stateId, _toTitleCase(val),
                                 f"From condition check",
                                 "if-chain", branch.get("line"), 0.85)

    # Extract from match/case
    for match in patterns.get("matchStatements", []):
        for case in match.get("cases", []):
            patternVal = case.get("pattern")
            if patternVal and isinstance(patternVal, str):
                stateId = patternVal.lower()
                addState(stateId, _toTitleCase(patternVal),
                         "From match/case pattern",
                         "match", case.get("line"), 0.9)

    # Extract from constant definitions
    for const in patterns.get("constantDefinitions", []):
        constName = const.get("name", "")
        constVal = const.get("value", "")

        # Check if constant name or value matches state keywords
        for category, keywords in STATE_VALUE_KEYWORDS.items():
            if any(kw in constName.lower() or kw in constVal.lower()
                   for kw in keywords):
                stateId = constVal.lower() if constVal else constName.lower()
                addState(stateId, _toTitleCase(stateId),
                         f"From constant {constName}",
                         f"const:{constName}", const.get("line"), 0.7)
                break

    # Extract from annotations (if present)
    for ann in patterns.get("annotations", []):
        if ann.get("type") == "state":
            val = ann.get("value", "")
            if val:
                stateId = val.lower().replace(" ", "_")
                addState(stateId, _toTitleCase(val),
                         "From annotation",
                         "annotation", ann.get("line"), 1.0)

    return {"states": states, "uncertainties": uncertainties}


def extractTransitions(params: dict) -> dict:
    """Extract state transitions from methods."""
    astDict = params.get("ast", {})
    patterns = params.get("patterns", {})
    existingStates = params.get("extractedStates", [])

    transitions = []
    uncertainties = params.get("uncertainties", [])
    stateIds = {s["id"] for s in existingStates}
    tId = 0

    def addTransition(fromState: str, toState: str, event: str, source: str,
                      line: int, confidence: float = 1.0):
        nonlocal tId
        trans = {
            "id": f"t_{tId}",
            "from": fromState,
            "to": toState,
            "on_event": event,
            "source": source,
            "line": line,
            "confidence": confidence,
            "gates": [],
            "actions": []
        }
        transitions.append(trans)
        tId += 1

        if confidence < 0.8:
            uncertainties.append({
                "type": "transition",
                "element": trans,
                "reason": f"Low confidence ({confidence:.0%}) - needs review"
            })

    # Extract from state class methods
    for cls in patterns.get("stateClasses", []):
        clsName = cls.get("name", "")
        stateAttr = cls.get("stateAttr", "")

        for method in cls.get("methods", []):
            methodName = method.get("name", "")
            if methodName.startswith("_"):
                continue

            # Find state changes in method body
            methodBody = _getMethodBody(astDict, clsName, methodName)
            stateChanges = _findStateChanges(methodBody, stateAttr)

            for change in stateChanges:
                fromState = change.get("from", "*")
                toState = change.get("to")

                if toState:
                    event = methodName.upper()
                    addTransition(fromState, toState, event,
                                  f"method:{clsName}.{methodName}",
                                  change.get("line", method.get("line")), 0.9)

    # Extract from if-chains
    for chain in patterns.get("ifChains", []):
        stateVar = chain.get("stateVar", "")
        clsName = chain.get("className")

        for branch in chain.get("branches", []):
            fromState = _extractStateFromCondition(branch.get("testNode"))
            toState = _findStateAssignment(branch.get("body", []), stateVar)

            if fromState and toState:
                event = "AUTO" if not clsName else "PROCESS"
                addTransition(fromState, toState, event,
                              "if-chain", branch.get("line"), 0.85)

    # Extract from event handlers
    for handler in patterns.get("eventHandlers", []):
        eventName = handler.get("event", "")
        clsName = handler.get("className")

        # Find state changes in handler body
        handlerBody = _getMethodBody(astDict, clsName,
                                     handler.get("name")) if clsName else []

        stateChanges = _findStateChangesGeneric(handlerBody)

        for change in stateChanges:
            addTransition(change.get("from", "*"), change.get("to"),
                          eventName, f"handler:{handler.get('name')}",
                          handler.get("line"), 0.8)

    # Extract from annotations
    for ann in patterns.get("annotations", []):
        if ann.get("type") == "transition":
            val = ann.get("value", "")
            # Parse "from -> to ON event" format
            match = re.match(r"(\w+)\s*->\s*(\w+)(?:\s+ON\s+(\w+))?", val)
            if match:
                fromState = match.group(1).lower()
                toState = match.group(2).lower()
                event = match.group(3).upper() if match.group(3) else "AUTO"
                addTransition(fromState, toState, event,
                              "annotation", ann.get("line"), 1.0)

    return {"transitions": transitions, "uncertainties": uncertainties}


def _findStateChanges(body: List[dict], stateAttr: str) -> List[dict]:
    """Find state variable assignments in method body."""
    changes = []

    def walk(nodes, currentFrom=None):
        for node in nodes:
            if not isinstance(node, dict):
                continue

            ntype = node.get("_type")

            # Check for if statements checking current state
            if ntype == "If":
                test = node.get("test", {})
                fromState = _extractStateFromCondition(test)

                # Process if body
                toState = _findStateAssignment(node.get("body", []), stateAttr)
                if toState:
                    changes.append({
                        "from": fromState or "*",
                        "to": toState,
                        "line": node.get("lineno")
                    })

                # Process elif/else
                walk(node.get("orelse", []), currentFrom)

            # Direct state assignment
            elif ntype == "Assign":
                for target in node.get("targets", []):
                    targetName = _getName(target)
                    if stateAttr in targetName or "state" in targetName.lower():
                        toState = _getValue(node.get("value", {}))
                        if toState:
                            changes.append({
                                "from": currentFrom or "*",
                                "to": str(toState).lower().strip("'\""),
                                "line": node.get("lineno")
                            })

    walk(body)
    return changes


def _findStateChangesGeneric(body: List[dict]) -> List[dict]:
    """Find state changes without knowing specific state variable."""
    changes = []

    def walk(nodes):
        for node in nodes:
            if not isinstance(node, dict):
                continue

            ntype = node.get("_type")

            if ntype == "Assign":
                for target in node.get("targets", []):
                    targetName = _getName(target).lower()
                    if any(kw in targetName for kw in STATE_KEYWORDS):
                        toState = _getValue(node.get("value", {}))
                        if toState:
                            changes.append({
                                "from": "*",
                                "to": str(toState).lower().strip("'\""),
                                "line": node.get("lineno")
                            })

            # Recurse into body elements
            for key in ["body", "orelse", "finalbody"]:
                if key in node and isinstance(node[key], list):
                    walk(node[key])

    walk(body)
    return changes


def _extractStateFromCondition(test: Optional[dict]) -> Optional[str]:
    """Extract state value from a comparison condition."""
    if not test:
        return None

    if test.get("_type") == "Compare":
        comparators = test.get("comparators", [])
        for comp in comparators:
            val = _getValue(comp)
            if val and isinstance(val, str):
                return val.lower()

    return None


def _findStateAssignment(body: List[dict], stateAttr: str) -> Optional[str]:
    """Find state assignment in code body."""
    for node in body:
        if not isinstance(node, dict):
            continue

        if node.get("_type") == "Assign":
            for target in node.get("targets", []):
                targetName = _getName(target)
                if stateAttr in targetName or any(
                        kw in targetName.lower() for kw in STATE_KEYWORDS):
                    val = _getValue(node.get("value", {}))
                    if val:
                        return str(val).lower().strip("'\"")

    return None


def extractGates(params: dict) -> dict:
    """Extract gate conditions from if statements."""
    astDict = params.get("ast", {})
    patterns = params.get("patterns", {})
    transitions = params.get("extractedTransitions", [])

    gates = []
    uncertainties = params.get("uncertainties", [])
    gId = 0

    # Extract from if-chains
    for chain in patterns.get("ifChains", []):
        for branch in chain.get("branches", []):
            condition = branch.get("condition", "")
            if condition and condition != "else":
                gate = {
                    "id": f"g_{gId}",
                    "type": "expression",
                    "expression": condition,
                    "source": "if-chain",
                    "line": branch.get("line"),
                    "confidence": 0.85
                }
                gates.append(gate)
                gId += 1

    # Extract from match cases
    for match in patterns.get("matchStatements", []):
        subject = match.get("subject", "")
        for case in match.get("cases", []):
            patternVal = case.get("pattern")
            if patternVal:
                gate = {
                    "id": f"g_{gId}",
                    "type": "expression",
                    "expression": f"{subject} == '{patternVal}'",
                    "source": "match",
                    "line": case.get("line"),
                    "confidence": 0.9
                }
                gates.append(gate)
                gId += 1

    # Extract from annotations
    for ann in patterns.get("annotations", []):
        if ann.get("type") == "gate":
            gate = {
                "id": f"g_{gId}",
                "type": "expression",
                "expression": ann.get("value", ""),
                "source": "annotation",
                "line": ann.get("line"),
                "confidence": 1.0
            }
            gates.append(gate)
            gId += 1

    return {"gates": gates, "uncertainties": uncertainties}


def extractActions(params: dict) -> dict:
    """Extract actions from side effects."""
    astDict = params.get("ast", {})
    patterns = params.get("patterns", {})
    transitions = params.get("extractedTransitions", [])

    actions = []
    uncertainties = params.get("uncertainties", [])
    aId = 0
    seenActions: Set[str] = set()

    def addAction(name: str, actionType: str, target: str, value: str,
                  source: str, line: int, confidence: float = 1.0):
        nonlocal aId
        if name in seenActions:
            return
        seenActions.add(name)

        action = {
            "id": f"a_{aId}",
            "name": name,
            "type": actionType,
            "target": target,
            "value": value,
            "source": source,
            "line": line,
            "confidence": confidence
        }
        actions.append(action)
        aId += 1

        if confidence < 0.8:
            uncertainties.append({
                "type": "action",
                "element": action,
                "reason": f"Low confidence ({confidence:.0%}) - needs review"
            })

    # Extract from state class methods
    for cls in patterns.get("stateClasses", []):
        clsName = cls.get("name", "")
        stateAttr = cls.get("stateAttr", "")

        for method in cls.get("methods", []):
            methodName = method.get("name", "")
            if methodName.startswith("_"):
                continue

            methodBody = _getMethodBody(astDict, clsName, methodName)
            sideEffects = _findSideEffects(methodBody, stateAttr)

            for effect in sideEffects:
                actionName = f"{methodName}_{effect['type']}"
                addAction(actionName, effect["type"], effect.get("target", ""),
                          effect.get("value", ""),
                          f"method:{clsName}.{methodName}",
                          effect.get("line", method.get("line")), 0.85)

    # Extract from event handlers
    for handler in patterns.get("eventHandlers", []):
        clsName = handler.get("className")
        handlerName = handler.get("name", "")

        handlerBody = _getMethodBody(astDict, clsName, handlerName) if \
            clsName else []
        sideEffects = _findSideEffects(handlerBody)

        for effect in sideEffects:
            actionName = f"{handlerName}_{effect['type']}"
            addAction(actionName, effect["type"], effect.get("target", ""),
                      effect.get("value", ""),
                      f"handler:{handlerName}",
                      effect.get("line", handler.get("line")), 0.8)

    # Extract from annotations
    for ann in patterns.get("annotations", []):
        if ann.get("type") == "action":
            val = ann.get("value", "")
            # Parse "SET target = value" or "COMPUTE unit" format
            if val.startswith("SET "):
                match = re.match(r"SET\s+(\w+)\s*=\s*(.+)", val)
                if match:
                    addAction(f"set_{match.group(1)}", "set",
                              match.group(1), match.group(2),
                              "annotation", ann.get("line"), 1.0)
            elif val.startswith("COMPUTE "):
                unit = val[8:].strip()
                addAction(f"compute_{unit}", "compute",
                          "", unit,
                          "annotation", ann.get("line"), 1.0)

    return {"actions": actions, "uncertainties": uncertainties}


def _findSideEffects(body: List[dict], stateAttr: str = "") -> List[dict]:
    """Find side effects (non-state assignments, calls) in code body."""
    effects = []

    def walk(nodes):
        for node in nodes:
            if not isinstance(node, dict):
                continue

            ntype = node.get("_type")

            # Assignments (excluding state)
            if ntype == "Assign":
                for target in node.get("targets", []):
                    targetName = _getName(target)
                    if stateAttr and stateAttr in targetName:
                        continue
                    if any(kw in targetName.lower() for kw in STATE_KEYWORDS):
                        continue

                    effects.append({
                        "type": "set",
                        "target": targetName,
                        "value": _exprToStr(node.get("value", {})),
                        "line": node.get("lineno")
                    })

            # Method calls (potential compute actions)
            elif ntype == "Expr":
                val = node.get("value", {})
                if val.get("_type") == "Call":
                    funcName = _getName(val.get("func", {}))
                    if funcName and not funcName.startswith("print"):
                        effects.append({
                            "type": "compute",
                            "target": funcName,
                            "value": "",
                            "line": node.get("lineno")
                        })

            # Recurse
            for key in ["body", "orelse", "finalbody"]:
                if key in node and isinstance(node[key], list):
                    walk(node[key])

    walk(body)
    return effects


def analyzeEventHandlers(params: dict) -> dict:
    """Analyze event handler patterns."""
    astDict = params.get("ast", {})
    patterns = params.get("patterns", {})
    states = params.get("extractedStates", [])

    events = []
    uncertainties = params.get("uncertainties", [])
    stateIds = {s["id"] for s in states}

    for handler in patterns.get("eventHandlers", []):
        eventName = handler.get("event", "")
        clsName = handler.get("className")

        event = {
            "name": eventName,
            "handler": handler.get("name"),
            "args": handler.get("args", []),
            "source": f"handler:{handler.get('name')}",
            "line": handler.get("line"),
            "triggersTransitions": []
        }

        # Find which transitions this event triggers
        handlerBody = _getMethodBody(astDict, clsName, handler.get("name")) \
            if clsName else []
        stateChanges = _findStateChangesGeneric(handlerBody)

        for change in stateChanges:
            event["triggersTransitions"].append({
                "from": change.get("from"),
                "to": change.get("to")
            })

        events.append(event)

    # Also extract from annotations
    for ann in patterns.get("annotations", []):
        if ann.get("type") == "event":
            events.append({
                "name": ann.get("value", "").upper(),
                "handler": None,
                "args": [],
                "source": "annotation",
                "line": ann.get("line"),
                "triggersTransitions": []
            })

    return {"events": events, "uncertainties": uncertainties}


def inferEntryState(params: dict) -> dict:
    """Infer entry and terminal states."""
    astDict = params.get("ast", {})
    patterns = params.get("patterns", {})
    states = params.get("extractedStates", [])
    transitions = params.get("extractedTransitions", [])

    stateIds = [s["id"] for s in states]
    entryState = None
    terminalStates = []

    # Rule 1: State with "init", "start", "idle" in name
    for state in states:
        sid = state["id"].lower()
        if any(kw in sid for kw in STATE_VALUE_KEYWORDS["initial"]):
            entryState = state["id"]
            break

    # Rule 2: First state defined
    if not entryState and states:
        entryState = states[0]["id"]

    # Rule 3: State never reached by any transition
    if not entryState and stateIds:
        targetStates = {t["to"] for t in transitions}
        unreachable = [s for s in stateIds if s not in targetStates]
        if unreachable:
            entryState = unreachable[0]

    # Terminal states: states with no outgoing transitions
    sourceStates = {t["from"] for t in transitions if t["from"] != "*"}
    for state in states:
        sid = state["id"]
        # Has no outgoing transitions
        if sid not in sourceStates:
            terminalStates.append(sid)
        # Or has terminal keywords
        elif any(kw in sid.lower() for kw in STATE_VALUE_KEYWORDS["terminal"]):
            if sid not in terminalStates:
                terminalStates.append(sid)
        elif any(kw in sid.lower() for kw in STATE_VALUE_KEYWORDS["error"]):
            if sid not in terminalStates:
                terminalStates.append(sid)

    # Ensure entry state is set
    if not entryState:
        entryState = "idle"

    return {"entryState": entryState, "terminalStates": terminalStates}


def generateBlueprint(params: dict) -> dict:
    """Generate L++ blueprint from extracted elements."""
    filePath = params.get("filePath", "extracted")
    states = params.get("extractedStates", [])
    transitions = params.get("extractedTransitions", [])
    gates = params.get("extractedGates", [])
    actions = params.get("extractedActions", [])
    events = params.get("extractedEvents", [])
    entryState = params.get("entryState", "idle")
    terminalStates = params.get("terminalStates", [])

    baseName = os.path.basename(filePath).replace(".py", "") if filePath else \
        "extracted"

    # Build states dict
    statesDict = {}
    for s in states:
        statesDict[s["id"]] = {
            "description": s.get("description", f"Extracted from {s['source']}")
        }

    # Ensure entry state exists
    if entryState not in statesDict:
        statesDict[entryState] = {"description": "Entry state (inferred)"}

    # Build gates dict
    gatesDict = {}
    for g in gates:
        gatesDict[g["id"]] = {
            "type": g.get("type", "expression"),
            "expression": g.get("expression", "true")
        }

    # Build actions dict
    actionsDict = {}
    for a in actions:
        if a["type"] == "set":
            actionsDict[a["id"]] = {
                "type": "set",
                "target": a.get("target", ""),
                "value_from": a.get("value", "")
            }
        elif a["type"] == "compute":
            actionsDict[a["id"]] = {
                "type": "compute",
                "compute_unit": f"impl:{a.get('target', a['name'])}",
                "input_map": {},
                "output_map": {}
            }

    # Build transitions array
    transArr = []
    for t in transitions:
        trans = {
            "id": t["id"],
            "from": t["from"],
            "to": t["to"],
            "on_event": t["on_event"]
        }
        if t.get("gates"):
            trans["gates"] = t["gates"]
        if t.get("actions"):
            trans["actions"] = t["actions"]
        transArr.append(trans)

    # Build context schema from states and actions
    contextProps = {}
    for s in states:
        contextProps["currentState"] = {"type": "string"}
    for a in actions:
        if a["type"] == "set":
            contextProps[a.get("target", "data")] = {"type": "object"}
    contextProps["error"] = {"type": "string"}

    blueprint = {
        "$schema": "lpp/v0.1.2",
        "id": f"extracted_{baseName}",
        "name": f"Extracted: {_toTitleCase(baseName)}",
        "version": "1.0.0",
        "description": f"State machine extracted from {filePath}",
        "context_schema": {"properties": contextProps},
        "states": statesDict,
        "transitions": transArr,
        "gates": gatesDict,
        "actions": actionsDict,
        "entry_state": entryState,
        "terminal_states": terminalStates,
        "display": {"rules": []}
    }

    return {
        "blueprint": blueprint,
        "blueprintJson": json.dumps(blueprint, indent=2)
    }


def generateMapping(params: dict) -> dict:
    """Generate source-to-blueprint mapping."""
    filePath = params.get("filePath", "")
    states = params.get("extractedStates", [])
    transitions = params.get("extractedTransitions", [])
    gates = params.get("extractedGates", [])
    actions = params.get("extractedActions", [])
    blueprint = params.get("blueprint", {})

    mapping = {
        "source": filePath,
        "blueprint_id": blueprint.get("id", ""),
        "elements": []
    }

    # Map states
    for s in states:
        mapping["elements"].append({
            "type": "state",
            "source_location": f"{filePath}:{s.get('line', '?')}",
            "blueprint_element": f"states.{s['id']}",
            "confidence": s.get("confidence", 1.0),
            "source_type": s.get("source", "unknown")
        })

    # Map transitions
    for t in transitions:
        mapping["elements"].append({
            "type": "transition",
            "source_location": f"{filePath}:{t.get('line', '?')}",
            "blueprint_element": f"transitions.{t['id']}",
            "confidence": t.get("confidence", 1.0),
            "source_type": t.get("source", "unknown")
        })

    # Map gates
    for g in gates:
        mapping["elements"].append({
            "type": "gate",
            "source_location": f"{filePath}:{g.get('line', '?')}",
            "blueprint_element": f"gates.{g['id']}",
            "confidence": g.get("confidence", 1.0),
            "source_type": g.get("source", "unknown")
        })

    # Map actions
    for a in actions:
        mapping["elements"].append({
            "type": "action",
            "source_location": f"{filePath}:{a.get('line', '?')}",
            "blueprint_element": f"actions.{a['id']}",
            "confidence": a.get("confidence", 1.0),
            "source_type": a.get("source", "unknown")
        })

    # Generate report
    report = {
        "source_file": filePath,
        "blueprint_id": blueprint.get("id", ""),
        "extraction_summary": {
            "states_extracted": len(states),
            "transitions_extracted": len(transitions),
            "gates_extracted": len(gates),
            "actions_extracted": len(actions)
        },
        "confidence_summary": {
            "high_confidence": len([e for e in mapping["elements"]
                                    if e.get("confidence", 0) >= 0.9]),
            "medium_confidence": len([e for e in mapping["elements"]
                                      if 0.7 <= e.get("confidence", 0) < 0.9]),
            "low_confidence": len([e for e in mapping["elements"]
                                   if e.get("confidence", 0) < 0.7])
        },
        "source_coverage": {
            "classes_analyzed": 0,
            "functions_analyzed": 0,
            "lines_mapped": len(set(e.get("source_location", "").split(":")[-1]
                                    for e in mapping["elements"]))
        }
    }

    return {"sourceMapping": mapping, "report": report}


def exportBlueprint(params: dict) -> dict:
    """Export blueprint to file."""
    blueprintJson = params.get("blueprintJson", "")
    outputPath = params.get("outputPath")

    if not outputPath:
        return {"error": "No output path specified"}

    try:
        with open(outputPath, "w", encoding="utf-8") as f:
            f.write(blueprintJson)
        return {"error": None}
    except Exception as e:
        return {"error": f"Failed to export: {e}"}


def exportReport(params: dict) -> dict:
    """Export extraction report."""
    report = params.get("extractionReport", {})
    mapping = params.get("sourceMapping", {})
    uncertainties = params.get("uncertainties", [])
    outputPath = params.get("outputPath")

    if not outputPath:
        return {"error": "No output path specified"}

    fullReport = {
        "summary": report,
        "mapping": mapping,
        "uncertainties": uncertainties,
        "requires_review": len(uncertainties)
    }

    try:
        with open(outputPath, "w", encoding="utf-8") as f:
            json.dump(fullReport, f, indent=2)
        return {"error": None}
    except Exception as e:
        return {"error": f"Failed to export report: {e}"}


def clearState(params: dict) -> dict:
    """Reset all extraction state."""
    return {
        "sourceCode": None,
        "ast": None,
        "patterns": None,
        "extractedStates": None,
        "extractedTransitions": None,
        "extractedGates": None,
        "extractedActions": None,
        "extractedEvents": None,
        "entryState": None,
        "terminalStates": None,
        "blueprint": None,
        "blueprintJson": None,
        "sourceMapping": None,
        "uncertainties": None,
        "extractionReport": None,
        "error": None
    }


# Helper functions

def _getName(node: Any) -> str:
    """Extract name from AST node."""
    if node is None:
        return ""
    if isinstance(node, str):
        return node
    if isinstance(node, dict):
        ntype = node.get("_type")
        if ntype == "Name":
            return node.get("id", "")
        elif ntype == "Attribute":
            val = _getName(node.get("value"))
            return f"{val}.{node.get('attr', '')}"
        elif ntype == "Constant":
            return str(node.get("value", ""))
    return ""


def _getValue(node: Any) -> Any:
    """Extract value from AST node."""
    if node is None:
        return None
    if isinstance(node, dict):
        ntype = node.get("_type")
        if ntype == "Constant":
            return node.get("value")
        elif ntype == "Name":
            return node.get("id")
        elif ntype == "Attribute":
            return _getName(node)
    return None


def _getPatternValue(node: dict) -> Any:
    """Extract pattern value from match case."""
    if not isinstance(node, dict):
        return None
    ntype = node.get("_type")
    if ntype == "MatchValue":
        return _getValue(node.get("value"))
    elif ntype == "MatchAs":
        return node.get("name") or "_"
    return None


def _exprToStr(node: dict) -> str:
    """Convert expression node to readable string."""
    if not isinstance(node, dict):
        return str(node) if node else ""

    ntype = node.get("_type")
    if ntype == "Name":
        return node.get("id", "?")
    elif ntype == "Constant":
        val = node.get("value")
        if isinstance(val, str):
            return f"'{val}'"
        return str(val)
    elif ntype == "Attribute":
        return _getName(node)
    elif ntype == "Compare":
        left = _exprToStr(node.get("left"))
        ops = node.get("ops", [])
        comps = node.get("comparators", [])
        opMap = {"Eq": "==", "NotEq": "!=", "Lt": "<", "LtE": "<=",
                 "Gt": ">", "GtE": ">=", "Is": "is", "IsNot": "is not",
                 "In": "in", "NotIn": "not in"}
        opStr = opMap.get(ops[0].get("_type", "?"), "?") if ops else "?"
        right = _exprToStr(comps[0]) if comps else "?"
        return f"{left} {opStr} {right}"
    elif ntype == "BoolOp":
        op = node.get("op", {}).get("_type", "And")
        opStr = "and" if op == "And" else "or"
        vals = [_exprToStr(v) for v in node.get("values", [])]
        return f" {opStr} ".join(vals)
    elif ntype == "Call":
        return f"{_getName(node.get('func'))}(...)"

    return "..."


def _toTitleCase(s: str) -> str:
    """Convert snake_case or SCREAMING_CASE to Title Case."""
    words = s.replace("_", " ").replace("-", " ").split()
    return " ".join(w.capitalize() for w in words)


def _getClassBody(astDict: dict, className: str) -> List[dict]:
    """Get body of a class definition."""
    def find(node):
        if isinstance(node, dict):
            if node.get("_type") == "ClassDef" and node.get("name") == className:
                return node.get("body", [])
            for v in node.values():
                result = find(v)
                if result:
                    return result
        elif isinstance(node, list):
            for item in node:
                result = find(item)
                if result:
                    return result
        return None

    return find(astDict) or []


def _getMethodBody(astDict: dict, className: Optional[str],
                   methodName: str) -> List[dict]:
    """Get body of a method definition."""
    if className:
        classBody = _getClassBody(astDict, className)
        for item in classBody:
            if (isinstance(item, dict) and
                    item.get("_type") in ("FunctionDef", "AsyncFunctionDef") and
                    item.get("name") == methodName):
                return item.get("body", [])
    else:
        # Module-level function
        def find(node):
            if isinstance(node, dict):
                if (node.get("_type") in ("FunctionDef", "AsyncFunctionDef") and
                        node.get("name") == methodName):
                    return node.get("body", [])
                for v in node.values():
                    result = find(v)
                    if result:
                        return result
            elif isinstance(node, list):
                for item in node:
                    result = find(item)
                    if result:
                        return result
            return None

        return find(astDict) or []

    return []


# Registry
EXTRACT_REGISTRY = {
    "extract:loadSource": loadSource,
    "extract:parseAst": parseAst,
    "extract:findStatePatterns": findStatePatterns,
    "extract:extractStates": extractStates,
    "extract:extractTransitions": extractTransitions,
    "extract:extractGates": extractGates,
    "extract:extractActions": extractActions,
    "extract:analyzeEventHandlers": analyzeEventHandlers,
    "extract:inferEntryState": inferEntryState,
    "extract:generateBlueprint": generateBlueprint,
    "extract:generateMapping": generateMapping,
    "extract:exportBlueprint": exportBlueprint,
    "extract:exportReport": exportReport,
    "extract:clearState": clearState,
}
