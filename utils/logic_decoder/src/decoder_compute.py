"""
L++ Logic Decoder - Compute Units
Decode Python files into L++ blueprints via AST analysis.
"""
import ast
import json
import os
from typing import Any

# Import semantic mappings for common packages
IMPORT_SEMANTICS = {
    # HTTP/API
    "requests": {"category": "http", "actions": ["fetch", "post", "get"]},
    "httpx": {"category": "http", "actions": ["fetch", "post", "get"]},
    "aiohttp": {"category": "http", "actions": ["asyncFetch"]},
    "urllib": {"category": "http", "actions": ["fetch"]},
    # Data
    "json": {"category": "serialization", "actions": ["parse", "dump"]},
    "yaml": {"category": "serialization", "actions": ["parse", "dump"]},
    "pickle": {"category": "serialization", "actions": ["load", "dump"]},
    "csv": {"category": "data", "actions": ["read", "write"]},
    "pandas": {"category": "dataframe", "actions": ["transform", "filter"]},
    "numpy": {"category": "compute", "actions": ["calculate"]},
    # File I/O
    "os": {"category": "filesystem", "actions": ["readFile", "writeFile"]},
    "pathlib": {"category": "filesystem", "actions": ["resolvePath"]},
    "shutil": {"category": "filesystem", "actions": ["copy", "move"]},
    # Async
    "asyncio": {"category": "async", "actions": ["await", "gather"]},
    "concurrent": {"category": "parallel", "actions": ["fork", "join"]},
    "threading": {"category": "parallel", "actions": ["fork", "join"]},
    "multiprocessing": {"category": "parallel", "actions": ["fork", "join"]},
    # Database
    "sqlite3": {"category": "database", "actions": ["query", "execute"]},
    "sqlalchemy": {"category": "database", "actions": ["query", "commit"]},
    "pymongo": {"category": "database", "actions": ["find", "insert"]},
    "redis": {"category": "cache", "actions": ["get", "set"]},
    # Logging/Debug
    "logging": {"category": "observability", "actions": ["emit"]},
    "print": {"category": "observability", "actions": ["emit"]},
    # Time
    "time": {"category": "timing", "actions": ["wait", "measure"]},
    "datetime": {"category": "timing", "actions": ["timestamp"]},
    # Regex/Text
    "re": {"category": "text", "actions": ["match", "search", "replace"]},
    # Type hints
    "typing": {"category": "meta", "actions": []},
    # CLI
    "argparse": {"category": "cli", "actions": ["parseArgs"]},
    "click": {"category": "cli", "actions": ["parseArgs"]},
    "sys": {"category": "system", "actions": ["exit", "readStdin"]},
}

# Control flow patterns that map to states
CONTROL_PATTERNS = {
    "if": "branch",
    "elif": "branch",
    "else": "branch",
    "while": "loop",
    "for": "iteration",
    "try": "errorHandling",
    "except": "errorRecovery",
    "finally": "cleanup",
    "with": "resourceScope",
    "match": "dispatch",
    "case": "dispatch",
}


def hasValue(params: dict) -> dict:
    """Gate: check if context field has non-null value."""
    field = params.get("field", "").strip("'\"")
    val = params.get(field)
    return {"result": val is not None and val != "" and val != []}


def loadFile(params: dict) -> dict:
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
        return result
    elif isinstance(node, list):
        return [_astToDict(x) for x in node]
    else:
        return node


def analyzeImports(params: dict) -> dict:
    """Extract and resolve import semantics."""
    astDict = params.get("ast", {})
    imports = []

    def walk(node):
        if isinstance(node, dict):
            ntype = node.get("_type")
            if ntype == "Import":
                for alias in node.get("names", []):
                    name = alias.get("name", "")
                    modName = name.split(".")[0]
                    imports.append({
                        "module": name,
                        "alias": alias.get("asname"),
                        "semantic": IMPORT_SEMANTICS.get(modName, {
                            "category": "unknown",
                            "actions": []
                        }),
                        "line": node.get("lineno")
                    })
            elif ntype == "ImportFrom":
                mod = node.get("module", "")
                modName = mod.split(".")[0] if mod else ""
                for alias in node.get("names", []):
                    imports.append({
                        "module": mod,
                        "name": alias.get("name"),
                        "alias": alias.get("asname"),
                        "semantic": IMPORT_SEMANTICS.get(modName, {
                            "category": "unknown",
                            "actions": []
                        }),
                        "line": node.get("lineno")
                    })
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for item in node:
                walk(item)

    walk(astDict)
    return {"imports": imports}


def analyzeFunctions(params: dict) -> dict:
    """Extract function and class definitions."""
    astDict = params.get("ast", {})
    imports = params.get("imports", [])
    functions = []
    classes = []

    importedNames = {i.get("alias") or i.get("name") or i.get("module", "")
                     .split(".")[-1] for i in imports}

    def extractFn(node, className=None):
        if node.get("_type") in ("FunctionDef", "AsyncFunctionDef"):
            args = []
            for arg in node.get("args", {}).get("args", []):
                args.append(arg.get("arg"))
            returns = _extractType(node.get("returns"))
            decorators = [_extractName(d) for d in node.get("decorator_list",
                                                            [])]
            # Analyze body for side effects
            sideEffects = _findSideEffects(node.get("body", []), importedNames)
            fnData = {
                "name": node.get("name"),
                "args": args,
                "returns": returns,
                "decorators": decorators,
                "isAsync": node.get("_type") == "AsyncFunctionDef",
                "line": node.get("lineno"),
                "sideEffects": sideEffects,
                "className": className,
                "docstring": _extractDocstring(node)
            }
            functions.append(fnData)

    def walk(node, className=None):
        if isinstance(node, dict):
            ntype = node.get("_type")
            if ntype == "ClassDef":
                bases = [_extractName(b) for b in node.get("bases", [])]
                classes.append({
                    "name": node.get("name"),
                    "bases": bases,
                    "line": node.get("lineno"),
                    "docstring": _extractDocstring(node)
                })
                for item in node.get("body", []):
                    walk(item, className=node.get("name"))
            elif ntype in ("FunctionDef", "AsyncFunctionDef"):
                extractFn(node, className)
                for item in node.get("body", []):
                    walk(item, className)
            else:
                for v in node.values():
                    walk(v, className)
        elif isinstance(node, list):
            for item in node:
                walk(item, className)

    walk(astDict)
    return {"functions": functions, "classes": classes}


def _extractDocstring(node: dict) -> str:
    """Extract docstring from function/class body."""
    body = node.get("body", [])
    if body and isinstance(body, list) and len(body) > 0:
        first = body[0]
        if (first.get("_type") == "Expr" and
                first.get("value", {}).get("_type") == "Constant"):
            val = first.get("value", {}).get("value")
            if isinstance(val, str):
                return val.strip()
    return ""


def _extractType(node: Any) -> str:
    """Extract type annotation string."""
    if node is None:
        return "Any"
    if isinstance(node, dict):
        ntype = node.get("_type")
        if ntype == "Name":
            return node.get("id", "Any")
        elif ntype == "Constant":
            return str(node.get("value", "Any"))
        elif ntype == "Subscript":
            val = _extractName(node.get("value"))
            slc = _extractType(node.get("slice"))
            return f"{val}[{slc}]"
    return "Any"


def _extractName(node: Any) -> str:
    """Extract name from AST node."""
    if node is None:
        return ""
    if isinstance(node, dict):
        ntype = node.get("_type")
        if ntype == "Name":
            return node.get("id", "")
        elif ntype == "Attribute":
            val = _extractName(node.get("value"))
            return f"{val}.{node.get('attr', '')}"
        elif ntype == "Call":
            return _extractName(node.get("func"))
    return str(node) if node else ""


def _findSideEffects(body: list, importedNames: set) -> list:
    """Find side effects (calls, assignments) in function body."""
    effects = []

    def walk(node):
        if isinstance(node, dict):
            ntype = node.get("_type")
            if ntype == "Call":
                fname = _extractName(node.get("func"))
                root = fname.split(".")[0]
                effects.append({
                    "type": "call",
                    "name": fname,
                    "isImported": root in importedNames,
                    "line": node.get("lineno")
                })
            elif ntype == "Assign":
                for t in node.get("targets", []):
                    tname = _extractName(t)
                    effects.append({
                        "type": "assign",
                        "target": tname,
                        "line": node.get("lineno")
                    })
            for v in node.values():
                walk(v)
        elif isinstance(node, list):
            for item in node:
                walk(item)

    for item in body:
        walk(item)
    return effects


def analyzeControlFlow(params: dict) -> dict:
    """Build control flow graph from AST."""
    astDict = params.get("ast", {})
    functions = params.get("functions", [])
    cfg = {"nodes": [], "edges": [], "patterns": {}}

    nodeId = [0]

    def addNode(label, ntype, line=None):
        nid = f"n{nodeId[0]}"
        nodeId[0] += 1
        cfg["nodes"].append({
            "id": nid,
            "label": label,
            "type": ntype,
            "line": line
        })
        return nid

    def addEdge(src, dst, label=""):
        cfg["edges"].append({"from": src, "to": dst, "label": label})

    def walkBody(body, prevId=None):
        lastId = prevId
        for node in body:
            if isinstance(node, dict):
                ntype = node.get("_type")
                line = node.get("lineno")

                if ntype == "If":
                    testStr = _exprToStr(node.get("test", {}))
                    ifId = addNode(f"if {testStr}", "branch", line)
                    if lastId:
                        addEdge(lastId, ifId)
                    cfg["patterns"]["branch"] = cfg["patterns"].get("branch",
                                                                    0) + 1
                    # True branch
                    thenEnd = walkBody(node.get("body", []), ifId)
                    # False branch
                    elseBody = node.get("orelse", [])
                    if elseBody:
                        elseEnd = walkBody(elseBody, ifId)
                        mergeId = addNode("merge", "merge", line)
                        if thenEnd:
                            addEdge(thenEnd, mergeId, "then")
                        if elseEnd:
                            addEdge(elseEnd, mergeId, "else")
                        lastId = mergeId
                    else:
                        lastId = thenEnd or ifId

                elif ntype == "For":
                    iterStr = _exprToStr(node.get("iter", {}))
                    forId = addNode(f"for {iterStr}", "loop", line)
                    if lastId:
                        addEdge(lastId, forId)
                    cfg["patterns"]["loop"] = cfg["patterns"].get("loop", 0)+1
                    bodyEnd = walkBody(node.get("body", []), forId)
                    if bodyEnd:
                        addEdge(bodyEnd, forId, "next")
                    lastId = forId

                elif ntype == "While":
                    testStr = _exprToStr(node.get("test", {}))
                    whileId = addNode(f"while {testStr}", "loop", line)
                    if lastId:
                        addEdge(lastId, whileId)
                    cfg["patterns"]["loop"] = cfg["patterns"].get("loop", 0)+1
                    bodyEnd = walkBody(node.get("body", []), whileId)
                    if bodyEnd:
                        addEdge(bodyEnd, whileId, "loop")
                    lastId = whileId

                elif ntype == "Try":
                    tryId = addNode("try", "errorHandling", line)
                    if lastId:
                        addEdge(lastId, tryId)
                    cfg["patterns"]["errorHandling"] = cfg["patterns"].get(
                        "errorHandling", 0) + 1
                    bodyEnd = walkBody(node.get("body", []), tryId)
                    handlers = node.get("handlers", [])
                    handlerEnds = []
                    for h in handlers:
                        htype = _extractName(h.get("type"))
                        hId = addNode(f"except {htype}", "errorRecovery", line)
                        addEdge(tryId, hId, "error")
                        hEnd = walkBody(h.get("body", []), hId)
                        if hEnd:
                            handlerEnds.append(hEnd)
                    finallyBody = node.get("finalbody", [])
                    if finallyBody:
                        finId = addNode("finally", "cleanup", line)
                        if bodyEnd:
                            addEdge(bodyEnd, finId, "ok")
                        for he in handlerEnds:
                            addEdge(he, finId)
                        lastId = walkBody(finallyBody, finId) or finId
                    else:
                        lastId = bodyEnd

                elif ntype == "Return":
                    retId = addNode("return", "terminal", line)
                    if lastId:
                        addEdge(lastId, retId)
                    lastId = None

                elif ntype in ("Expr", "Assign", "AugAssign"):
                    label = _stmtLabel(node)
                    stmtId = addNode(label, "statement", line)
                    if lastId:
                        addEdge(lastId, stmtId)
                    lastId = stmtId

        return lastId

    # Process each function
    for fn in functions:
        fnName = fn.get("name", "main")
        entryId = addNode(f"fn:{fnName}", "entry", fn.get("line"))
        # Re-parse to get body (simplified: walk AST again)

    # Walk module-level
    moduleBody = astDict.get("body", [])
    walkBody(moduleBody)

    return {"controlFlow": cfg}


def _exprToStr(node: dict) -> str:
    """Convert expression node to readable string."""
    if not isinstance(node, dict):
        return str(node)
    ntype = node.get("_type")
    if ntype == "Name":
        return node.get("id", "?")
    elif ntype == "Constant":
        return repr(node.get("value"))
    elif ntype == "Compare":
        left = _exprToStr(node.get("left"))
        ops = node.get("ops", [])
        comps = node.get("comparators", [])
        opStr = ops[0].get("_type", "?") if ops else "?"
        opMap = {"Eq": "==", "NotEq": "!=", "Lt": "<", "LtE": "<=",
                 "Gt": ">", "GtE": ">=", "Is": "is", "IsNot": "is not",
                 "In": "in", "NotIn": "not in"}
        op = opMap.get(opStr, opStr)
        right = _exprToStr(comps[0]) if comps else "?"
        return f"{left} {op} {right}"
    elif ntype == "BoolOp":
        op = node.get("op", {}).get("_type", "and")
        opStr = "and" if op == "And" else "or"
        vals = [_exprToStr(v) for v in node.get("values", [])]
        return f" {opStr} ".join(vals)
    elif ntype == "Call":
        return f"{_extractName(node.get('func'))}(...)"
    elif ntype == "Attribute":
        return _extractName(node)
    return "..."


def _stmtLabel(node: dict) -> str:
    """Generate label for statement node."""
    ntype = node.get("_type")
    if ntype == "Expr":
        return _exprToStr(node.get("value", {}))
    elif ntype == "Assign":
        targets = [_extractName(t) for t in node.get("targets", [])]
        return f"{', '.join(targets)} = ..."
    elif ntype == "AugAssign":
        return f"{_extractName(node.get('target'))} += ..."
    return ntype


def inferStates(params: dict) -> dict:
    """Infer state machine states from code structure."""
    functions = params.get("functions", [])
    classes = params.get("classes", [])
    controlFlow = params.get("controlFlow", {})
    imports = params.get("imports", [])

    states = []
    stateId = 0

    # Entry state
    states.append({
        "id": "idle",
        "name": "Idle",
        "description": "Initial state",
        "inferred_from": "entry_point"
    })

    # Infer states from function names
    for fn in functions:
        name = fn.get("name", "")
        if name.startswith("_"):
            continue  # Skip private
        
        # Convert function name to readable state name
        def to_state_name(fn_name):
            """Convert snake_case to Title Case"""
            words = fn_name.replace("_", " ").split()
            return " ".join(w.capitalize() for w in words)
        
        # Common patterns -> grouped states
        if any(kw in name.lower() for kw in ["init", "setup", "start"]):
            states.append({
                "id": f"initializing",
                "name": "Initializing",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["process", "handle", "run", "execute"]):
            states.append({
                "id": f"processing",
                "name": "Processing",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["validate", "check", "verify"]):
            states.append({
                "id": f"validating",
                "name": "Validating",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["load", "fetch", "get", "read"]):
            states.append({
                "id": f"loading",
                "name": "Loading",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["save", "write", "store"]):
            states.append({
                "id": f"saving",
                "name": "Saving",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["error", "fail", "except"]):
            states.append({
                "id": f"error",
                "name": "Error",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["query", "search", "find", "lookup"]):
            states.append({
                "id": f"querying",
                "name": "Querying",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["generate", "create", "build", "make"]):
            states.append({
                "id": f"generating",
                "name": "Generating",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["analyze", "parse", "decode", "extract"]):
            states.append({
                "id": f"analyzing",
                "name": "Analyzing",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["explain", "describe", "format", "render"]):
            states.append({
                "id": f"explaining",
                "name": "Explaining",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["suggest", "recommend", "improve"]):
            states.append({
                "id": f"suggesting",
                "name": "Suggesting",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["register", "add", "update", "set"]):
            states.append({
                "id": f"registering",
                "name": "Registering",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["list", "show", "display", "print"]):
            states.append({
                "id": f"listing",
                "name": "Listing",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["compile", "transform", "convert"]):
            states.append({
                "id": f"compiling",
                "name": "Compiling",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["visualize", "graph", "draw", "plot"]):
            states.append({
                "id": f"visualizing",
                "name": "Visualizing",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["orchestrate", "dispatch", "schedule", "route"]):
            states.append({
                "id": f"orchestrating",
                "name": "Orchestrating",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["scrape", "crawl", "download"]):
            states.append({
                "id": f"scraping",
                "name": "Scraping",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        elif any(kw in name.lower() for kw in ["seal", "sign", "verify", "proof"]):
            states.append({
                "id": f"sealing",
                "name": "Sealing",
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })
        else:
            # Fallback: create a unique state for each unmatched public function
            state_id = name.lower().replace("_", "-")
            state_name = to_state_name(name)
            states.append({
                "id": state_id,
                "name": state_name,
                "description": f"From function: {name}",
                "inferred_from": f"function:{name}"
            })

    # Infer from control flow patterns
    patterns = controlFlow.get("patterns", {})
    if patterns.get("errorHandling", 0) > 0:
        if not any(s["id"] == "error" for s in states):
            states.append({
                "id": "error",
                "name": "Error",
                "description": "From try/except blocks",
                "inferred_from": "pattern:errorHandling"
            })

    # Infer from imports
    for imp in imports:
        cat = imp.get("semantic", {}).get("category")
        if cat == "http":
            if not any(s["id"] == "fetching" for s in states):
                states.append({
                    "id": "fetching",
                    "name": "Fetching",
                    "description": f"HTTP operations via {imp.get('module')}",
                    "inferred_from": f"import:{imp.get('module')}"
                })
        elif cat == "database":
            if not any(s["id"] == "querying" for s in states):
                states.append({
                    "id": "querying",
                    "name": "Querying",
                    "description": f"Database ops via {imp.get('module')}",
                    "inferred_from": f"import:{imp.get('module')}"
                })

    # Terminal state
    states.append({
        "id": "complete",
        "name": "Complete",
        "description": "Terminal state",
        "inferred_from": "exit_point"
    })

    # Deduplicate
    seen = set()
    unique = []
    for s in states:
        if s["id"] not in seen:
            seen.add(s["id"])
            unique.append(s)

    return {"states": unique}


def inferTransitions(params: dict) -> dict:
    """Infer transitions and guards from control flow."""
    controlFlow = params.get("controlFlow", {})
    states = params.get("inferredStates", [])
    functions = params.get("functions", [])

    transitions = []
    gates = []
    tId = 0
    gId = 0

    stateIds = [s["id"] for s in states]

    # Infer gates from control flow branches first
    nodes = controlFlow.get("nodes", [])
    gateConditions = []
    for node in nodes:
        if node.get("type") == "branch":
            label = node.get("label", "")
            if label.startswith("if "):
                cond = label[3:]
                gateId = f"g{gId}"
                gates.append({
                    "id": gateId,
                    "type": "expression",
                    "expression": cond,
                    "inferred_from": f"line:{node.get('line')}"
                })
                gateConditions.append(gateId)
                gId += 1

    # Build transitions from state pairs with optional gate associations
    gateIdx = 0
    for i, state in enumerate(states[:-1]):
        nextState = states[i + 1] if i + 1 < len(states) else None
        if nextState:
            event = f"{state['id'].upper()}_DONE"
            trans = {
                "id": f"t{tId}",
                "from": state["id"],
                "to": nextState["id"],
                "on_event": event,
                "inferred_from": "state_sequence"
            }
            # Associate a gate with validation/check transitions
            if any(kw in state["id"] for kw in ["validat", "check", "verify"]):
                if gateIdx < len(gateConditions):
                    trans["gates"] = [gateConditions[gateIdx]]
                    gateIdx += 1
            transitions.append(trans)
            tId += 1

    # Add error transition if error state exists
    if "error" in stateIds:
        # Add hasError gate
        errorGateId = f"g{gId}"
        gates.append({
            "id": errorGateId,
            "type": "expression",
            "expression": "error is not None",
            "inferred_from": "error_pattern"
        })
        gId += 1

        for state in states:
            if state["id"] not in ("error", "complete"):
                transitions.append({
                    "id": f"t{tId}",
                    "from": state["id"],
                    "to": "error",
                    "on_event": "ERROR",
                    "gates": [errorGateId],
                    "inferred_from": "error_pattern"
                })
                tId += 1

    # Reset transition
    transitions.append({
        "id": f"t{tId}",
        "from": "*",
        "to": "idle",
        "on_event": "RESET",
        "inferred_from": "convention"
    })

    return {"transitions": transitions, "gates": gates}


def inferActions(params: dict) -> dict:
    """Infer actions from function calls and side effects."""
    functions = params.get("functions", [])
    imports = params.get("imports", [])
    controlFlow = params.get("controlFlow", {})

    actions = []
    aId = 0

    importSemantics = {i.get("module", "").split(".")[0]: i.get("semantic", {})
                       for i in imports if i.get("module")}

    for fn in functions:
        name = fn.get("name", "")
        if name.startswith("_"):
            continue

        effects = fn.get("sideEffects", [])
        for effect in effects:
            if effect.get("type") == "call":
                callName = effect.get("name", "")
                root = callName.split(".")[0]
                semantic = importSemantics.get(root, {})
                cat = semantic.get("category", "compute")

                actionType = "compute"
                if cat == "observability":
                    actionType = "emit"
                elif cat in ("filesystem", "database"):
                    actionType = "compute"

                actions.append({
                    "id": f"a{aId}",
                    "name": f"call_{callName.replace('.', '_')}",
                    "type": actionType,
                    "compute_unit": f"impl:{callName}",
                    "inferred_from": f"function:{name}",
                    "line": effect.get("line")
                })
                aId += 1

    # Deduplicate by name
    seen = set()
    unique = []
    for a in actions:
        if a["name"] not in seen:
            seen.add(a["name"])
            unique.append(a)

    return {"actions": unique[:20]}  # Limit to 20 actions


def generateBlueprint(params: dict) -> dict:
    """Assemble final L++ blueprint."""
    filePath = params.get("filePath", "decoded")
    states = params.get("inferredStates", [])
    transitions = params.get("inferredTransitions", [])
    gates = params.get("inferredGates", [])
    actions = params.get("inferredActions", [])
    imports = params.get("imports", [])

    baseName = os.path.basename(filePath).replace(".py", "") if filePath else \
        "decoded"

    # Build context schema from function args
    contextProps = {}
    for imp in imports:
        cat = imp.get("semantic", {}).get("category")
        if cat == "http":
            contextProps["response"] = {"type": "object"}
        elif cat == "database":
            contextProps["queryResult"] = {"type": "array"}
    contextProps["error"] = {"type": "string"}
    contextProps["result"] = {"type": "object"}

    # Build states dict
    statesDict = {}
    for s in states:
        statesDict[s["id"]] = {
            "name": s.get("name", s["id"]),
            "description": s.get("description", "")
        }

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
        actionsDict[a["id"]] = {
            "type": a.get("type", "compute"),
            "compute_unit": a.get("compute_unit", ""),
            "description": f"Inferred from {a.get('inferred_from', 'code')}"
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
        # Include gates if present
        if t.get("gates"):
            trans["gates"] = t["gates"]
        transArr.append(trans)

    blueprint = {
        "$schema": "lpp/v0.1",
        "id": f"decoded_{baseName}",
        "name": f"Decoded: {baseName}",
        "version": "1.0.0",
        "description": f"Auto-decoded from {filePath}",
        "context_schema": {"properties": contextProps},
        "states": statesDict,
        "transitions": transArr,
        "gates": gatesDict,
        "actions": actionsDict,
        "entry_state": states[0]["id"] if states else "idle",
        "terminal_states": ["complete", "error"]
    }

    report = {
        "source": filePath,
        "statesCount": len(states),
        "transitionsCount": len(transitions),
        "gatesCount": len(gates),
        "actionsCount": len(actions),
        "importsAnalyzed": len(imports),
        "importCategories": list(set(i.get("semantic", {}).get("category")
                                     for i in imports))
    }

    return {
        "blueprint": blueprint,
        "json": json.dumps(blueprint, indent=2),
        "report": report
    }


def clearState(params: dict) -> dict:
    """Reset all analysis state."""
    return {
        "ast": None,
        "imports": None,
        "functions": None,
        "classes": None,
        "controlFlow": None,
        "inferredStates": None,
        "inferredTransitions": None,
        "inferredActions": None,
        "inferredGates": None,
        "blueprint": None,
        "blueprintJson": None,
        "analysisReport": None,
        "error": None
    }


COMPUTE_REGISTRY = {
    "decoder:hasValue": hasValue,
    "decoder:loadFile": loadFile,
    "decoder:parseAst": parseAst,
    "decoder:analyzeImports": analyzeImports,
    "decoder:analyzeFunctions": analyzeFunctions,
    "decoder:analyzeControlFlow": analyzeControlFlow,
    "decoder:inferStates": inferStates,
    "decoder:inferTransitions": inferTransitions,
    "decoder:inferActions": inferActions,
    "decoder:generateBlueprint": generateBlueprint,
    "decoder:clearState": clearState,
}
