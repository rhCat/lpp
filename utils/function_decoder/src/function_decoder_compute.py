"""
Function Decoder Compute Module
Analyzes Python scripts to extract inbound/outbound function interfaces
and build modular dependency graphs for cross-script linking.
"""
import ast
import os
from collections import defaultdict
from pathlib import Path

# Standard library modules for classification
STDLIB_MODULES = {
    "abc", "aifc", "argparse", "array", "ast", "asynchat", "asyncio",
    "asyncore", "atexit", "audioop", "base64", "bdb", "binascii", "binhex",
    "bisect", "builtins", "bz2", "calendar", "cgi", "cgitb", "chunk", "cmath",
    "cmd", "code", "codecs", "codeop", "collections", "colorsys", "compileall",
    "concurrent", "configparser", "contextlib", "contextvars", "copy",
    "copyreg", "cProfile", "crypt", "csv", "ctypes", "curses", "dataclasses",
    "datetime", "dbm", "decimal", "difflib", "dis", "distutils", "doctest",
    "email", "encodings", "enum", "errno", "faulthandler", "fcntl", "filecmp",
    "fileinput", "fnmatch", "fractions", "ftplib", "functools", "gc", "getopt",
    "getpass", "gettext", "glob", "graphlib", "grp", "gzip", "hashlib",
    "heapq", "hmac", "html", "http", "idlelib", "imaplib", "imghdr", "imp",
    "importlib", "inspect", "io", "ipaddress", "itertools", "json", "keyword",
    "lib2to3", "linecache", "locale", "logging", "lzma", "mailbox", "mailcap",
    "marshal", "math", "mimetypes", "mmap", "modulefinder", "multiprocessing",
    "netrc", "nis", "nntplib", "numbers", "operator", "optparse", "os",
    "ossaudiodev", "pathlib", "pdb", "pickle", "pickletools", "pipes",
    "pkgutil", "platform", "plistlib", "poplib", "posix", "posixpath", "pprint",
    "profile", "pstats", "pty", "pwd", "py_compile", "pyclbr", "pydoc", "queue",
    "quopri", "random", "re", "readline", "reprlib", "resource", "rlcompleter",
    "runpy", "sched", "secrets", "select", "selectors", "shelve", "shlex",
    "shutil", "signal", "site", "smtpd", "smtplib", "sndhdr", "socket",
    "socketserver", "spwd", "sqlite3", "ssl", "stat", "statistics", "string",
    "stringprep", "struct", "subprocess", "sunau", "symtable", "sys", "sysconfig",
    "syslog", "tabnanny", "tarfile", "telnetlib", "tempfile", "termios", "test",
    "textwrap", "threading", "time", "timeit", "tkinter", "token", "tokenize",
    "trace", "traceback", "tracemalloc", "tty", "turtle", "turtledemo", "types",
    "typing", "unicodedata", "unittest", "urllib", "uu", "uuid", "venv",
    "warnings", "wave", "weakref", "webbrowser", "winreg", "winsound", "wsgiref",
    "xdrlib", "xml", "xmlrpc", "zipapp", "zipfile", "zipimport", "zlib"
}


def loadFile(params: dict) -> dict:
    """Load Python file from disk."""
    filePath = params.get("filePath", "")
    if not filePath:
        return {"sourceCode": None, "error": "No file path provided"}
    try:
        with open(filePath, "r", encoding="utf-8") as f:
            return {"sourceCode": f.read(), "error": None}
    except Exception as e:
        return {"sourceCode": None, "error": str(e)}


def parseAst(params: dict) -> dict:
    """Parse source code into AST."""
    sourceCode = params.get("sourceCode")
    if not sourceCode:
        return {"ast": None, "error": "No source code"}
    try:
        tree = ast.parse(sourceCode)
        return {"ast": tree, "error": None}
    except SyntaxError as e:
        return {"ast": None, "error": f"Syntax error: {e}"}


def extractExports(params: dict) -> dict:
    """Extract public functions and classes (inbound interface)."""
    tree = params.get("ast")
    filePath = params.get("filePath", "")
    sourceCode = params.get("sourceCode", "")
    if not tree:
        return {"exports": []}

    moduleName = Path(filePath).stem if filePath else "unknown"
    exports = []
    sourceLines = sourceCode.split('\n') if sourceCode else []

    def get_source(node):
        """Extract source code for a node using line numbers."""
        if not sourceLines or not hasattr(node, 'lineno'):
            return None
        start = node.lineno - 1
        end = getattr(node, 'end_lineno', start + 1)
        if start < len(sourceLines) and end <= len(sourceLines):
            return '\n'.join(sourceLines[start:end])
        return None

    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if not node.name.startswith("_"):
                exports.append({
                    "type": "function",
                    "name": node.name,
                    "module": moduleName,
                    "line": node.lineno,
                    "endLine": getattr(node, 'end_lineno', node.lineno),
                    "args": [a.arg for a in node.args.args],
                    "returns": _get_annotation(node.returns),
                    "docstring": ast.get_docstring(node),
                    "decorators": [_get_decorator_name(d) for d in node.decorator_list],
                    "source": get_source(node)
                })
        elif isinstance(node, ast.AsyncFunctionDef):
            if not node.name.startswith("_"):
                exports.append({
                    "type": "async_function",
                    "name": node.name,
                    "module": moduleName,
                    "line": node.lineno,
                    "endLine": getattr(node, 'end_lineno', node.lineno),
                    "args": [a.arg for a in node.args.args],
                    "returns": _get_annotation(node.returns),
                    "docstring": ast.get_docstring(node),
                    "decorators": [_get_decorator_name(d) for d in node.decorator_list],
                    "source": get_source(node)
                })
        elif isinstance(node, ast.ClassDef):
            if not node.name.startswith("_"):
                methods = []
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        if not item.name.startswith("_") or item.name in (
                            "__init__", "__call__", "__enter__", "__exit__"
                        ):
                            methods.append(item.name)
                exports.append({
                    "type": "class",
                    "name": node.name,
                    "module": moduleName,
                    "line": node.lineno,
                    "endLine": getattr(node, 'end_lineno', node.lineno),
                    "bases": [_get_name(b) for b in node.bases],
                    "methods": methods,
                    "docstring": ast.get_docstring(node),
                    "source": get_source(node)
                })

    # Check for module-level __all__
    for node in ast.iter_child_nodes(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name) and target.id == "__all__":
                    if isinstance(node.value, (ast.List, ast.Tuple)):
                        explicit = [
                            elt.value for elt in node.value.elts
                            if isinstance(elt, ast.Constant)
                        ]
                        # Filter exports to only __all__ members
                        exports = [e for e in exports if e["name"] in explicit]
                        break

    return {"exports": exports}


def extractImports(params: dict) -> dict:
    """Extract import statements with aliases and classify them."""
    tree = params.get("ast")
    if not tree:
        return {"imports": []}

    imports = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                mod = alias.name.split(".")[0]
                imports.append({
                    "type": "import",
                    "module": alias.name,
                    "alias": alias.asname or alias.name,
                    "line": node.lineno,
                    "category": _classify_module(mod),
                    "names": []
                })
        elif isinstance(node, ast.ImportFrom):
            mod = node.module or ""
            baseMod = mod.split(".")[0] if mod else ""
            isRelative = node.level > 0
            imports.append({
                "type": "from_import",
                "module": mod,
                "level": node.level,
                "alias": None,
                "line": node.lineno,
                "category": "local" if isRelative else _classify_module(baseMod),
                "names": [
                    {"name": a.name, "alias": a.asname or a.name}
                    for a in node.names
                ]
            })

    return {"imports": imports}


def traceInternalCalls(params: dict) -> dict:
    """Trace function-to-function calls within the script."""
    tree = params.get("ast")
    exports = params.get("exports", [])
    if not tree:
        return {"internalCalls": []}

    exportNames = {e["name"] for e in exports}
    calls = []

    class CallVisitor(ast.NodeVisitor):
        def __init__(self):
            self.currentFunc = None

        def visit_FunctionDef(self, node):
            prevFunc = self.currentFunc
            self.currentFunc = node.name
            self.generic_visit(node)
            self.currentFunc = prevFunc

        def visit_AsyncFunctionDef(self, node):
            prevFunc = self.currentFunc
            self.currentFunc = node.name
            self.generic_visit(node)
            self.currentFunc = prevFunc

        def visit_Call(self, node):
            if self.currentFunc:
                callee = _get_call_name(node)
                if callee and callee in exportNames:
                    calls.append({
                        "from": self.currentFunc,
                        "to": callee,
                        "line": node.lineno,
                        "type": "internal"
                    })
            self.generic_visit(node)

    CallVisitor().visit(tree)
    return {"internalCalls": calls}


def traceExternalCalls(params: dict) -> dict:
    """Trace calls to imported modules, separating external and local."""
    tree = params.get("ast")
    imports = params.get("imports", [])
    if not tree:
        return {"externalCalls": [], "localCalls": []}

    # Build alias -> (module, category) mapping
    aliasMap = {}
    for imp in imports:
        if imp["type"] == "import":
            aliasMap[imp["alias"]] = (imp["module"], imp["category"])
        elif imp["type"] == "from_import":
            for n in imp["names"]:
                aliasMap[n["alias"]] = (
                    f"{imp['module']}.{n['name']}" if imp["module"] else n["name"],
                    imp["category"]
                )

    externalCalls = []
    localCalls = []

    class ExternalCallVisitor(ast.NodeVisitor):
        def __init__(self):
            self.currentFunc = None

        def visit_FunctionDef(self, node):
            prevFunc = self.currentFunc
            self.currentFunc = node.name
            self.generic_visit(node)
            self.currentFunc = prevFunc

        def visit_AsyncFunctionDef(self, node):
            prevFunc = self.currentFunc
            self.currentFunc = node.name
            self.generic_visit(node)
            self.currentFunc = prevFunc

        def visit_Call(self, node):
            caller = self.currentFunc or "<module>"
            # Handle attribute calls like requests.get()
            if isinstance(node.func, ast.Attribute):
                parts = []
                n = node.func
                while isinstance(n, ast.Attribute):
                    parts.append(n.attr)
                    n = n.value
                if isinstance(n, ast.Name):
                    parts.append(n.id)
                parts.reverse()
                root = parts[0] if parts else None
                if root and root in aliasMap:
                    mod, cat = aliasMap[root]
                    fullCall = ".".join(parts)
                    entry = {
                        "from": caller,
                        "to": fullCall,
                        "module": mod,
                        "line": node.lineno
                    }
                    if cat == "local":
                        localCalls.append(entry)
                    else:
                        entry["category"] = cat
                        externalCalls.append(entry)
            # Handle direct calls like json_loads()
            elif isinstance(node.func, ast.Name):
                name = node.func.id
                if name in aliasMap:
                    mod, cat = aliasMap[name]
                    entry = {
                        "from": caller,
                        "to": name,
                        "module": mod,
                        "line": node.lineno
                    }
                    if cat == "local":
                        localCalls.append(entry)
                    else:
                        entry["category"] = cat
                        externalCalls.append(entry)
            self.generic_visit(node)

    ExternalCallVisitor().visit(tree)
    return {"externalCalls": externalCalls, "localCalls": localCalls}


def computeCoupling(params: dict) -> dict:
    """Compute coupling metrics: fan-in, fan-out, afferent/efferent."""
    exports = params.get("exports", [])
    imports = params.get("imports", [])
    internalCalls = params.get("internalCalls", [])
    externalCalls = params.get("externalCalls", [])
    localCalls = params.get("localCalls", [])

    # Fan-out: number of external dependencies
    fanOut = len(set(imp["module"]
                 for imp in imports if imp["category"] != "local"))

    # Fan-in: number of exports (potential inbound callers)
    fanIn = len(exports)

    # Internal complexity: number of internal call edges
    internalEdges = len(internalCalls)

    # External call count by category
    callsByCategory = defaultdict(int)
    for call in externalCalls:
        callsByCategory[call.get("category", "unknown")] += 1

    # Local coupling: connections to other local scripts
    localDeps = set()
    for call in localCalls:
        localDeps.add(call["module"].split(".")[0])
    for imp in imports:
        if imp["category"] == "local":
            localDeps.add(imp["module"].split(".")[0] if imp["module"] else "")

    # Instability: I = Ce / (Ca + Ce) where Ce = fan-out, Ca = fan-in
    instability = fanOut / (fanIn + fanOut) if (fanIn + fanOut) > 0 else 0

    return {
        "coupling": {
            "fanIn": fanIn,
            "fanOut": fanOut,
            "instability": round(instability, 3),
            "internalEdges": internalEdges,
            "externalCallCount": len(externalCalls),
            "localCallCount": len(localCalls),
            "callsByCategory": dict(callsByCategory),
            "localDependencies": list(localDeps)
        }
    }


def generateModuleGraph(params: dict) -> dict:
    """Generate final linkable module graph JSON."""
    filePath = params.get("filePath", "")
    exports = params.get("exports", [])
    imports = params.get("imports", [])
    internalCalls = params.get("internalCalls", [])
    externalCalls = params.get("externalCalls", [])
    localCalls = params.get("localCalls", [])
    coupling = params.get("coupling", {})

    moduleName = Path(filePath).stem if filePath else "unknown"

    # Build nodes
    nodes = []

    # Module node (central)
    nodes.append({
        "id": moduleName,
        "type": "module",
        "label": moduleName,
        "metrics": coupling
    })

    # Export nodes (inbound interface)
    for exp in exports:
        nodes.append({
            "id": f"{moduleName}.{exp['name']}",
            "type": exp["type"],
            "label": exp["name"],
            "direction": "inbound",
            "parent": moduleName,
            "line": exp.get("line"),
            "endLine": exp.get("endLine"),
            "signature": _build_signature(exp),
            "docstring": exp.get("docstring"),
            "source": exp.get("source"),
            "args": exp.get("args"),
            "returns": exp.get("returns")
        })

    # Import nodes (outbound dependencies)
    seenMods = set()
    for imp in imports:
        mod = imp["module"] or f"relative.level{imp.get('level', 1)}"
        if mod not in seenMods:
            seenMods.add(mod)
            nodes.append({
                "id": mod,
                "type": "dependency",
                "label": mod.split(".")[-1],
                "direction": "outbound",
                "category": imp["category"]
            })

    # Build edges
    edges = []

    # Internal call edges
    for call in internalCalls:
        edges.append({
            "from": f"{moduleName}.{call['from']}",
            "to": f"{moduleName}.{call['to']}",
            "type": "internal",
            "line": call.get("line")
        })

    # External call edges
    for call in externalCalls:
        mod = call["module"].split(".")[0]
        edges.append({
            "from": f"{moduleName}.{call['from']}" if call["from"] != "<module>" else moduleName,
            "to": mod,
            "type": "external",
            "category": call.get("category"),
            "line": call.get("line")
        })

    # Local call edges (to other scripts)
    for call in localCalls:
        mod = call["module"].split(".")[0]
        edges.append({
            "from": f"{moduleName}.{call['from']}" if call["from"] != "<module>" else moduleName,
            "to": mod,
            "type": "local",
            "line": call.get("line")
        })

    return {
        "moduleGraph": {
            "module": moduleName,
            "filePath": filePath,
            "inbound": [e for e in exports],
            "outbound": [
                {"module": imp["module"],
                    "category": imp["category"], "names": imp["names"]}
                for imp in imports
            ],
            "nodes": nodes,
            "edges": edges,
            "coupling": coupling
        }
    }


# --- Helper Functions ---

def _get_annotation(node) -> str:
    """Extract type annotation as string."""
    if node is None:
        return None
    if isinstance(node, ast.Constant):
        return str(node.value)
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Subscript):
        return f"{_get_name(node.value)}[{_get_name(node.slice)}]"
    return ast.dump(node)


def _get_name(node) -> str:
    """Extract name from various AST nodes."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return f"{_get_name(node.value)}.{node.attr}"
    if isinstance(node, ast.Constant):
        return str(node.value)
    if isinstance(node, ast.Subscript):
        return f"{_get_name(node.value)}[{_get_name(node.slice)}]"
    return ""


def _get_decorator_name(node) -> str:
    """Extract decorator name."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return f"{_get_name(node.value)}.{node.attr}"
    if isinstance(node, ast.Call):
        return _get_decorator_name(node.func)
    return ""


def _get_call_name(node) -> str:
    """Extract the function name from a Call node."""
    if isinstance(node.func, ast.Name):
        return node.func.id
    if isinstance(node.func, ast.Attribute):
        return node.func.attr
    return None


def _classify_module(mod: str) -> str:
    """Classify module as stdlib, pip, or local."""
    if not mod:
        return "local"
    if mod in STDLIB_MODULES:
        return "stdlib"
    return "pip"


def _build_signature(exp: dict) -> str:
    """Build function signature string."""
    if exp["type"] in ("function", "async_function"):
        args = ", ".join(exp.get("args", []))
        ret = exp.get("returns")
        sig = f"({args})"
        if ret:
            sig += f" -> {ret}"
        return sig
    return None


def visualizeModuleGraph(params: dict) -> dict:
    """Generate stackable HTML visualization for module graph(s).

    Args:
        params: dict with 'moduleGraphs' (list of moduleGraph dicts or single),
                'outputPath' (HTML file path), 'title' (optional)

    Returns:
        dict with 'htmlPath', 'error'
    """
    import json as json_mod

    graphs = params.get("moduleGraphs", [])
    if not isinstance(graphs, list):
        graphs = [graphs]

    outputPath = params.get("outputPath", "function_graph.html")
    title = params.get("title", "Function Module Graph")

    if not graphs:
        return {"htmlPath": None, "error": "No module graphs provided"}

    # Merge all graphs into combined nodes/edges
    all_nodes = []
    all_edges = []
    module_colors = {}
    color_palette = [
        "#00d4ff", "#ff6b6b", "#4ecdc4", "#f39c12", "#9b59b6",
        "#1abc9c", "#e74c3c", "#3498db", "#2ecc71", "#e67e22"
    ]

    for idx, graph in enumerate(graphs):
        if not graph:
            continue
        mod_name = graph.get("module", f"module_{idx}")
        module_colors[mod_name] = color_palette[idx % len(color_palette)]

        for node in graph.get("nodes", []):
            node_copy = dict(node)
            node_copy["moduleColor"] = module_colors[mod_name]
            node_copy["moduleName"] = mod_name
            all_nodes.append(node_copy)

        for edge in graph.get("edges", []):
            all_edges.append(edge)

    # Deduplicate dependency nodes
    seen_deps = set()
    deduped_nodes = []
    for node in all_nodes:
        if node.get("type") == "dependency":
            if node["id"] not in seen_deps:
                seen_deps.add(node["id"])
                deduped_nodes.append(node)
        else:
            deduped_nodes.append(node)

    html = _build_function_html(title, deduped_nodes, all_edges, module_colors)

    try:
        with open(outputPath, "w", encoding="utf-8") as f:
            f.write(html)
        return {"htmlPath": outputPath, "error": None}
    except Exception as e:
        return {"htmlPath": None, "error": str(e)}


def _build_function_html(title: str, nodes: list, edges: list, module_colors: dict) -> str:
    """Build stackable D3.js HTML for function visualization."""
    import json as json_mod

    nodes_json = json_mod.dumps(nodes)
    edges_json = json_mod.dumps(edges)
    colors_json = json_mod.dumps(module_colors)

    return f'''<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8"/>
<title>{title}</title>
<script src="https://d3js.org/d3.v7.min.js"></script>
<style>
body {{ font-family: 'Segoe UI', Arial, sans-serif; margin: 0; padding: 20px; background: #0f0f23; color: #eee; }}
h1 {{ color: #00d4ff; margin-bottom: 5px; font-size: 24px; }}
.subtitle {{ color: #888; margin-bottom: 15px; font-size: 14px; }}
#container {{ display: flex; gap: 20px; height: calc(100vh - 120px); }}
#graph {{ flex: 1; position: relative; }}
#sidebar {{ width: 350px; background: #1a1a2e; padding: 15px; border-radius: 8px; overflow-y: auto; }}
svg {{ background: #16213e; border-radius: 8px; width: 100%; height: 100%; }}

/* Node styles */
.node {{ cursor: pointer; }}
.node-module {{ fill: #2a2a4a; stroke-width: 3; }}
.node-function {{ fill: #3a3a5a; stroke-width: 2; }}
.node-dependency {{ fill: #1a1a3a; stroke: #666; stroke-width: 1; stroke-dasharray: 4; }}
.node-label {{ font-size: 11px; fill: #fff; pointer-events: none; font-weight: 500; }}
.node-sublabel {{ font-size: 9px; fill: #888; pointer-events: none; }}

/* Edge styles */
.edge {{ fill: none; stroke-opacity: 0.6; }}
.edge-internal {{ stroke: #4ecdc4; stroke-width: 2; }}
.edge-external {{ stroke: #f39c12; stroke-width: 1.5; stroke-dasharray: 4; }}
.edge-local {{ stroke: #9b59b6; stroke-width: 2; }}
.edge-label {{ font-size: 8px; fill: #666; pointer-events: none; }}

/* Highlight styles */
.highlight {{ stroke-width: 3 !important; stroke-opacity: 1 !important; }}
.dim {{ opacity: 0.2; }}

/* Controls */
.controls {{ display: flex; gap: 8px; margin-bottom: 10px; flex-wrap: wrap; }}
.controls button {{ background: #3a3a5a; color: #fff; border: 1px solid #555; padding: 6px 12px; border-radius: 4px; cursor: pointer; font-size: 12px; }}
.controls button:hover {{ background: #4a4a6a; }}
.controls button.active {{ background: #00d4ff; color: #000; border-color: #00d4ff; }}

/* Module legend */
.module-legend {{ margin-top: 15px; }}
.module-item {{ display: flex; align-items: center; gap: 8px; padding: 5px 0; cursor: pointer; }}
.module-item:hover {{ background: #2a2a4a; }}
.module-dot {{ width: 12px; height: 12px; border-radius: 3px; }}
.module-name {{ font-size: 12px; }}

/* Info panel */
h3 {{ color: #00d4ff; margin: 15px 0 8px 0; font-size: 14px; border-bottom: 1px solid #333; padding-bottom: 5px; }}
.info-section {{ font-size: 12px; line-height: 1.6; }}
.info-label {{ color: #888; }}
.info-value {{ color: #fff; }}

/* Source code panel */
.source-panel {{ margin-top: 10px; }}
.source-code {{ background: #0d0d1a; border: 1px solid #333; border-radius: 4px; padding: 10px; font-family: 'Consolas', 'Monaco', monospace; font-size: 11px; line-height: 1.4; overflow-x: auto; max-height: 300px; overflow-y: auto; white-space: pre; color: #b8b8b8; }}
.source-header {{ display: flex; justify-content: space-between; align-items: center; margin-bottom: 5px; }}
.source-toggle {{ background: #3a3a5a; color: #fff; border: none; padding: 4px 8px; border-radius: 3px; cursor: pointer; font-size: 10px; }}
.source-toggle:hover {{ background: #4a4a6a; }}
.docstring {{ color: #6a9955; font-style: italic; }}
.metric {{ display: flex; justify-content: space-between; padding: 3px 0; }}
.metric-bar {{ height: 4px; background: #333; border-radius: 2px; margin-top: 2px; }}
.metric-fill {{ height: 100%; border-radius: 2px; }}

/* Edge list */
.edge-list {{ max-height: 200px; overflow-y: auto; }}
.edge-item {{ padding: 4px 0; border-bottom: 1px solid #333; font-size: 11px; }}
.edge-item .from {{ color: #4ecdc4; }}
.edge-item .to {{ color: #f39c12; }}
.edge-item .type {{ color: #666; font-size: 10px; }}

/* Tooltip */
#tooltip {{ position: absolute; background: #1a1a2e; border: 1px solid #00d4ff; padding: 10px; border-radius: 4px; pointer-events: none; display: none; max-width: 300px; z-index: 100; font-size: 11px; }}
</style>
</head>
<body>
<h1>{title}</h1>
<div class="subtitle">Stackable function dependency visualization • Drag nodes to rearrange • Click to inspect</div>

<div class="controls">
  <button onclick="resetView()">Reset View</button>
  <button onclick="fitToView()">Fit</button>
  <button onclick="toggleLayout('force')" id="btn-force" class="active">Force</button>
  <button onclick="toggleLayout('horizontal')" id="btn-horizontal">Horizontal</button>
  <button onclick="toggleLayout('vertical')" id="btn-vertical">Vertical</button>
  <span style="margin-left: 10px; color: #666">|</span>
  <button onclick="toggleEdgeType('internal')" id="btn-internal" class="active">Internal</button>
  <button onclick="toggleEdgeType('external')" id="btn-external" class="active">External</button>
  <button onclick="toggleEdgeType('local')" id="btn-local" class="active">Local</button>
</div>

<div id="container">
  <div id="graph"><svg></svg></div>
  <div id="sidebar">
    <h3>Modules</h3>
    <div class="module-legend" id="module-legend"></div>

    <h3>Selected Node</h3>
    <div class="info-section" id="node-info">Click a node to see details</div>

    <h3>Source Code</h3>
    <div class="source-panel" id="source-panel">
      <div id="source-content" style="color:#666;font-size:11px">Click a function to view source</div>
    </div>

    <h3>Connections</h3>
    <div class="edge-list" id="edge-list"></div>
  </div>
</div>
<div id="tooltip"></div>

<script>
const nodes = {nodes_json};
const edges = {edges_json};
const moduleColors = {colors_json};

// Edge type visibility
const edgeVisibility = {{ internal: true, external: true, local: true }};
let currentLayout = 'force';

// Create node lookup
const nodeById = {{}};
nodes.forEach(n => nodeById[n.id] = n);

// Setup SVG
const container = document.getElementById('graph');
const width = container.clientWidth;
const height = container.clientHeight || 600;

const svg = d3.select("svg").attr("viewBox", [0, 0, width, height]);
const g = svg.append("g");

// Zoom behavior
const zoom = d3.zoom()
    .scaleExtent([0.1, 4])
    .filter(e => !e.target.closest('.node'))
    .on("zoom", e => g.attr("transform", e.transform));
svg.call(zoom);

// Arrow markers
const defs = svg.append("defs");
["internal", "external", "local"].forEach(type => {{
    const color = type === "internal" ? "#4ecdc4" : type === "external" ? "#f39c12" : "#9b59b6";
    defs.append("marker")
        .attr("id", `arrow-${{type}}`)
        .attr("viewBox", "0 -5 10 10")
        .attr("refX", 20)
        .attr("refY", 0)
        .attr("markerWidth", 6)
        .attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M0,-4L10,0L0,4")
        .attr("fill", color);
}});

// Build module legend
const legendDiv = document.getElementById('module-legend');
Object.entries(moduleColors).forEach(([mod, color]) => {{
    const item = document.createElement('div');
    item.className = 'module-item';
    item.innerHTML = `<div class="module-dot" style="background:${{color}}"></div><span class="module-name">${{mod}}</span>`;
    item.onclick = () => highlightModule(mod);
    legendDiv.appendChild(item);
}});

// Process edges - resolve node references
const processedEdges = edges.map(e => ({{
    ...e,
    source: nodeById[e.from] || {{ id: e.from, x: 0, y: 0 }},
    target: nodeById[e.to] || {{ id: e.to, x: 0, y: 0 }}
}})).filter(e => e.source && e.target);

// Force simulation
const simulation = d3.forceSimulation(nodes)
    .force("link", d3.forceLink(processedEdges).id(d => d.id).distance(80).strength(0.5))
    .force("charge", d3.forceManyBody().strength(-300))
    .force("center", d3.forceCenter(width / 2, height / 2))
    .force("collision", d3.forceCollide().radius(40));

// Draw edges
const edge = g.append("g").selectAll("path")
    .data(processedEdges)
    .join("path")
    .attr("class", d => `edge edge-${{d.type || 'internal'}}`)
    .attr("marker-end", d => `url(#arrow-${{d.type || 'internal'}})`);

// Node size based on type
function nodeSize(d) {{
    if (d.type === 'module') return {{ w: 120, h: 40 }};
    if (d.type === 'function' || d.type === 'async_function') return {{ w: 100, h: 30 }};
    if (d.type === 'class') return {{ w: 110, h: 35 }};
    return {{ w: 80, h: 25 }};  // dependency
}}

// Draw nodes
const node = g.append("g").selectAll("g")
    .data(nodes)
    .join("g")
    .attr("class", "node")
    .call(d3.drag()
        .on("start", dragStart)
        .on("drag", dragging)
        .on("end", dragEnd));

node.append("rect")
    .attr("class", d => `node-${{d.type === 'dependency' ? 'dependency' : d.type === 'module' ? 'module' : 'function'}}`)
    .attr("width", d => nodeSize(d).w)
    .attr("height", d => nodeSize(d).h)
    .attr("x", d => -nodeSize(d).w / 2)
    .attr("y", d => -nodeSize(d).h / 2)
    .attr("rx", 6)
    .attr("stroke", d => d.moduleColor || "#666");

node.append("text")
    .attr("class", "node-label")
    .attr("text-anchor", "middle")
    .attr("dy", d => d.signature ? -3 : 4)
    .text(d => d.label || d.id);

node.filter(d => d.signature).append("text")
    .attr("class", "node-sublabel")
    .attr("text-anchor", "middle")
    .attr("dy", 10)
    .text(d => d.signature.length > 20 ? d.signature.slice(0, 18) + ".." : d.signature);

// Tooltip
const tooltip = d3.select("#tooltip");
node.on("mouseover", (e, d) => {{
    let html = `<b>${{d.label || d.id}}</b>`;
    if (d.type) html += `<br><span style="color:#888">${{d.type}}</span>`;
    if (d.signature) html += `<br><code>${{d.signature}}</code>`;
    if (d.direction) html += `<br>Direction: ${{d.direction}}`;
    tooltip.style("display", "block").html(html);
}})
.on("mousemove", e => {{
    tooltip.style("left", (e.pageX + 15) + "px").style("top", (e.pageY - 10) + "px");
}})
.on("mouseout", () => tooltip.style("display", "none"));

// Click to select
node.on("click", (e, d) => {{
    e.stopPropagation();
    selectNode(d);
}});

svg.on("click", () => clearSelection());

// Update positions
simulation.on("tick", () => {{
    edge.attr("d", d => {{
        if (!d.source || !d.target) return "";
        const dx = d.target.x - d.source.x;
        const dy = d.target.y - d.source.y;
        const dr = Math.sqrt(dx * dx + dy * dy) * 1.5;
        return `M${{d.source.x}},${{d.source.y}}A${{dr}},${{dr}} 0 0,1 ${{d.target.x}},${{d.target.y}}`;
    }});
    node.attr("transform", d => `translate(${{d.x}},${{d.y}})`);
}});

// Drag functions
function dragStart(e, d) {{
    if (!e.active) simulation.alphaTarget(0.3).restart();
    d.fx = d.x;
    d.fy = d.y;
}}
function dragging(e, d) {{
    d.fx = e.x;
    d.fy = e.y;
}}
function dragEnd(e, d) {{
    if (!e.active) simulation.alphaTarget(0);
    d.fx = null;
    d.fy = null;
}}

// Selection functions
let selectedNode = null;

function selectNode(d) {{
    selectedNode = d;
    
    // Highlight node
    node.classed("dim", n => n.id !== d.id && !isConnected(d, n));
    node.select("rect").attr("stroke-width", n => n.id === d.id ? 4 : 2);
    
    // Highlight edges
    edge.classed("dim", e => e.source.id !== d.id && e.target.id !== d.id);
    edge.classed("highlight", e => e.source.id === d.id || e.target.id === d.id);
    
    // Update info panel
    updateNodeInfo(d);
    updateEdgeList(d);
}}

function clearSelection() {{
    selectedNode = null;
    node.classed("dim", false);
    node.select("rect").attr("stroke-width", 2);
    edge.classed("dim", false).classed("highlight", false);
    document.getElementById('node-info').innerHTML = 'Click a node to see details';
    document.getElementById('edge-list').innerHTML = '';
}}

function isConnected(a, b) {{
    return processedEdges.some(e => 
        (e.source.id === a.id && e.target.id === b.id) ||
        (e.source.id === b.id && e.target.id === a.id)
    );
}}

function updateNodeInfo(d) {{
    let html = `<div class="metric"><span class="info-label">ID:</span><span class="info-value">${{d.id}}</span></div>`;
    html += `<div class="metric"><span class="info-label">Type:</span><span class="info-value">${{d.type}}</span></div>`;
    if (d.moduleName) html += `<div class="metric"><span class="info-label">Module:</span><span class="info-value">${{d.moduleName}}</span></div>`;
    if (d.line) html += `<div class="metric"><span class="info-label">Line:</span><span class="info-value">${{d.line}}${{d.endLine ? '-' + d.endLine : ''}}</span></div>`;
    if (d.signature) html += `<div class="metric"><span class="info-label">Signature:</span><span class="info-value" style="font-family:monospace">${{d.signature}}</span></div>`;
    if (d.direction) html += `<div class="metric"><span class="info-label">Direction:</span><span class="info-value">${{d.direction}}</span></div>`;
    if (d.category) html += `<div class="metric"><span class="info-label">Category:</span><span class="info-value">${{d.category}}</span></div>`;

    if (d.metrics) {{
        html += `<div style="margin-top:10px"><b>Coupling Metrics</b></div>`;
        html += `<div class="metric"><span class="info-label">Fan-In:</span><span class="info-value">${{d.metrics.fanIn}}</span></div>`;
        html += `<div class="metric"><span class="info-label">Fan-Out:</span><span class="info-value">${{d.metrics.fanOut}}</span></div>`;
        html += `<div class="metric"><span class="info-label">Instability:</span><span class="info-value">${{(d.metrics.instability * 100).toFixed(1)}}%</span></div>`;
        html += `<div class="metric-bar"><div class="metric-fill" style="width:${{d.metrics.instability * 100}}%;background:${{d.metrics.instability > 0.5 ? '#ff6b6b' : '#4ecdc4'}}"></div></div>`;
        html += `<div class="metric"><span class="info-label">Internal Edges:</span><span class="info-value">${{d.metrics.internalEdges}}</span></div>`;
    }}

    document.getElementById('node-info').innerHTML = html;

    // Update source code panel
    updateSourcePanel(d);
}}

function escapeHtml(str) {{
    if (!str) return '';
    return str.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}}

function updateSourcePanel(d) {{
    const panel = document.getElementById('source-content');

    if (d.source) {{
        let sourceHtml = '';
        if (d.docstring) {{
            sourceHtml += `<div class="docstring" style="margin-bottom:8px;padding:5px;background:#1a1a2a;border-radius:3px">${{escapeHtml(d.docstring)}}</div>`;
        }}
        sourceHtml += `<div class="source-code">${{escapeHtml(d.source)}}</div>`;
        panel.innerHTML = sourceHtml;
    }} else if (d.type === 'module') {{
        panel.innerHTML = `<div style="color:#888;font-size:11px">Module: ${{d.label}}<br>Click a function to view its source code.</div>`;
    }} else if (d.type === 'dependency') {{
        panel.innerHTML = `<div style="color:#888;font-size:11px">External dependency: ${{d.label}}<br>Category: ${{d.category || 'unknown'}}</div>`;
    }} else {{
        panel.innerHTML = `<div style="color:#666;font-size:11px">No source available for this node</div>`;
    }}
}}

function updateEdgeList(d) {{
    const outgoing = processedEdges.filter(e => e.source.id === d.id);
    const incoming = processedEdges.filter(e => e.target.id === d.id);
    
    let html = '';
    if (outgoing.length) {{
        html += '<div style="color:#4ecdc4;font-weight:bold;margin-bottom:5px">Outgoing →</div>';
        outgoing.forEach(e => {{
            html += `<div class="edge-item">→ <span class="to">${{e.target.id || e.to}}</span> <span class="type">[${{e.type}}]</span></div>`;
        }});
    }}
    if (incoming.length) {{
        html += '<div style="color:#f39c12;font-weight:bold;margin:10px 0 5px 0">← Incoming</div>';
        incoming.forEach(e => {{
            html += `<div class="edge-item">← <span class="from">${{e.source.id || e.from}}</span> <span class="type">[${{e.type}}]</span></div>`;
        }});
    }}
    if (!outgoing.length && !incoming.length) {{
        html = '<div style="color:#666">No connections</div>';
    }}
    
    document.getElementById('edge-list').innerHTML = html;
}}

function highlightModule(modName) {{
    node.classed("dim", n => n.moduleName !== modName && n.type !== 'dependency');
    edge.classed("dim", e => {{
        const srcMod = nodeById[e.source.id]?.moduleName;
        const tgtMod = nodeById[e.target.id]?.moduleName;
        return srcMod !== modName && tgtMod !== modName;
    }});
}}

// Layout functions
function toggleLayout(layout) {{
    currentLayout = layout;
    document.querySelectorAll('.controls button').forEach(b => {{
        if (b.id.startsWith('btn-') && ['force', 'horizontal', 'vertical'].includes(b.id.replace('btn-', ''))) {{
            b.classList.toggle('active', b.id === `btn-${{layout}}`);
        }}
    }});
    
    if (layout === 'force') {{
        simulation.alpha(1).restart();
    }} else {{
        simulation.stop();
        layoutNodes(layout);
    }}
}}

function layoutNodes(layout) {{
    const modules = [...new Set(nodes.filter(n => n.type === 'module').map(n => n.id))];
    const padding = 50;
    
    if (layout === 'horizontal') {{
        // Group by module, spread horizontally
        modules.forEach((mod, mi) => {{
            const modNodes = nodes.filter(n => n.moduleName === mod || n.id === mod);
            const x = padding + mi * (width - padding * 2) / Math.max(modules.length - 1, 1);
            modNodes.forEach((n, ni) => {{
                n.x = x;
                n.y = padding + ni * 50;
            }});
        }});
        // Dependencies on the right
        const deps = nodes.filter(n => n.type === 'dependency');
        deps.forEach((n, i) => {{
            n.x = width - padding;
            n.y = padding + i * 40;
        }});
    }} else if (layout === 'vertical') {{
        // Modules at top, functions below, dependencies at bottom
        const modNodes = nodes.filter(n => n.type === 'module');
        const funcNodes = nodes.filter(n => n.type === 'function' || n.type === 'async_function' || n.type === 'class');
        const depNodes = nodes.filter(n => n.type === 'dependency');
        
        modNodes.forEach((n, i) => {{
            n.x = padding + i * 150;
            n.y = padding;
        }});
        funcNodes.forEach((n, i) => {{
            n.x = padding + (i % 6) * 130;
            n.y = 120 + Math.floor(i / 6) * 60;
        }});
        depNodes.forEach((n, i) => {{
            n.x = padding + (i % 8) * 100;
            n.y = height - padding - 50;
        }});
    }}
    
    // Update positions
    node.transition().duration(500).attr("transform", d => `translate(${{d.x}},${{d.y}})`);
    edge.transition().duration(500).attr("d", d => {{
        if (!d.source || !d.target) return "";
        const dx = d.target.x - d.source.x;
        const dy = d.target.y - d.source.y;
        const dr = Math.sqrt(dx * dx + dy * dy) * 1.5;
        return `M${{d.source.x}},${{d.source.y}}A${{dr}},${{dr}} 0 0,1 ${{d.target.x}},${{d.target.y}}`;
    }});
}}

// Edge type toggle
function toggleEdgeType(type) {{
    edgeVisibility[type] = !edgeVisibility[type];
    document.getElementById(`btn-${{type}}`).classList.toggle('active', edgeVisibility[type]);
    edge.style("display", d => edgeVisibility[d.type || 'internal'] ? null : "none");
}}

// View controls
function resetView() {{
    svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity);
}}

function fitToView() {{
    const bounds = g.node().getBBox();
    const scale = Math.min(width / bounds.width, height / bounds.height) * 0.9;
    const tx = (width - bounds.width * scale) / 2 - bounds.x * scale;
    const ty = (height - bounds.height * scale) / 2 - bounds.y * scale;
    svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
}}

// Initial fit
setTimeout(fitToView, 1000);
</script>
</body>
</html>'''


# Compute registry for L++ dispatcher
COMPUTE_REGISTRY = {
    "funcdec:loadFile": loadFile,
    "funcdec:parseAst": parseAst,
    "funcdec:extractExports": extractExports,
    "funcdec:extractImports": extractImports,
    "funcdec:traceInternalCalls": traceInternalCalls,
    "funcdec:traceExternalCalls": traceExternalCalls,
    "funcdec:computeCoupling": computeCoupling,
    "funcdec:generateModuleGraph": generateModuleGraph,
    "funcdec:visualizeModuleGraph": visualizeModuleGraph
}
