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
        """Extract source code for a node using line numbers, including decorators."""
        if not sourceLines or not hasattr(node, 'lineno'):
            return None
        start = node.lineno - 1
        # Include decorator lines if present
        if hasattr(node, 'decorator_list') and node.decorator_list:
            first_decorator = node.decorator_list[0]
            if hasattr(first_decorator, 'lineno'):
                start = first_decorator.lineno - 1
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
                    "decorators": [_get_decorator_name(d) for d in node.decorator_list],
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
            "returns": exp.get("returns"),
            "decorators": exp.get("decorators")
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
    """Build collapsible D3.js HTML for function visualization."""
    import json as json_mod

    # Escape </script> in JSON to prevent HTML parsing issues
    def safe_json(data):
        return json_mod.dumps(data).replace('</script>', '<\\/script>').replace('</Script>', '<\\/Script>')

    nodes_json = safe_json(nodes)
    edges_json = safe_json(edges)
    colors_json = safe_json(module_colors)

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
#sidebar {{ width: 420px; background: #1a1a2e; padding: 15px; border-radius: 8px; overflow-y: auto; }}
svg {{ background: #16213e; border-radius: 8px; width: 100%; height: 100%; }}

/* Search box */
.search-box {{ margin-bottom: 10px; }}
.search-box input {{ width: 100%; padding: 8px 12px; background: #0d0d1a; border: 1px solid #333; border-radius: 4px; color: #fff; font-size: 12px; }}
.search-box input:focus {{ outline: none; border-color: #00d4ff; }}
.search-box input::placeholder {{ color: #666; }}

/* Node styles */
.node {{ cursor: pointer; }}
.node-module {{ fill: #2a2a4a; stroke-width: 3; }}
.node-function {{ fill: #3a3a5a; stroke-width: 2; }}
.node-dependency {{ fill: #2a2a4a; stroke: #f39c12; stroke-width: 2; stroke-dasharray: 5,3; }}
.node-collapsed {{ fill: #4a4a7a; stroke-width: 3; }}
.node-label {{ font-size: 13px; fill: #fff; pointer-events: none; font-weight: 500; }}
.node-sublabel {{ font-size: 10px; fill: #888; pointer-events: none; }}
.node-badge {{ font-size: 10px; fill: #fff; pointer-events: none; }}
.node-hidden {{ display: none; }}

/* Edge styles */
.edge {{ fill: none; stroke-opacity: 0.6; }}
.edge-internal {{ stroke: #4ecdc4; stroke-width: 2; }}
.edge-external {{ stroke: #f39c12; stroke-width: 1.5; stroke-dasharray: 4; }}
.edge-local {{ stroke: #9b59b6; stroke-width: 2; }}
.edge-label {{ font-size: 8px; fill: #666; pointer-events: none; }}
.edge-hidden {{ display: none; }}

/* Highlight styles */
.highlight {{ stroke-width: 3 !important; stroke-opacity: 1 !important; }}
.dim {{ opacity: 0.2; }}

/* Controls */
.controls {{ display: flex; gap: 8px; margin-bottom: 10px; flex-wrap: wrap; align-items: center; }}
.controls button {{ background: #3a3a5a; color: #fff; border: 1px solid #555; padding: 6px 12px; border-radius: 4px; cursor: pointer; font-size: 12px; }}
.controls button:hover {{ background: #4a4a6a; }}
.controls button.active {{ background: #00d4ff; color: #000; border-color: #00d4ff; }}
.controls .separator {{ color: #444; margin: 0 5px; }}

/* Category groups */
.category-group {{ margin-bottom: 8px; border: 1px solid #333; border-radius: 6px; overflow: hidden; }}
.category-header {{ display: flex; align-items: center; padding: 8px 10px; background: #252540; cursor: pointer; user-select: none; }}
.category-header:hover {{ background: #2a2a4a; }}
.category-toggle {{ margin-right: 8px; font-size: 11px; color: #888; transition: transform 0.2s; }}
.category-toggle.collapsed {{ transform: rotate(-90deg); }}
.category-name {{ font-size: 14px; font-weight: 600; color: #00d4ff; flex: 1; }}
.category-count {{ font-size: 11px; color: #666; background: #1a1a2e; padding: 2px 8px; border-radius: 10px; }}
.category-content {{ max-height: 500px; overflow: hidden; transition: max-height 0.3s ease; }}
.category-content.collapsed {{ max-height: 0; }}

/* Module items in sidebar */
.module-item {{ display: flex; align-items: center; gap: 8px; padding: 6px 10px; cursor: pointer; border-bottom: 1px solid #222; }}
.module-item:hover {{ background: #2a2a4a; }}
.module-item.hidden {{ display: none; }}
.module-dot {{ width: 10px; height: 10px; border-radius: 3px; flex-shrink: 0; }}
.module-name {{ font-size: 13px; flex: 1; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }}
.module-expand {{ font-size: 11px; color: #888; padding: 3px 8px; background: #1a1a2e; border-radius: 3px; cursor: pointer; }}
.module-expand:hover {{ background: #3a3a5a; color: #fff; }}
.module-expand.collapsed {{ color: #f39c12; }}
.module-metrics {{ font-size: 10px; color: #666; }}

/* Info panel */
h3 {{ color: #00d4ff; margin: 15px 0 8px 0; font-size: 15px; border-bottom: 1px solid #333; padding-bottom: 5px; }}
.info-section {{ font-size: 13px; line-height: 1.6; }}
.info-label {{ color: #888; }}
.info-value {{ color: #fff; }}

/* Source code panel */
.source-panel {{ margin-top: 10px; }}
.source-code {{ background: #0d0d1a; border: 1px solid #333; border-radius: 4px; padding: 10px; font-family: 'Consolas', 'Monaco', monospace; font-size: 11px; line-height: 1.4; overflow-x: auto; max-height: 250px; overflow-y: auto; white-space: pre; color: #b8b8b8; }}
.docstring {{ color: #6a9955; font-style: italic; }}
.metric {{ display: flex; justify-content: space-between; padding: 3px 0; }}
.metric-bar {{ height: 4px; background: #333; border-radius: 2px; margin-top: 2px; }}
.metric-fill {{ height: 100%; border-radius: 2px; }}

/* Edge list */
.edge-list {{ max-height: 150px; overflow-y: auto; }}
.edge-item {{ padding: 4px 0; border-bottom: 1px solid #333; font-size: 11px; }}
.edge-item .from {{ color: #4ecdc4; }}
.edge-item .to {{ color: #f39c12; }}
.edge-item .type {{ color: #666; font-size: 10px; }}

/* Tooltip */
#tooltip {{ position: absolute; background: #1a1a2e; border: 1px solid #00d4ff; padding: 10px; border-radius: 4px; pointer-events: none; display: none; max-width: 300px; z-index: 100; font-size: 11px; }}

/* Stats bar */
.stats-bar {{ display: flex; gap: 18px; padding: 10px 15px; background: #1a1a2e; border-radius: 4px; margin-bottom: 10px; font-size: 13px; }}
.stat {{ color: #888; }}
.stat span {{ color: #00d4ff; font-weight: 600; }}
</style>
</head>
<body>
<h1>{title}</h1>
<div class="subtitle">Collapsible function graph • Click module ▼ to collapse • Double-click to focus</div>

<div class="stats-bar">
  <div class="stat">Modules: <span id="stat-modules">0</span></div>
  <div class="stat">Functions: <span id="stat-functions">0</span></div>
  <div class="stat">Dependencies: <span id="stat-deps">0</span></div>
  <div class="stat">Edges: <span id="stat-edges">0</span></div>
  <div class="stat">Visible: <span id="stat-visible">0</span></div>
</div>

<div class="controls">
  <button onclick="collapseAll()">Collapse All</button>
  <button onclick="expandAll()">Expand All</button>
  <button onclick="resetView()">Reset</button>
  <button onclick="fitToView()">Fit</button>
  <span class="separator">|</span>
  <button onclick="toggleLayout('force')" id="btn-force" class="active">Force</button>
  <button onclick="toggleLayout('cluster')" id="btn-cluster">Cluster</button>
  <button onclick="toggleLayout('tree')" id="btn-tree">Tree</button>
  <span class="separator">|</span>
  <button onclick="toggleEdgeType('internal')" id="btn-internal" class="active">Internal</button>
  <button onclick="toggleEdgeType('external')" id="btn-external" class="active">External</button>
  <button onclick="toggleEdgeType('local')" id="btn-local" class="active">Local</button>
  <span class="separator">|</span>
  <button onclick="toggleTableView()" id="btn-table" style="background:#00d4ff;color:#000">📊 Table View</button>
</div>

<div id="container">
  <div id="graph"><svg></svg></div>
  <div id="sidebar">
    <div class="search-box">
      <input type="text" id="search-input" placeholder="Search modules, functions..." oninput="filterModules(this.value)">
      <div style="display:flex;gap:5px;margin-top:5px">
        <button onclick="selectSearchResults()" style="flex:1;font-size:10px;padding:4px 8px;background:#3a3a5a;border:1px solid #555;color:#fff;border-radius:3px;cursor:pointer">Select Matches</button>
        <button onclick="addSearchToSelection()" style="flex:1;font-size:10px;padding:4px 8px;background:#3a3a5a;border:1px solid #555;color:#fff;border-radius:3px;cursor:pointer">Add to Selection</button>
      </div>
    </div>

    <h3>Modules <span style="font-weight:normal;font-size:11px;color:#666" id="module-count"></span></h3>
    <div style="display:flex;gap:5px;margin-bottom:8px">
      <button onclick="foldAllCategories()" style="flex:1;font-size:10px;padding:4px 8px;background:#3a3a5a;border:1px solid #555;color:#fff;border-radius:3px;cursor:pointer">▶ Fold All</button>
      <button onclick="unfoldAllCategories()" style="flex:1;font-size:10px;padding:4px 8px;background:#3a3a5a;border:1px solid #555;color:#fff;border-radius:3px;cursor:pointer">▼ Unfold All</button>
    </div>
    <div id="module-legend"></div>

    <h3>Selected <span id="selection-count" style="font-weight:normal;color:#888">(0)</span> <button onclick="clearSelection()" style="float:right;font-size:10px;padding:2px 8px;background:#3a3a5a;border:1px solid #555;color:#fff;border-radius:3px;cursor:pointer">Clear</button></h3>
    <div style="font-size:11px;color:#666;margin-bottom:8px">Click to select • Ctrl+click for multi-select</div>
    <div class="info-section" id="node-info">Click a node to see details</div>

    <h3>Source Code</h3>
    <div class="source-panel" id="source-panel">
      <div id="source-content" style="color:#666;font-size:13px">Click a function to view source</div>
    </div>

    <h3>Connections <span id="connection-summary" style="font-weight:normal;color:#888"></span></h3>
    <div style="display:flex;gap:5px;margin-bottom:8px">
      <button onclick="selectAllIncoming()" style="flex:1;font-size:10px;padding:4px;background:#2a4a4a;border:1px solid #4ecdc4;color:#4ecdc4;border-radius:3px;cursor:pointer">+ Incoming</button>
      <button onclick="selectAllOutgoing()" style="flex:1;font-size:10px;padding:4px;background:#4a3a2a;border:1px solid #f39c12;color:#f39c12;border-radius:3px;cursor:pointer">+ Outgoing</button>
    </div>
    <div class="edge-list" id="edge-list"></div>
  </div>
</div>

<!-- Table View (hidden by default) -->
<div id="table-view" style="display:none;margin-top:20px">
  <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:10px">
    <h3 style="margin:0;color:#00d4ff">Module Analysis Table</h3>
    <button onclick="toggleTableView()" style="padding:6px 12px;background:#3a3a5a;color:#fff;border:1px solid #555;border-radius:4px;cursor:pointer">← Back to Graph</button>
  </div>
  <div style="margin-bottom:10px">
    <input type="text" id="table-search" placeholder="Filter modules..." oninput="filterTable(this.value)" style="width:300px;padding:8px;background:#1a1a2e;border:1px solid #333;border-radius:4px;color:#fff">
  </div>
  <div style="overflow-x:auto;max-height:calc(100vh - 200px);overflow-y:auto">
    <table id="metrics-table" style="width:100%;border-collapse:collapse;font-size:12px">
      <thead style="position:sticky;top:0;background:#1a1a2e">
        <tr style="border-bottom:2px solid #00d4ff">
          <th onclick="sortTable(0)" style="padding:10px;text-align:left;cursor:pointer;color:#00d4ff">Module ⇅</th>
          <th onclick="sortTable(1)" style="padding:10px;text-align:center;cursor:pointer;color:#4ecdc4">Funcs ⇅</th>
          <th onclick="sortTable(2)" style="padding:10px;text-align:center;cursor:pointer;color:#4ecdc4">Fan-In ⇅</th>
          <th onclick="sortTable(3)" style="padding:10px;text-align:center;cursor:pointer;color:#f39c12">Fan-Out ⇅</th>
          <th onclick="sortTable(4)" style="padding:10px;text-align:center;cursor:pointer;color:#ff6b6b">Instability ⇅</th>
          <th onclick="sortTable(5)" style="padding:10px;text-align:center;cursor:pointer;color:#f39c12">Direct Deps ⇅</th>
          <th onclick="sortTable(6)" style="padding:10px;text-align:center;cursor:pointer;color:#ff6b6b">Total Impact ⇅</th>
          <th onclick="sortTable(7)" style="padding:10px;text-align:center;cursor:pointer;color:#4ecdc4">Upstream ⇅</th>
        </tr>
      </thead>
      <tbody id="table-body"></tbody>
    </table>
  </div>
</div>

<div id="tooltip"></div>

<script>
const nodes = {nodes_json};
const edges = {edges_json};
const moduleColors = {colors_json};

// State management
const collapsedModules = new Set();
const edgeVisibility = {{ internal: true, external: true, local: true }};
let currentLayout = 'force';
let searchQuery = '';

// Create node lookup
const nodeById = {{}};
nodes.forEach(n => nodeById[n.id] = n);

// Group nodes by module
const moduleGroups = {{}};
nodes.forEach(n => {{
    const mod = n.moduleName || (n.type === 'module' ? n.id : 'dependencies');
    if (!moduleGroups[mod]) moduleGroups[mod] = [];
    moduleGroups[mod].push(n);
}});

// Group modules by category (folder path)
const categoryGroups = {{}};
Object.keys(moduleColors).forEach(mod => {{
    const parts = mod.split(/[_\\/]/);
    const category = parts.length > 1 ? parts[0] : 'root';
    if (!categoryGroups[category]) categoryGroups[category] = [];
    categoryGroups[category].push(mod);
}});

// Build dependency graph for transitive impact analysis
const dependsOn = {{}};  // module -> Set of modules it depends on
const dependedBy = {{}};  // module -> Set of modules that depend on it
edges.forEach(e => {{
    const fromMod = e.from.split('.')[0];
    const toMod = e.to.split('.')[0];
    if (fromMod !== toMod) {{
        if (!dependsOn[fromMod]) dependsOn[fromMod] = new Set();
        if (!dependedBy[toMod]) dependedBy[toMod] = new Set();
        dependsOn[fromMod].add(toMod);
        dependedBy[toMod].add(fromMod);
    }}
}});

// Compute transitive closure (all downstream modules affected by changes)
function getTransitiveImpact(modName, visited = new Set()) {{
    if (visited.has(modName)) return visited;
    visited.add(modName);
    const dependents = dependedBy[modName] || new Set();
    dependents.forEach(dep => getTransitiveImpact(dep, visited));
    return visited;
}}

// Compute transitive dependencies (all upstream modules this depends on)
function getTransitiveDeps(modName, visited = new Set()) {{
    if (visited.has(modName)) return visited;
    visited.add(modName);
    const deps = dependsOn[modName] || new Set();
    deps.forEach(dep => getTransitiveDeps(dep, visited));
    return visited;
}}

// Setup SVG - use explicit width/height like working graph_visualizer
const container = document.getElementById('graph');
const width = container.clientWidth || 1200;
const height = container.clientHeight || 600;

const svg = d3.select("svg").attr("width", width).attr("height", height);
const g = svg.append("g");

// Zoom behavior - filter to prevent zoom when clicking on nodes (matches working graph_visualizer)
const zoom = d3.zoom()
    .scaleExtent([0.1, 4])
    .filter(e => !e.target.closest('.node'))  // Prevent zoom/pan when clicking on nodes
    .on("zoom", e => g.attr("transform", e.transform));
svg.call(zoom);

// Arrow markers
const defs = svg.append("defs");
["internal", "external", "local"].forEach(type => {{
    const color = type === "internal" ? "#4ecdc4" : type === "external" ? "#f39c12" : "#9b59b6";
    defs.append("marker")
        .attr("id", `arrow-${{type}}`)
        .attr("viewBox", "0 -5 10 10")
        .attr("refX", 25)
        .attr("refY", 0)
        .attr("markerWidth", 6)
        .attr("markerHeight", 6)
        .attr("orient", "auto")
        .append("path")
        .attr("d", "M0,-4L10,0L0,4")
        .attr("fill", color);
}});

// Build sidebar with categories
const legendDiv = document.getElementById('module-legend');
Object.entries(categoryGroups).sort().forEach(([category, mods]) => {{
    const group = document.createElement('div');
    group.className = 'category-group';
    group.id = `cat-${{category}}`;

    const header = document.createElement('div');
    header.className = 'category-header';
    header.innerHTML = `
        <span class="category-toggle">▼</span>
        <span class="category-name">${{category}}</span>
        <span class="category-count">${{mods.length}}</span>
    `;
    header.onclick = () => toggleCategory(category);

    const content = document.createElement('div');
    content.className = 'category-content';
    content.id = `cat-content-${{category}}`;

    mods.sort().forEach(mod => {{
        const moduleNodes = moduleGroups[mod] || [];
        const funcCount = moduleNodes.filter(n => n.type === 'function' || n.type === 'async_function').length;

        const item = document.createElement('div');
        item.className = 'module-item';
        item.id = `mod-item-${{mod}}`;
        item.innerHTML = `
            <div class="module-dot" style="background:${{moduleColors[mod]}}"></div>
            <span class="module-name" title="${{mod}}" style="cursor:pointer">${{mod}}</span>
            <span class="module-metrics">${{funcCount}}fn</span>
            <span class="module-select" onclick="event.stopPropagation(); selectModuleFromSidebar('${{mod}}')" title="Select & Focus" style="font-size:10px;color:#00d4ff;padding:2px 6px;background:#1a1a2e;border-radius:3px;cursor:pointer;margin-right:4px">⎯⬤</span>
            <span class="module-expand" onclick="event.stopPropagation(); toggleModule('${{mod}}')" title="Collapse/Expand">▼</span>
        `;
        item.onclick = () => selectModuleFromSidebar(mod);
        item.ondblclick = () => focusModule(mod);
        content.appendChild(item);
    }});

    group.appendChild(header);
    group.appendChild(content);
    legendDiv.appendChild(group);
}});

// Update module count
document.getElementById('module-count').textContent = `(${{Object.keys(moduleColors).length}})`;

// Process edges - ONLY include edges where both source and target exist
const processedEdges = edges
    .filter(e => nodeById[e.from] && nodeById[e.to])  // Filter out edges with missing nodes
    .map(e => ({{
        ...e,
        source: nodeById[e.from],
        target: nodeById[e.to]
    }}));

// Force simulation - run to compute initial layout, then stop
const simulation = d3.forceSimulation(nodes)
    .force("link", d3.forceLink(processedEdges).id(d => d.id).distance(120).strength(0.4))
    .force("charge", d3.forceManyBody().strength(-500).distanceMax(400))
    .force("center", d3.forceCenter(width / 2, height / 2))
    .force("collision", d3.forceCollide().radius(d => nodeSize(d).w / 2 + 15))
    .force("x", d3.forceX(width / 2).strength(0.03))
    .force("y", d3.forceY(height / 2).strength(0.03))
    .alphaDecay(0.05)
    .velocityDecay(0.5);

// Run simulation synchronously to completion for initial layout (prevents jump)
simulation.stop();
for (let i = 0; i < 300; i++) simulation.tick();
// Now simulation is stopped - only restarts on drag

// Draw edges
const edge = g.append("g").selectAll("path")
    .data(processedEdges)
    .join("path")
    .attr("class", d => `edge edge-${{d.type || 'internal'}}`)
    .attr("marker-end", d => `url(#arrow-${{d.type || 'internal'}})`);

// Node size based on type and collapsed state
function nodeSize(d) {{
    if (d.type === 'module') {{
        const isCollapsed = collapsedModules.has(d.id);
        return isCollapsed ? {{ w: 160, h: 55 }} : {{ w: 140, h: 45 }};
    }}
    if (d.type === 'function' || d.type === 'async_function') return {{ w: 120, h: 35 }};
    if (d.type === 'class') return {{ w: 130, h: 40 }};
    if (d.type === 'dependency') return {{ w: 140, h: 40 }};  // Larger for packages/imports
    return {{ w: 100, h: 30 }};
}}

// Drag behavior - matches working graph_visualizer pattern
let dragStartPos = null;
let isDragging = false;
const DRAG_THRESHOLD = 5;

// Function to update edge positions
function updateEdges() {{
    edge.attr("d", d => {{
        if (!d.source || !d.target) return "";
        const dx = d.target.x - d.source.x;
        const dy = d.target.y - d.source.y;
        const dr = Math.sqrt(dx * dx + dy * dy) * 1.5;
        return `M${{d.source.x}},${{d.source.y}}A${{dr}},${{dr}} 0 0,1 ${{d.target.x}},${{d.target.y}}`;
    }});
}}

const drag = d3.drag()
    .on("start", function(e, d) {{
        e.sourceEvent.stopPropagation();
        dragStartPos = {{ x: e.x, y: e.y }};
        isDragging = false;
    }})
    .on("drag", function(e, d) {{
        const dx = e.x - dragStartPos.x;
        const dy = e.y - dragStartPos.y;
        if (Math.sqrt(dx*dx + dy*dy) > DRAG_THRESHOLD) {{
            isDragging = true;
            d3.select(this).raise().select("rect").attr("stroke", "#ff0").attr("stroke-width", 4);
            d.x = e.x;
            d.y = e.y;
            d.fx = e.x;
            d.fy = e.y;
            d3.select(this).attr("transform", `translate(${{e.x}},${{e.y}})`);
            // Update edges immediately during drag
            updateEdges();
        }}
    }})
    .on("end", function(e, d) {{
        if (isDragging) {{
            d3.select(this).select("rect").attr("stroke", d.moduleColor || "#666").attr("stroke-width", d.type === 'module' ? 3 : 2);
            d.fx = null;
            d.fy = null;
            updateEdges();
        }}
        dragStartPos = null;
        isDragging = false;
    }});

// Draw nodes
const node = g.append("g").selectAll("g")
    .data(nodes)
    .join("g")
    .attr("class", "node")
    .call(drag);

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
    .attr("dy", d => d.signature ? -3 : 5)
    .text(d => {{
        const label = d.label || d.id;
        return label.length > 18 ? label.slice(0, 16) + '..' : label;
    }});

node.filter(d => d.signature).append("text")
    .attr("class", "node-sublabel")
    .attr("text-anchor", "middle")
    .attr("dy", 10)
    .text(d => d.signature.length > 20 ? d.signature.slice(0, 18) + ".." : d.signature);

// Add collapse indicator for modules
node.filter(d => d.type === 'module').append("text")
    .attr("class", "node-badge collapse-indicator")
    .attr("x", d => nodeSize(d).w / 2 - 15)
    .attr("y", d => -nodeSize(d).h / 2 + 12)
    .attr("font-size", "10px")
    .attr("fill", "#888")
    .text("▼")
    .style("cursor", "pointer");

// Tooltip
const tooltip = d3.select("#tooltip");
node.on("mouseover", (e, d) => {{
    let html = `<b>${{d.label || d.id}}</b>`;
    if (d.type) html += `<br><span style="color:#888">${{d.type}}</span>`;
    if (d.signature) html += `<br><code>${{d.signature}}</code>`;
    if (collapsedModules.has(d.moduleName || d.id)) html += `<br><span style="color:#f39c12">[collapsed]</span>`;
    tooltip.style("display", "block").html(html);
}})
.on("mousemove", e => {{
    tooltip.style("left", (e.pageX + 15) + "px").style("top", (e.pageY - 10) + "px");
}})
.on("mouseout", () => tooltip.style("display", "none"));

// Use pointerup as backup for click detection (D3 drag can consume click events)
node.on("pointerup", function(event) {{
    // Get datum from the element
    const datum = d3.select(this).datum();
    // Only handle if this wasn't a drag (check if node moved significantly)
    if (!isDragging && dragStartPos && datum) {{
        console.log("Pointerup detected on node:", datum.id);
        event.stopPropagation();
        selectNode(datum, event);
    }}
}});

// Double-click to collapse modules
node.on("dblclick", (e, d) => {{
    e.stopPropagation();
    if (d.type === 'module') {{
        toggleModule(d.id);
    }} else if (d.moduleName) {{
        toggleModule(d.moduleName);
    }}
}});

// Click on svg background to clear selection
svg.on("click", (e) => {{
    if (e.target.tagName === 'svg') {{
        clearSelection();
    }}
}});

// Function to update positions (used for both initial layout and tick)
function updatePositions() {{
    edge.attr("d", d => {{
        if (!d.source || !d.target) return "";
        const dx = d.target.x - d.source.x;
        const dy = d.target.y - d.source.y;
        const dr = Math.sqrt(dx * dx + dy * dy) * 1.5;
        return `M${{d.source.x}},${{d.source.y}}A${{dr}},${{dr}} 0 0,1 ${{d.target.x}},${{d.target.y}}`;
    }});
    node.attr("transform", d => `translate(${{d.x}},${{d.y}})`);
}}

// Apply initial positions after synchronous simulation
updatePositions();

// Tick handler for when simulation is restarted during drag
simulation.on("tick", updatePositions);


// === COLLAPSE/EXPAND FUNCTIONS ===

function toggleModule(modName) {{
    if (collapsedModules.has(modName)) {{
        collapsedModules.delete(modName);
    }} else {{
        collapsedModules.add(modName);
    }}
    updateVisibility();
    updateSidebarState(modName);
}}

function collapseAll() {{
    Object.keys(moduleColors).forEach(mod => collapsedModules.add(mod));
    updateVisibility();
    updateAllSidebarStates();
}}

function expandAll() {{
    collapsedModules.clear();
    updateVisibility();
    updateAllSidebarStates();
}}

function updateVisibility() {{
    // Hide/show nodes based on collapsed state
    node.classed("node-hidden", d => {{
        if (d.type === 'module') return false;  // Always show module nodes
        if (d.type === 'dependency') return false;  // Always show dependencies
        return collapsedModules.has(d.moduleName);  // Hide children of collapsed modules
    }});

    // Update module node appearance when collapsed
    node.select("rect").classed("node-collapsed", d => d.type === 'module' && collapsedModules.has(d.id));
    node.select(".collapse-indicator").text(d => collapsedModules.has(d.id) ? "►" : "▼");

    // Hide edges connected to hidden nodes
    edge.classed("edge-hidden", d => {{
        const srcHidden = d.source.type !== 'module' && d.source.type !== 'dependency' && collapsedModules.has(d.source.moduleName);
        const tgtHidden = d.target.type !== 'module' && d.target.type !== 'dependency' && collapsedModules.has(d.target.moduleName);
        return srcHidden || tgtHidden;
    }});

    updateStats();

    // Restart simulation to reposition with higher alpha for visible movement
    if (currentLayout === 'force') {{
        simulation.alpha(0.8).restart();
    }}
}}

function updateSidebarState(modName) {{
    const item = document.getElementById(`mod-item-${{modName}}`);
    if (item) {{
        const expand = item.querySelector('.module-expand');
        if (expand) {{
            expand.classList.toggle('collapsed', collapsedModules.has(modName));
            expand.textContent = collapsedModules.has(modName) ? '►' : '▼';
        }}
    }}
}}

function updateAllSidebarStates() {{
    Object.keys(moduleColors).forEach(mod => updateSidebarState(mod));
}}

function updateStats() {{
    const modCount = nodes.filter(n => n.type === 'module').length;
    const funcCount = nodes.filter(n => n.type === 'function' || n.type === 'async_function').length;
    const depCount = nodes.filter(n => n.type === 'dependency').length;
    const visibleCount = nodes.filter(n => {{
        if (n.type === 'module' || n.type === 'dependency') return true;
        return !collapsedModules.has(n.moduleName);
    }}).length;

    document.getElementById('stat-modules').textContent = modCount;
    document.getElementById('stat-functions').textContent = funcCount;
    document.getElementById('stat-deps').textContent = depCount;
    document.getElementById('stat-edges').textContent = processedEdges.length;
    document.getElementById('stat-visible').textContent = visibleCount;
}}

// === CATEGORY TOGGLE ===

function toggleCategory(category) {{
    const content = document.getElementById(`cat-content-${{category}}`);
    const toggle = document.querySelector(`#cat-${{category}} .category-toggle`);
    if (content && toggle) {{
        content.classList.toggle('collapsed');
        toggle.classList.toggle('collapsed');
    }}
}}

function foldAllCategories() {{
    Object.keys(categoryGroups).forEach(category => {{
        const content = document.getElementById(`cat-content-${{category}}`);
        const toggle = document.querySelector(`#cat-${{category}} .category-toggle`);
        if (content && toggle) {{
            content.classList.add('collapsed');
            toggle.classList.add('collapsed');
        }}
    }});
}}

function unfoldAllCategories() {{
    Object.keys(categoryGroups).forEach(category => {{
        const content = document.getElementById(`cat-content-${{category}}`);
        const toggle = document.querySelector(`#cat-${{category}} .category-toggle`);
        if (content && toggle) {{
            content.classList.remove('collapsed');
            toggle.classList.remove('collapsed');
        }}
    }});
}}

// === SEARCH/FILTER ===

function filterModules(query) {{
    searchQuery = query.toLowerCase();
    document.querySelectorAll('.module-item').forEach(item => {{
        const name = item.querySelector('.module-name').textContent.toLowerCase();
        item.classList.toggle('hidden', query && !name.includes(searchQuery));
    }});

    // Also filter nodes visually
    if (query) {{
        node.classed("dim", d => {{
            const label = (d.label || d.id || '').toLowerCase();
            const modName = (d.moduleName || '').toLowerCase();
            return !label.includes(searchQuery) && !modName.includes(searchQuery);
        }});
    }} else {{
        node.classed("dim", false);
    }}
}}

function getSearchMatches() {{
    if (!searchQuery) return [];
    return nodes.filter(d => {{
        const label = (d.label || d.id || '').toLowerCase();
        const modName = (d.moduleName || '').toLowerCase();
        return label.includes(searchQuery) || modName.includes(searchQuery);
    }});
}}

function selectSearchResults() {{
    const matches = getSearchMatches();
    if (matches.length === 0) return;
    selectedNodes.clear();
    matches.forEach(d => selectedNodes.add(d.id));
    updateSelectionDisplay();
}}

function addSearchToSelection() {{
    const matches = getSearchMatches();
    if (matches.length === 0) return;
    matches.forEach(d => selectedNodes.add(d.id));
    updateSelectionDisplay();
}}

function selectAllIncoming() {{
    if (selectedNodes.size === 0) return;
    const currentSelected = [...selectedNodes];
    processedEdges.forEach(e => {{
        if (currentSelected.includes(e.target.id)) {{
            selectedNodes.add(e.source.id);
        }}
    }});
    updateSelectionDisplay();
}}

function selectAllOutgoing() {{
    if (selectedNodes.size === 0) return;
    const currentSelected = [...selectedNodes];
    processedEdges.forEach(e => {{
        if (currentSelected.includes(e.source.id)) {{
            selectedNodes.add(e.target.id);
        }}
    }});
    updateSelectionDisplay();
}}

// === FOCUS MODULE ===

function focusModule(modName) {{
    // Expand this module if collapsed
    if (collapsedModules.has(modName)) {{
        collapsedModules.delete(modName);
        updateVisibility();
        updateSidebarState(modName);
    }}

    // Center on module node
    const modNode = nodes.find(n => n.id === modName || n.moduleName === modName);
    if (modNode && modNode.x && modNode.y) {{
        svg.transition().duration(500).call(
            zoom.transform,
            d3.zoomIdentity.translate(width / 2 - modNode.x, height / 2 - modNode.y).scale(1.5)
        );
    }}

    // Highlight module
    highlightModule(modName);
}}

// Selection functions - Multi-select support
const selectedNodes = new Set();

function selectNode(d, event) {{
    const isMultiSelect = event && (event.ctrlKey || event.metaKey || event.shiftKey);

    if (isMultiSelect) {{
        // Toggle selection
        if (selectedNodes.has(d.id)) {{
            selectedNodes.delete(d.id);
        }} else {{
            selectedNodes.add(d.id);
        }}
    }} else {{
        // Single select - clear others
        selectedNodes.clear();
        selectedNodes.add(d.id);
    }}

    updateSelectionDisplay();
}}

function updateSelectionDisplay() {{
    const selectedIds = [...selectedNodes];
    const selectedData = selectedIds.map(id => nodeById[id]).filter(Boolean);

    // Update selection count
    document.getElementById('selection-count').textContent = `(${{selectedNodes.size}})`;

    if (selectedNodes.size === 0) {{
        node.classed("dim", false);
        node.select("rect").attr("stroke-width", d => d.type === 'module' ? 3 : 2);
        edge.classed("dim", false).classed("highlight", false);
        document.getElementById('node-info').innerHTML = 'Click a node to see details';
        document.getElementById('edge-list').innerHTML = '';
        document.getElementById('connection-summary').textContent = '';
        return;
    }}

    // Highlight selected nodes and their connections
    const connectedIds = new Set(selectedIds);
    processedEdges.forEach(e => {{
        if (selectedNodes.has(e.source.id)) connectedIds.add(e.target.id);
        if (selectedNodes.has(e.target.id)) connectedIds.add(e.source.id);
    }});

    node.classed("dim", n => !connectedIds.has(n.id));
    node.select("rect").attr("stroke-width", n => selectedNodes.has(n.id) ? 4 : 2);

    // Highlight edges connected to any selected node
    edge.classed("dim", e => !selectedNodes.has(e.source.id) && !selectedNodes.has(e.target.id));
    edge.classed("highlight", e => selectedNodes.has(e.source.id) || selectedNodes.has(e.target.id));

    // Update info panel for single or multiple selection
    if (selectedNodes.size === 1) {{
        updateNodeInfo(selectedData[0]);
    }} else {{
        updateMultiNodeInfo(selectedData);
    }}
    updateCombinedEdgeList(selectedData);
}}

function clearSelection() {{
    selectedNodes.clear();
    updateSelectionDisplay();
}}

function isConnected(a, b) {{
    return processedEdges.some(e =>
        (e.source.id === a.id && e.target.id === b.id) ||
        (e.source.id === b.id && e.target.id === a.id)
    );
}}

function updateMultiNodeInfo(nodes) {{
    let html = `<div style="color:#00d4ff;font-weight:bold;margin-bottom:10px">${{nodes.length}} items selected</div>`;
    html += '<div style="max-height:150px;overflow-y:auto">';
    nodes.forEach(d => {{
        const color = d.moduleColor || moduleColors[d.moduleName] || '#666';
        html += `<div style="display:flex;align-items:center;gap:8px;padding:4px 0;border-bottom:1px solid #333">`;
        html += `<span style="width:8px;height:8px;background:${{color}};border-radius:2px"></span>`;
        html += `<span style="flex:1">${{d.label || d.id}}</span>`;
        html += `<span style="color:#666;font-size:10px">${{d.type}}</span>`;
        html += `</div>`;
    }});
    html += '</div>';
    document.getElementById('node-info').innerHTML = html;
    document.getElementById('source-content').innerHTML = '<div style="color:#666;font-size:13px">Select a single node to view source</div>';
}}

function updateCombinedEdgeList(selectedData) {{
    const selectedIds = new Set(selectedData.map(d => d.id));

    // Collect all outgoing and incoming edges for selected nodes
    const outgoing = [];
    const incoming = [];

    processedEdges.forEach(e => {{
        if (selectedIds.has(e.source.id) && !selectedIds.has(e.target.id)) {{
            outgoing.push(e);
        }}
        if (selectedIds.has(e.target.id) && !selectedIds.has(e.source.id)) {{
            incoming.push(e);
        }}
    }});

    // Deduplicate by target/source
    const uniqueOutgoing = [...new Map(outgoing.map(e => [e.target.id, e])).values()];
    const uniqueIncoming = [...new Map(incoming.map(e => [e.source.id, e])).values()];

    // Update summary
    document.getElementById('connection-summary').textContent = `(${{uniqueIncoming.length}} in, ${{uniqueOutgoing.length}} out)`;

    let html = '';
    if (uniqueOutgoing.length) {{
        html += `<div style="color:#4ecdc4;font-weight:bold;margin-bottom:5px">Outgoing (${{uniqueOutgoing.length}}) →</div>`;
        uniqueOutgoing.slice(0, 20).forEach(e => {{
            const fromLabel = e.source.label || e.source.id;
            html += `<div class="edge-item" style="cursor:pointer" onclick="selectNodeById('${{e.target.id}}')">`;
            html += `<span style="color:#666;font-size:10px">from ${{fromLabel.slice(0,15)}}</span> → `;
            html += `<span class="to">${{e.target.label || e.target.id}}</span>`;
            html += `</div>`;
        }});
        if (uniqueOutgoing.length > 20) html += `<div style="color:#666;font-size:10px">...and ${{uniqueOutgoing.length - 20}} more</div>`;
    }}
    if (uniqueIncoming.length) {{
        html += `<div style="color:#f39c12;font-weight:bold;margin:10px 0 5px 0">← Incoming (${{uniqueIncoming.length}})</div>`;
        uniqueIncoming.slice(0, 20).forEach(e => {{
            const toLabel = e.target.label || e.target.id;
            html += `<div class="edge-item" style="cursor:pointer" onclick="selectNodeById('${{e.source.id}}')">`;
            html += `<span class="from">${{e.source.label || e.source.id}}</span>`;
            html += ` → <span style="color:#666;font-size:10px">to ${{toLabel.slice(0,15)}}</span>`;
            html += `</div>`;
        }});
        if (uniqueIncoming.length > 20) html += `<div style="color:#666;font-size:10px">...and ${{uniqueIncoming.length - 20}} more</div>`;
    }}
    if (!uniqueOutgoing.length && !uniqueIncoming.length) {{
        html = '<div style="color:#666">No external connections</div>';
    }}

    document.getElementById('edge-list').innerHTML = html;
}}

function selectNodeById(id) {{
    const d = nodeById[id];
    if (d) {{
        selectedNodes.clear();
        selectedNodes.add(id);
        updateSelectionDisplay();
        focusOnNode(d);
    }}
}}

function selectModuleFromSidebar(modName) {{
    // Find the module node
    const modNode = nodes.find(n => n.id === modName && n.type === 'module');
    if (modNode) {{
        selectedNodes.clear();
        selectedNodes.add(modName);
        updateSelectionDisplay();
        focusOnNode(modNode);
    }}
}}

function focusOnNode(d) {{
    if (d.x && d.y) {{
        svg.transition().duration(300).call(
            zoom.transform,
            d3.zoomIdentity.translate(width / 2 - d.x, height / 2 - d.y).scale(1.2)
        );
    }}
}}

function updateNodeInfo(d) {{
    let html = `<div class="metric"><span class="info-label">ID:</span><span class="info-value">${{d.id}}</span></div>`;
    html += `<div class="metric"><span class="info-label">Type:</span><span class="info-value">${{d.type}}</span></div>`;
    if (d.moduleName) html += `<div class="metric"><span class="info-label">Module:</span><span class="info-value">${{d.moduleName}}</span></div>`;
    if (d.line) html += `<div class="metric"><span class="info-label">Line:</span><span class="info-value">${{d.line}}${{d.endLine ? '-' + d.endLine : ''}}</span></div>`;
    if (d.signature) html += `<div class="metric"><span class="info-label">Signature:</span><span class="info-value" style="font-family:monospace">${{d.signature}}</span></div>`;
    if (d.direction) html += `<div class="metric"><span class="info-label">Direction:</span><span class="info-value">${{d.direction}}</span></div>`;
    if (d.category) html += `<div class="metric"><span class="info-label">Category:</span><span class="info-value">${{d.category}}</span></div>`;

    if (d.metrics || d.type === 'module') {{
        const modName = d.type === 'module' ? d.id : d.moduleName;
        const fanIn = d.metrics?.fanIn || 0;
        const fanOut = d.metrics?.fanOut || 0;
        const instability = d.metrics?.instability || 0;
        const internalEdges = d.metrics?.internalEdges || 0;
        const total = fanIn + fanOut;

        // Compute transitive impact
        const directDependents = dependedBy[modName] ? dependedBy[modName].size : 0;
        const directDeps = dependsOn[modName] ? dependsOn[modName].size : 0;
        const transitiveImpact = getTransitiveImpact(modName);
        const transitiveDeps = getTransitiveDeps(modName);
        const totalImpacted = transitiveImpact.size - 1;  // Exclude self
        const totalDeps = transitiveDeps.size - 1;  // Exclude self

        html += `<div style="margin-top:10px;padding:8px;background:#1a1a2e;border-radius:4px;border:1px solid #333">`;
        html += `<div style="font-weight:bold;color:#00d4ff;margin-bottom:8px">Dependency Analysis</div>`;

        // Impact section (who depends on this)
        html += `<div style="background:#2a2a3a;padding:6px;border-radius:3px;margin-bottom:8px">`;
        html += `<div style="font-size:11px;color:#f39c12;font-weight:bold;margin-bottom:4px">⬆ IMPACT (if this changes)</div>`;
        html += `<div class="metric"><span class="info-label">Direct dependents:</span><span class="info-value">${{directDependents}}</span></div>`;
        html += `<div class="metric"><span class="info-label" style="color:#ff6b6b">Total affected:</span><span class="info-value" style="color:#ff6b6b;font-weight:bold">${{totalImpacted}}</span></div>`;
        if (totalImpacted > directDependents) {{
            html += `<div style="font-size:10px;color:#888">↳ ${{totalImpacted - directDependents}} modules indirectly affected</div>`;
        }}
        html += `</div>`;

        // Dependencies section (what this depends on)
        html += `<div style="background:#2a3a2a;padding:6px;border-radius:3px;margin-bottom:8px">`;
        html += `<div style="font-size:11px;color:#4ecdc4;font-weight:bold;margin-bottom:4px">⬇ DEPENDENCIES (what this needs)</div>`;
        html += `<div class="metric"><span class="info-label">Direct imports:</span><span class="info-value">${{directDeps}}</span></div>`;
        html += `<div class="metric"><span class="info-label">Total chain:</span><span class="info-value">${{totalDeps}}</span></div>`;
        if (totalDeps > directDeps) {{
            html += `<div style="font-size:10px;color:#888">↳ ${{totalDeps - directDeps}} transitive dependencies</div>`;
        }}
        html += `</div>`;

        // Internal complexity
        html += `<div class="metric"><span class="info-label">Internal calls:</span><span class="info-value">${{internalEdges}}</span></div>`;

        // Instability with formula
        const instColor = instability > 0.5 ? '#ff6b6b' : '#4ecdc4';
        html += `<div style="border-top:1px solid #333;padding-top:8px;margin-top:8px">`;
        html += `<div class="metric"><span class="info-label">Instability:</span><span class="info-value" style="color:${{instColor}};font-weight:bold">${{(instability * 100).toFixed(1)}}%</span></div>`;
        html += `<div class="metric-bar"><div class="metric-fill" style="width:${{instability * 100}}%;background:${{instColor}}"></div></div>`;
        html += `<div style="font-size:10px;color:#888;margin-top:4px;font-family:monospace">= FanOut/(FanIn+FanOut) = ${{fanOut}}/${{total || 1}}</div>`;
        html += `</div></div>`;
    }}

    document.getElementById('node-info').innerHTML = html;
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
        const funcCount = (moduleGroups[d.id] || []).filter(n => n.type === 'function').length;
        panel.innerHTML = `<div style="color:#888;font-size:11px">Module: ${{d.label}}<br>Functions: ${{funcCount}}<br><br>Double-click to collapse/expand</div>`;
    }} else if (d.type === 'dependency') {{
        panel.innerHTML = `<div style="color:#888;font-size:11px">External dependency: ${{d.label}}<br>Category: ${{d.category || 'unknown'}}</div>`;
    }} else {{
        panel.innerHTML = `<div style="color:#666;font-size:11px">No source available</div>`;
    }}
}}

function highlightModule(modName) {{
    clearSelection();
    node.classed("dim", n => n.moduleName !== modName && n.id !== modName && n.type !== 'dependency');
    edge.classed("dim", e => {{
        const srcMod = e.source.moduleName || e.source.id;
        const tgtMod = e.target.moduleName || e.target.id;
        return srcMod !== modName && tgtMod !== modName;
    }});
}}

// Layout functions
function toggleLayout(layout) {{
    currentLayout = layout;
    document.querySelectorAll('.controls button').forEach(b => {{
        if (b.id.startsWith('btn-') && ['force', 'cluster', 'tree'].includes(b.id.replace('btn-', ''))) {{
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
    const padding = 80;

    if (layout === 'cluster') {{
        // Cluster layout - modules in grid, functions around them
        const cols = Math.ceil(Math.sqrt(modules.length));
        const cellW = (width - padding * 2) / cols;
        const cellH = (height - padding * 2) / Math.ceil(modules.length / cols);

        modules.forEach((mod, mi) => {{
            const col = mi % cols;
            const row = Math.floor(mi / cols);
            const cx = padding + col * cellW + cellW / 2;
            const cy = padding + row * cellH + cellH / 2;

            // Module at center
            const modNode = nodes.find(n => n.id === mod);
            if (modNode) {{ modNode.x = cx; modNode.y = cy; }}

            // Functions around it
            const funcs = nodes.filter(n => n.moduleName === mod && n.type !== 'module');
            const radius = Math.min(cellW, cellH) * 0.35;
            funcs.forEach((n, fi) => {{
                const angle = (2 * Math.PI * fi) / funcs.length;
                n.x = cx + radius * Math.cos(angle);
                n.y = cy + radius * Math.sin(angle);
            }});
        }});

        // Dependencies at bottom
        const deps = nodes.filter(n => n.type === 'dependency');
        deps.forEach((n, i) => {{
            n.x = padding + (i % 10) * 90;
            n.y = height - padding;
        }});
    }} else if (layout === 'tree') {{
        // Tree layout - modules at top, functions below
        const modNodes = nodes.filter(n => n.type === 'module');
        const funcNodes = nodes.filter(n => n.type === 'function' || n.type === 'async_function' || n.type === 'class');
        const depNodes = nodes.filter(n => n.type === 'dependency');

        modNodes.forEach((n, i) => {{
            n.x = padding + (i % 8) * 120;
            n.y = padding + Math.floor(i / 8) * 60;
        }});

        funcNodes.forEach((n, i) => {{
            n.x = padding + (i % 10) * 100;
            n.y = 200 + Math.floor(i / 10) * 50;
        }});

        depNodes.forEach((n, i) => {{
            n.x = padding + (i % 12) * 80;
            n.y = height - padding - 30;
        }});
    }}

    // Animate transition
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
    edge.style("display", d => {{
        if (!edgeVisibility[d.type || 'internal']) return "none";
        // Also respect collapse state
        const srcHidden = d.source.type !== 'module' && d.source.type !== 'dependency' && collapsedModules.has(d.source.moduleName);
        const tgtHidden = d.target.type !== 'module' && d.target.type !== 'dependency' && collapsedModules.has(d.target.moduleName);
        return (srcHidden || tgtHidden) ? "none" : null;
    }});
}}

// View controls
function resetView() {{
    svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity);
    clearSelection();
}}

function fitToView() {{
    const bounds = g.node().getBBox();
    if (bounds.width === 0 || bounds.height === 0) return;
    const scale = Math.min(width / bounds.width, height / bounds.height) * 0.85;
    const tx = (width - bounds.width * scale) / 2 - bounds.x * scale;
    const ty = (height - bounds.height * scale) / 2 - bounds.y * scale;
    svg.transition().duration(500).call(zoom.transform, d3.zoomIdentity.translate(tx, ty).scale(scale));
}}

// Initialize
updateStats();
setTimeout(fitToView, 1000);

// === TABLE VIEW FUNCTIONS ===
let tableData = [];
let sortCol = 0;
let sortAsc = true;

function buildTableData() {{
    tableData = [];
    const moduleNodes = nodes.filter(n => n.type === 'module');

    moduleNodes.forEach(mod => {{
        const modName = mod.id;
        const funcs = (moduleGroups[modName] || []).filter(n => n.type === 'function' || n.type === 'async_function');
        const metrics = mod.metrics || {{}};

        const directDeps = dependedBy[modName] ? dependedBy[modName].size : 0;
        const transitiveImpact = getTransitiveImpact(modName);
        const transitiveDeps = getTransitiveDeps(modName);
        const totalImpact = transitiveImpact.size - 1;
        const totalUpstream = transitiveDeps.size - 1;

        tableData.push({{
            name: modName,
            funcs: funcs.length,
            fanIn: metrics.fanIn || 0,
            fanOut: metrics.fanOut || 0,
            instability: metrics.instability || 0,
            directDeps: directDeps,
            totalImpact: totalImpact,
            upstream: totalUpstream,
            color: moduleColors[modName] || '#666'
        }});
    }});
}}

function renderTable() {{
    const tbody = document.getElementById('table-body');
    tbody.innerHTML = '';

    tableData.forEach(row => {{
        const tr = document.createElement('tr');
        tr.style.cssText = 'border-bottom:1px solid #333;cursor:pointer;';
        tr.onmouseover = () => tr.style.background = '#2a2a4a';
        tr.onmouseout = () => tr.style.background = '';
        tr.onclick = () => {{ toggleTableView(); selectModuleFromSidebar(row.name); }};

        const instColor = row.instability > 0.5 ? '#ff6b6b' : '#4ecdc4';
        const impactColor = row.totalImpact > 5 ? '#ff6b6b' : row.totalImpact > 2 ? '#f39c12' : '#4ecdc4';

        tr.innerHTML = `
            <td style="padding:8px"><span style="display:inline-block;width:10px;height:10px;background:${{row.color}};border-radius:2px;margin-right:8px"></span>${{row.name}}</td>
            <td style="padding:8px;text-align:center">${{row.funcs}}</td>
            <td style="padding:8px;text-align:center;color:#4ecdc4">${{row.fanIn}}</td>
            <td style="padding:8px;text-align:center;color:#f39c12">${{row.fanOut}}</td>
            <td style="padding:8px;text-align:center;color:${{instColor}}">${{(row.instability * 100).toFixed(0)}}%</td>
            <td style="padding:8px;text-align:center">${{row.directDeps}}</td>
            <td style="padding:8px;text-align:center;color:${{impactColor}};font-weight:bold">${{row.totalImpact}}</td>
            <td style="padding:8px;text-align:center">${{row.upstream}}</td>
        `;
        tbody.appendChild(tr);
    }});
}}

function sortTable(col) {{
    if (sortCol === col) {{
        sortAsc = !sortAsc;
    }} else {{
        sortCol = col;
        sortAsc = true;
    }}

    const keys = ['name', 'funcs', 'fanIn', 'fanOut', 'instability', 'directDeps', 'totalImpact', 'upstream'];
    const key = keys[col];

    tableData.sort((a, b) => {{
        let cmp = 0;
        if (typeof a[key] === 'string') {{
            cmp = a[key].localeCompare(b[key]);
        }} else {{
            cmp = a[key] - b[key];
        }}
        return sortAsc ? cmp : -cmp;
    }});

    renderTable();
}}

function filterTable(query) {{
    const q = query.toLowerCase();
    const rows = document.querySelectorAll('#table-body tr');
    rows.forEach(row => {{
        const name = row.cells[0].textContent.toLowerCase();
        row.style.display = name.includes(q) ? '' : 'none';
    }});
}}

function toggleTableView() {{
    const container = document.getElementById('container');
    const tableView = document.getElementById('table-view');
    const statsBar = document.querySelector('.stats-bar');
    const controls = document.querySelector('.controls');

    if (tableView.style.display === 'none') {{
        // Show table
        container.style.display = 'none';
        statsBar.style.display = 'none';
        controls.style.display = 'none';
        tableView.style.display = 'block';
        buildTableData();
        sortTable(6);  // Sort by total impact by default
    }} else {{
        // Show graph
        container.style.display = 'flex';
        statsBar.style.display = 'flex';
        controls.style.display = 'flex';
        tableView.style.display = 'none';
    }}
}}
</script>
</body>
</html>'''


# === DEPENDENCY RESOLUTION FUNCTIONS ===

def resolveImportPath(params: dict) -> dict:
    """Resolve a project-relative import to a file path.

    Args:
        params: dict with:
            - projectRoot: absolute path to project root
            - importModule: module string (e.g. 'src.actions.scraper')
            - currentFile: (optional) current file for relative imports
            - level: (optional) relative import level (1 = ., 2 = .., etc.)

    Returns:
        dict with:
            - resolvedPath: absolute path to the Python file, or None
            - isPackage: True if it's a package __init__.py
            - error: error message if not found
    """
    projectRoot = params.get("projectRoot", "")
    importModule = params.get("importModule", "")
    currentFile = params.get("currentFile", "")
    level = params.get("level", 0)

    if not projectRoot or not importModule:
        return {"resolvedPath": None, "isPackage": False, "error": "Missing projectRoot or importModule"}

    projectRoot = Path(projectRoot)

    # Handle relative imports
    if level > 0 and currentFile:
        currentDir = Path(currentFile).parent
        # Go up 'level' directories
        for _ in range(level):
            currentDir = currentDir.parent
        basePath = currentDir
    else:
        basePath = projectRoot

    # Convert module path to file path
    parts = importModule.split(".") if importModule else []
    modulePath = basePath.joinpath(*parts)

    # Check for direct .py file
    pyFile = modulePath.with_suffix(".py")
    if pyFile.exists() and pyFile.is_file():
        return {"resolvedPath": str(pyFile), "isPackage": False, "error": None}

    # Check for package __init__.py
    initFile = modulePath / "__init__.py"
    if initFile.exists() and initFile.is_file():
        return {"resolvedPath": str(initFile), "isPackage": True, "error": None}

    # Check if modulePath itself is a file (without .py extension check)
    if modulePath.exists() and modulePath.is_file():
        return {"resolvedPath": str(modulePath), "isPackage": False, "error": None}

    return {
        "resolvedPath": None,
        "isPackage": False,
        "error": f"Cannot resolve: {importModule} from {basePath}"
    }


def buildProjectDependencyGraph(params: dict) -> dict:
    """Build a complete dependency graph for a Python project.

    Args:
        params: dict with:
            - projectRoot: absolute path to project root
            - pythonFiles: list of file info dicts with 'path' and 'module' keys
            - includeExternal: (optional) include stdlib/pip deps (default False)

    Returns:
        dict with:
            - graph: dict mapping module -> list of dependency modules
            - reverseGraph: dict mapping module -> list of dependent modules
            - externalDeps: set of external (non-project) dependencies
            - fileToModule: dict mapping file path -> module name
            - moduleToFile: dict mapping module name -> file path
    """
    projectRoot = params.get("projectRoot", "")
    pythonFiles = params.get("pythonFiles", [])
    includeExternal = params.get("includeExternal", False)

    if not projectRoot or not pythonFiles:
        return {"graph": {}, "reverseGraph": {}, "externalDeps": set(),
                "fileToModule": {}, "moduleToFile": {}}

    projectRoot = Path(projectRoot)

    # Build file <-> module mappings
    fileToModule = {}
    moduleToFile = {}
    for fileInfo in pythonFiles:
        filePath = fileInfo.get("path", "")
        moduleName = fileInfo.get("module", "")
        if filePath and moduleName:
            fileToModule[filePath] = moduleName
            moduleToFile[moduleName] = filePath

    # Set of all known project modules (for detecting local vs external)
    projectModules = set(moduleToFile.keys())

    # Also add parent modules (e.g., "src" if we have "src.actions.scraper")
    for mod in list(projectModules):
        parts = mod.split(".")
        for i in range(1, len(parts)):
            projectModules.add(".".join(parts[:i]))

    graph = defaultdict(list)       # module -> [dependencies]
    reverseGraph = defaultdict(list)  # module -> [dependents]
    externalDeps = set()

    for fileInfo in pythonFiles:
        filePath = fileInfo.get("path", "")
        moduleName = fileToModule.get(filePath, "")

        if not moduleName:
            continue

        # Parse the file to extract imports
        try:
            result = loadFile({"filePath": filePath})
            if result.get("error"):
                continue
            source = result["sourceCode"]

            result = parseAst({"sourceCode": source})
            if result.get("error"):
                continue
            tree = result["ast"]

            imports = extractImports({"ast": tree}).get("imports", [])

            for imp in imports:
                impModule = imp.get("module", "")
                impLevel = imp.get("level", 0)
                impCategory = imp.get("category", "")

                # Handle relative imports
                if impLevel > 0:
                    # Resolve relative import
                    resolved = resolveImportPath({
                        "projectRoot": str(projectRoot),
                        "importModule": impModule,
                        "currentFile": filePath,
                        "level": impLevel
                    })
                    if resolved.get("resolvedPath"):
                        depModule = fileToModule.get(resolved["resolvedPath"])
                        if depModule:
                            if depModule not in graph[moduleName]:
                                graph[moduleName].append(depModule)
                            if moduleName not in reverseGraph[depModule]:
                                reverseGraph[depModule].append(moduleName)
                elif impCategory == "local" or impModule in projectModules:
                    # Local/project import
                    # Check if this is a known project module or its submodule
                    depModule = impModule
                    baseMod = impModule.split(".")[0] if impModule else ""

                    # Try to find the most specific matching module
                    if depModule in projectModules:
                        if depModule not in graph[moduleName]:
                            graph[moduleName].append(depModule)
                        if moduleName not in reverseGraph[depModule]:
                            reverseGraph[depModule].append(moduleName)
                    elif baseMod in projectModules:
                        # Use base module
                        if baseMod not in graph[moduleName]:
                            graph[moduleName].append(baseMod)
                        if moduleName not in reverseGraph[baseMod]:
                            reverseGraph[baseMod].append(moduleName)
                else:
                    # External dependency (stdlib or pip)
                    if impModule:
                        externalDeps.add(impModule.split(".")[0])

        except Exception as e:
            # Skip files that can't be parsed
            continue

    return {
        "graph": dict(graph),
        "reverseGraph": dict(reverseGraph),
        "externalDeps": list(externalDeps),
        "fileToModule": fileToModule,
        "moduleToFile": moduleToFile
    }


def getCompileOrder(params: dict) -> dict:
    """Topologically sort modules for correct compilation order.

    Modules are sorted so dependencies are compiled before dependents.

    Args:
        params: dict with:
            - graph: dependency graph (module -> [dependencies])
            - modules: (optional) list of modules to sort (defaults to all)

    Returns:
        dict with:
            - order: list of modules in compile order (dependencies first)
            - cycles: list of detected dependency cycles
            - error: error message if there's a problem
    """
    graph = params.get("graph", {})
    modules = params.get("modules")

    if modules is None:
        # Collect all modules from graph
        allModules = set(graph.keys())
        for deps in graph.values():
            allModules.update(deps)
        modules = list(allModules)

    # Kahn's algorithm for topological sort
    # Build in-degree map
    inDegree = {mod: 0 for mod in modules}
    adjList = defaultdict(list)

    for mod, deps in graph.items():
        if mod not in inDegree:
            inDegree[mod] = 0
        for dep in deps:
            if dep in inDegree:  # Only count project modules
                adjList[dep].append(mod)  # dep -> mod (mod depends on dep)
                if mod in inDegree:
                    inDegree[mod] += 1

    # Find all modules with no dependencies (in-degree = 0)
    queue = [mod for mod, deg in inDegree.items() if deg == 0]
    order = []
    cycles = []

    while queue:
        # Sort to ensure deterministic order
        queue.sort()
        current = queue.pop(0)
        order.append(current)

        # Reduce in-degree for dependents
        for dependent in adjList.get(current, []):
            if dependent in inDegree:
                inDegree[dependent] -= 1
                if inDegree[dependent] == 0:
                    queue.append(dependent)

    # Check for cycles (modules that weren't processed)
    remaining = [mod for mod, deg in inDegree.items() if deg > 0]
    if remaining:
        # Detect cycle(s)
        visited = set()
        for mod in remaining:
            if mod not in visited:
                cycle = _detectCycle(mod, graph, visited)
                if cycle:
                    cycles.append(cycle)

    return {
        "order": order,
        "cycles": cycles,
        "error": f"Circular dependencies detected: {cycles}" if cycles else None
    }


def _detectCycle(start: str, graph: dict, visited: set) -> list:
    """Detect a cycle starting from a node using DFS."""
    path = []
    pathSet = set()

    def dfs(node):
        if node in pathSet:
            # Found cycle
            idx = path.index(node)
            return path[idx:] + [node]
        if node in visited:
            return None
        visited.add(node)
        path.append(node)
        pathSet.add(node)
        for dep in graph.get(node, []):
            result = dfs(dep)
            if result:
                return result
        path.pop()
        pathSet.remove(node)
        return None

    return dfs(start)


def transformImportPaths(params: dict) -> dict:
    """Transform project import paths for compiled output.

    Converts imports like 'from src.actions.scraper import X'
    to 'from lpp_output.decoded_scraper.src.decoded_scraper_compute import X'

    Args:
        params: dict with:
            - imports: list of import dicts from extractImports
            - moduleToOutput: dict mapping original module -> output module path
            - outputPrefix: prefix for output paths (e.g., 'lpp_output')

    Returns:
        dict with:
            - transformedImports: list of import statement strings
            - unmappedImports: list of imports that couldn't be mapped
    """
    imports = params.get("imports", [])
    moduleToOutput = params.get("moduleToOutput", {})
    outputPrefix = params.get("outputPrefix", "lpp_output")

    transformedImports = []
    unmappedImports = []

    for imp in imports:
        impType = imp.get("type", "")
        impModule = imp.get("module", "")
        impCategory = imp.get("category", "")
        impLevel = imp.get("level", 0)
        names = imp.get("names", [])

        # Skip stdlib and pip imports - they stay as-is
        if impCategory in ("stdlib", "pip"):
            if impType == "import":
                alias = imp.get("alias", "")
                if alias and alias != impModule:
                    transformedImports.append(f"import {impModule} as {alias}")
                else:
                    transformedImports.append(f"import {impModule}")
            elif impType == "from_import":
                nameStrs = []
                for n in names:
                    if n.get("alias") and n["alias"] != n["name"]:
                        nameStrs.append(f"{n['name']} as {n['alias']}")
                    else:
                        nameStrs.append(n["name"])
                if nameStrs:
                    transformedImports.append(f"from {impModule} import {', '.join(nameStrs)}")
            continue

        # Handle local/project imports
        if impCategory == "local" or impLevel > 0:
            # Check if we have a mapping for this module
            outputPath = moduleToOutput.get(impModule)

            if outputPath:
                if impType == "from_import":
                    nameStrs = []
                    for n in names:
                        if n.get("alias") and n["alias"] != n["name"]:
                            nameStrs.append(f"{n['name']} as {n['alias']}")
                        else:
                            nameStrs.append(n["name"])
                    if nameStrs:
                        transformedImports.append(f"from {outputPath} import {', '.join(nameStrs)}")
                else:
                    transformedImports.append(f"import {outputPath}")
            else:
                # No mapping - keep original and note it
                unmappedImports.append(imp)
                if impType == "import":
                    transformedImports.append(f"import {impModule}")
                elif impType == "from_import":
                    nameStrs = [n["name"] for n in names]
                    if impLevel > 0:
                        dots = "." * impLevel
                        if impModule:
                            transformedImports.append(f"from {dots}{impModule} import {', '.join(nameStrs)}")
                        else:
                            transformedImports.append(f"from {dots} import {', '.join(nameStrs)}")
                    else:
                        transformedImports.append(f"from {impModule} import {', '.join(nameStrs)}")

    return {
        "transformedImports": transformedImports,
        "unmappedImports": unmappedImports
    }


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
    "funcdec:visualizeModuleGraph": visualizeModuleGraph,
    # Dependency resolution
    "funcdec:resolveImportPath": resolveImportPath,
    "funcdec:buildProjectDependencyGraph": buildProjectDependencyGraph,
    "funcdec:getCompileOrder": getCompileOrder,
    "funcdec:transformImportPaths": transformImportPaths,
}
