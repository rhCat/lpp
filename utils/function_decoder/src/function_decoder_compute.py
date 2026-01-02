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
    if not tree:
        return {"exports": []}

    moduleName = Path(filePath).stem if filePath else "unknown"
    exports = []

    for node in ast.walk(tree):
        if isinstance(node, ast.FunctionDef):
            if not node.name.startswith("_"):
                exports.append({
                    "type": "function",
                    "name": node.name,
                    "module": moduleName,
                    "line": node.lineno,
                    "args": [a.arg for a in node.args.args],
                    "returns": _get_annotation(node.returns),
                    "docstring": ast.get_docstring(node),
                    "decorators": [_get_decorator_name(d) for d in node.decorator_list]
                })
        elif isinstance(node, ast.AsyncFunctionDef):
            if not node.name.startswith("_"):
                exports.append({
                    "type": "async_function",
                    "name": node.name,
                    "module": moduleName,
                    "line": node.lineno,
                    "args": [a.arg for a in node.args.args],
                    "returns": _get_annotation(node.returns),
                    "docstring": ast.get_docstring(node),
                    "decorators": [_get_decorator_name(d) for d in node.decorator_list]
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
                    "bases": [_get_name(b) for b in node.bases],
                    "methods": methods,
                    "docstring": ast.get_docstring(node)
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
    fanOut = len(set(imp["module"] for imp in imports if imp["category"] != "local"))

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
            "signature": _build_signature(exp)
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
                {"module": imp["module"], "category": imp["category"], "names": imp["names"]}
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


# Compute registry for L++ dispatcher
COMPUTE_REGISTRY = {
    "funcdec:loadFile": loadFile,
    "funcdec:parseAst": parseAst,
    "funcdec:extractExports": extractExports,
    "funcdec:extractImports": extractImports,
    "funcdec:traceInternalCalls": traceInternalCalls,
    "funcdec:traceExternalCalls": traceExternalCalls,
    "funcdec:computeCoupling": computeCoupling,
    "funcdec:generateModuleGraph": generateModuleGraph
}
