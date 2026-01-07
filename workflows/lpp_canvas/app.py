#!/usr/bin/env python3
"""L++ Canvas Web GUI - Interactive blueprint studio."""
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "src"))
from flask import Flask, render_template, request, jsonify, send_file
from src.canvas_compute import COMPUTE_REGISTRY
from frame_py.compiler import compile_blueprint

HERE = Path(__file__).parent
app = Flask(__name__, template_folder=str(HERE / "templates"),
            static_folder=str(HERE / "static"))

operator = None
operator_mtime = 0


def getOperator():
    global operator, operator_mtime
    out = HERE / "results/lpp_canvas_compiled.py"
    src = HERE / "lpp_canvas.json"
    out.parent.mkdir(exist_ok=True)
    # Recompile if source is newer than compiled output
    needs_recompile = not out.exists() or src.stat().st_mtime > out.stat().st_mtime
    if needs_recompile:
        compile_blueprint(str(src), str(out))
    # Recreate operator if recompiled or not yet created
    current_mtime = out.stat().st_mtime if out.exists() else 0
    if operator is None or current_mtime > operator_mtime:
        import importlib.util
        spec = importlib.util.spec_from_file_location("op", out)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        reg = {tuple(k.split(":")): fn for k, fn in COMPUTE_REGISTRY.items()}
        operator = mod.create_operator(reg)
        operator_mtime = current_mtime
    return operator


@app.route("/")
def index():
    return render_template("canvas.html")


@app.route("/api/state", methods=["GET"])
def getState():
    op = getOperator()
    return jsonify({
        "state": op.state,
        "context": {k: v for k, v in op.context.items()
                    if v is not None and k not in ["graph_html"]}
    })


@app.route("/api/dispatch", methods=["POST"])
def dispatch():
    op = getOperator()
    data = request.json or {}
    event = data.get("event", "")
    payload = data.get("payload", {})
    for k, v in payload.items():
        op.context[k] = v
    try:
        op.dispatch(event, payload)
        return jsonify({
            "success": True,
            "state": op.state,
            "context": {k: v for k, v in op.context.items()
                        if v is not None and k not in ["graph_html"]}
        })
    except Exception as e:
        return jsonify({"success": False, "error": str(e)})


@app.route("/api/blueprint", methods=["GET"])
def getBlueprint():
    op = getOperator()
    return jsonify({
        "blueprint": op.context.get("blueprint"),
        "blueprint_json": op.context.get("blueprint_json")
    })


@app.route("/api/blueprint", methods=["POST"])
def setBlueprint():
    op = getOperator()
    data = request.json or {}
    bp = data.get("blueprint")
    if isinstance(bp, str):
        try:
            bp = json.loads(bp)
        except:
            return jsonify({"success": False, "error": "Invalid JSON"})
    op.context["blueprint"] = bp
    op.context["blueprint_json"] = json.dumps(bp, indent=2)
    op.context["graph_html"] = ""  # Clear graph when blueprint changes
    op.context["is_dirty"] = True
    # Transition to loaded state via SET_BLUEPRINT event (works from any state)
    if bp:
        op.dispatch("SET_BLUEPRINT", {})
    return jsonify({"success": True, "state": op.state})


@app.route("/api/graph", methods=["GET"])
def getGraph():
    op = getOperator()
    # Check for force refresh parameter
    force = request.args.get("force", "").lower() in ("1", "true", "yes")
    if force:
        op.context["graph_html"] = ""
    html = op.context.get("graph_html", "")
    blueprint = op.context.get("blueprint")
    print(f"[DEBUG] /api/graph: html_len={len(html) if html else 0}, "
          f"has_blueprint={bool(blueprint)}, state={op.state}, force={force}")
    if not html and blueprint:
        try:
            from src.canvas_compute import generateOutputs
            result = generateOutputs({"blueprint": blueprint})
            html = result.get("graph_html", "")
            op.context["graph_html"] = html
            op.context["mermaid"] = result.get("mermaid", "")
            print(f"[DEBUG] Generated graph: html_len={len(html)}")
        except Exception as e:
            print(f"[ERROR] Graph generation failed: {e}")
            import traceback
            traceback.print_exc()
    if not html:
        html = """<!DOCTYPE html><html><body style='background:#0d1117;color:#666;
        display:flex;align-items:center;justify-content:center;height:100vh;
        font-family:sans-serif;'><p>Load or create a blueprint to begin</p>
        </body></html>"""
    return html, 200, {"Content-Type": "text/html"}


@app.route("/api/validate", methods=["POST"])
def validate():
    op = getOperator()
    if op.state != "loaded":
        return jsonify({"success": False, "error": "No blueprint loaded"})
    op.dispatch("VALIDATE", {})
    op.dispatch("DONE", {})
    return jsonify({
        "success": True,
        "passed": op.context.get("tlc_passed", False),
        "result": op.context.get("tlc_result"),
        "errors": op.context.get("tlc_errors", [])
    })


@app.route("/api/analyze", methods=["POST"])
def analyze():
    op = getOperator()
    print(f"[DEBUG] analyze called: state={op.state}, has_blueprint={bool(op.context.get('blueprint'))}", flush=True)
    if op.state != "loaded":
        return jsonify({"success": False, "error": f"No blueprint loaded (state={op.state})"})
    print(f"[DEBUG] Before ANALYZE: path_count={op.context.get('path_count')}", flush=True)
    result1 = op.dispatch("ANALYZE", {})
    print(f"[DEBUG] After ANALYZE: state={op.state}, result={result1}, path_count={op.context.get('path_count')}", flush=True)
    result2 = op.dispatch("DONE", {})
    print(f"[DEBUG] After DONE: state={op.state}, result={result2}, path_count={op.context.get('path_count')}", flush=True)
    # Use 'or' to handle None values (not just missing keys)
    paths = op.context.get("paths") or []
    return jsonify({
        "success": True,
        "paths": paths[:20],
        "path_count": op.context.get("path_count") or 0,
        "states": op.context.get("states_list") or [],
        "state_count": op.context.get("state_count") or 0,
        "reachability": op.context.get("reachability") or {},
        "deadlocks": op.context.get("deadlocks") or []
    })


@app.route("/api/simulate", methods=["POST"])
def simulate():
    op = getOperator()
    data = request.json or {}
    action = data.get("action", "init")
    if action == "init":
        if op.state == "loaded":
            op.dispatch("SIMULATE", {})
        return jsonify({
            "success": True,
            "sim_state": op.context.get("sim_state"),
            "sim_context": op.context.get("sim_context"),
            "sim_history": op.context.get("sim_history", []),
            "available_events": op.context.get("sim_available_events", [])
        })
    elif action == "step":
        event = data.get("event", "")
        op.context["prompt"] = event
        op.dispatch("STEP", {"prompt": event})
        return jsonify({
            "success": True,
            "sim_state": op.context.get("sim_state"),
            "sim_context": op.context.get("sim_context"),
            "sim_history": op.context.get("sim_history", []),
            "available_events": op.context.get("sim_available_events", [])
        })
    elif action == "reset":
        op.dispatch("RESET", {})
        return jsonify({
            "success": True,
            "sim_state": op.context.get("sim_state"),
            "sim_context": op.context.get("sim_context"),
            "sim_history": op.context.get("sim_history", []),
            "available_events": op.context.get("sim_available_events", [])
        })
    elif action == "done":
        op.dispatch("DONE", {})
        return jsonify({"success": True, "state": op.state})
    return jsonify({"success": False, "error": "Unknown action"})


@app.route("/api/cluster", methods=["POST"])
def cluster():
    op = getOperator()
    if op.state != "loaded":
        return jsonify({"success": False, "error": "No blueprint loaded"})
    op.dispatch("CLUSTER", {})
    op.dispatch("DONE", {})
    return jsonify({
        "success": True,
        "clusters": op.context.get("clusters", []),
        "dependencies": op.context.get("dependencies", {}),
        "sorted_states": op.context.get("sorted_states", [])
    })


@app.route("/api/review", methods=["POST"])
def review():
    op = getOperator()
    data = request.json or {}
    action = data.get("action", "start")
    if action == "start":
        if op.state == "loaded":
            op.dispatch("REVIEW", {})
        return jsonify({
            "success": True,
            "notes": op.context.get("review_notes", []),
            "status": op.context.get("review_status"),
            "coverage": op.context.get("coverage", {})
        })
    elif action == "add_note":
        note = data.get("note", "")
        nodeId = data.get("node_id")
        op.context["prompt"] = note
        op.context["selected_node"] = nodeId
        op.dispatch("ADD_NOTE", {})
        return jsonify({
            "success": True,
            "notes": op.context.get("review_notes", [])
        })
    elif action == "approve":
        op.dispatch("APPROVE", {})
        return jsonify({"success": True, "status": "approved"})
    elif action == "reject":
        op.dispatch("REJECT", {})
        return jsonify({"success": True, "status": "rejected"})
    elif action == "done":
        op.dispatch("DONE", {})
        return jsonify({"success": True, "state": op.state})
    return jsonify({"success": False, "error": "Unknown action"})


@app.route("/api/llm", methods=["POST"])
def llm():
    op = getOperator()
    data = request.json or {}
    action = data.get("action", "query")
    if action == "enable":
        op.context["llm_enabled"] = True
        op.context["api_key"] = data.get("api_key", os.environ.get(
            "ANTHROPIC_API_KEY", ""))
        op.context["api_base"] = data.get("api_base",
                                          "https://api.anthropic.com")
        op.context["model"] = data.get("model", "claude-sonnet-4-20250514")
        return jsonify({"success": True, "enabled": True})
    elif action == "query":
        prompt = data.get("prompt", "")
        op.context["prompt"] = prompt
        if op.state == "loaded":
            op.dispatch("LLM_ASSIST", {})
        if op.state == "llm_assist":
            op.dispatch("QUERY", {"prompt": prompt})
        return jsonify({
            "success": True,
            "response": op.context.get("llm_response"),
            "suggestions": op.context.get("suggestions", [])
        })
    elif action == "apply":
        op.dispatch("APPLY", {})
        return jsonify({
            "success": True,
            "blueprint": op.context.get("blueprint")
        })
    elif action == "cancel":
        op.dispatch("CANCEL", {})
        return jsonify({"success": True, "state": op.state})
    return jsonify({"success": False, "error": "Unknown action"})


@app.route("/api/edit", methods=["POST"])
def edit():
    op = getOperator()
    data = request.json or {}
    action = data.get("action", "select")
    if action == "select":
        nodeId = data.get("node_id", "")
        nodeType = data.get("node_type", "state")
        op.context["selected_node"] = nodeId
        op.context["selected_type"] = nodeType
        if op.state == "loaded":
            op.dispatch("SELECT", {})
        return jsonify({
            "success": True,
            "node_data": op.context.get("node_data"),
            "edit_buffer": op.context.get("edit_buffer")
        })
    elif action == "apply":
        editBuffer = data.get("edit_buffer", {})
        op.context["edit_buffer"] = editBuffer
        op.dispatch("APPLY", {})
        return jsonify({
            "success": True,
            "blueprint": op.context.get("blueprint")
        })
    elif action == "delete":
        op.dispatch("DELETE", {})
        return jsonify({
            "success": True,
            "blueprint": op.context.get("blueprint")
        })
    elif action == "add_state":
        op.context["edit_buffer"] = data.get("state_data", {})
        op.dispatch("ADD_STATE", {})
        return jsonify({
            "success": True,
            "blueprint": op.context.get("blueprint")
        })
    elif action == "add_transition":
        op.context["edit_buffer"] = data.get("transition_data", {})
        op.dispatch("ADD_TRANSITION", {})
        return jsonify({
            "success": True,
            "blueprint": op.context.get("blueprint")
        })
    elif action == "add_gate":
        op.context["edit_buffer"] = data.get("gate_data", {})
        op.dispatch("ADD_GATE", {})
        return jsonify({
            "success": True,
            "blueprint": op.context.get("blueprint")
        })
    elif action == "add_action":
        op.context["edit_buffer"] = data.get("action_data", {})
        op.dispatch("ADD_ACTION", {})
        return jsonify({
            "success": True,
            "blueprint": op.context.get("blueprint")
        })
    elif action == "cancel":
        op.dispatch("CANCEL", {})
        return jsonify({"success": True, "state": op.state})
    return jsonify({"success": False, "error": "Unknown action"})


@app.route("/api/save", methods=["POST"])
def save():
    op = getOperator()
    data = request.json or {}
    path = data.get("path", "")
    if path:
        op.context["blueprint_path"] = path
    if op.state == "loaded" and op.context.get("is_dirty"):
        op.dispatch("SAVE", {})
        op.dispatch("DONE", {})
    return jsonify({
        "success": op.context.get("error") is None,
        "error": op.context.get("error")
    })


@app.route("/api/load", methods=["POST"])
def load():
    op = getOperator()
    data = request.json or {}
    path = data.get("path", "")
    op.context["blueprint_path"] = path
    op.context["graph_html"] = ""  # Clear old graph when loading new blueprint
    op.context["error"] = None  # Clear previous errors
    op.dispatch("LOAD", {})
    return jsonify({
        "success": op.context.get("error") is None,
        "state": op.state,
        "blueprint": op.context.get("blueprint"),
        "error": op.context.get("error")
    })


@app.route("/api/new", methods=["POST"])
def new():
    op = getOperator()
    op.context["graph_html"] = ""  # Clear graph for new blueprint
    op.dispatch("NEW", {})  # t_new now goes directly to loaded state
    return jsonify({
        "success": True,
        "state": op.state,
        "blueprint": op.context.get("blueprint")
    })


@app.route("/api/audit", methods=["GET"])
def audit():
    op = getOperator()
    return jsonify({
        "audit_log": op.context.get("audit_log", [])
    })


@app.route("/api/debug", methods=["GET"])
def debug():
    """Debug endpoint to check state."""
    op = getOperator()
    graph_html = op.context.get("graph_html") or ""
    return jsonify({
        "state": op.state,
        "has_blueprint": bool(op.context.get("blueprint")),
        "blueprint_name": op.context.get("blueprint", {}).get("name") if op.context.get("blueprint") else None,
        "graph_html_len": len(graph_html),
        "error": op.context.get("error")
    })


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5001))
    print(f"L++ Canvas running at http://localhost:{port}")
    app.run(host="0.0.0.0", port=port, debug=True)
