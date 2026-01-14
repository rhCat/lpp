"""
COMPUTE units for the L++ Compliance Checker.

These are the pure computation functions that the compiled
compliance checker operator calls. All functions are hermetic.
"""

import json
import re
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional


def load_blueprint(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load an L++ blueprint from a JSON file for compliance checking."""
    path = params.get("path")
    if not path:
        return {"blueprint": None, "error": "No path provided"}

    try:
        path = Path(path)
        if not path.exists():
            return {"blueprint": None, "error": f"File not found: {path}"}

        with open(path) as f:
            blueprint = json.load(f)

        return {
            "blueprint": blueprint,
            "blueprint_path": str(path),
            "blueprint_name": blueprint.get("name", path.stem),
            "error": None
        }
    except Exception as e:
        return {"blueprint": None, "error": str(e)}


def load_policy(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load a single compliance policy and add to existing policies."""
    path = params.get("path")
    existing = params.get("policies", []) or []

    if not path:
        return {"policies": existing, "error": "No path provided"}

    try:
        path = Path(path)
        if not path.exists():
            return {"policies": existing, "error": f"File not found: {path}"}

        with open(path) as f:
            policy = json.load(f)

        # Validate policy structure
        if not policy.get("policy_id"):
            return {"policies": existing, "error": "Invalid policy: missing policy_id"}

        # Add to existing policies (avoid duplicates)
        policies = [p for p in existing if p.get(
            "policy_id") != policy.get("policy_id")]
        policies.append(policy)

        return {"policies": policies, "error": None}
    except Exception as e:
        return {"policies": existing, "error": str(e)}


def load_policies(params: Dict[str, Any]) -> Dict[str, Any]:
    """Load all compliance policies from a directory."""
    dirPath = params.get("dir_path")

    if not dirPath:
        # Default to built-in policies
        dirPath = Path(__file__).parent.parent / "policies"
    else:
        dirPath = Path(dirPath)

    if not dirPath.exists():
        return {"policies": [], "error": f"Directory not found: {dirPath}"}

    policies = []
    errors = []

    for pf in sorted(dirPath.glob("*.json")):
        try:
            with open(pf) as f:
                policy = json.load(f)
            if policy.get("policy_id"):
                policies.append(policy)
        except Exception as e:
            errors.append(f"{pf.name}: {e}")

    error = "; ".join(errors) if errors else None
    return {
        "policies": policies,
        "policies_dir": str(dirPath),
        "error": error
    }


def evaluate_rule(params: Dict[str, Any]) -> Dict[str, Any]:
    """Evaluate a single rule against a blueprint."""
    blueprint = params.get("blueprint", {})
    rule = params.get("rule", {})
    policy = params.get("policy", {})

    ruleType = rule.get("type")
    findings = []

    if ruleType == "state_exists":
        findings = _check_state_exists(blueprint, rule, policy)
    elif ruleType == "transition_requires_gate":
        findings = _check_transition_requires_gate(blueprint, rule, policy)
    elif ruleType == "transition_requires_action":
        findings = _check_transition_requires_action(blueprint, rule, policy)
    elif ruleType == "gate_expression_check":
        findings = _check_gate_expression(blueprint, rule, policy)
    elif ruleType == "action_type_required":
        findings = _check_action_type_required(blueprint, rule, policy)
    elif ruleType == "context_property_required":
        findings = _check_context_property(blueprint, rule, policy)
    elif ruleType == "no_direct_transition":
        findings = _check_no_direct_transition(blueprint, rule, policy)
    else:
        findings = [{
            "policy_id": policy.get("policy_id"),
            "rule_type": ruleType,
            "severity": "warning",
            "message": f"Unknown rule type: {ruleType}",
            "element": None,
            "passed": False
        }]

    return {"findings": findings}


def _check_state_exists(bp: dict, rule: dict, policy: dict) -> List[dict]:
    """Check if required states exist in the blueprint."""
    findings = []
    reqStates = rule.get("required_states", [])
    bpStates = set(bp.get("states", {}).keys())

    for reqState in reqStates:
        if reqState not in bpStates:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "state_exists",
                "severity": policy.get("severity", "error"),
                "message": f"Required state '{reqState}' not found",
                "element": {"type": "state", "id": reqState},
                "passed": False,
                "remediation": f"Add state '{reqState}' to the blueprint"
            })
        else:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "state_exists",
                "severity": "info",
                "message": f"Required state '{reqState}' exists",
                "element": {"type": "state", "id": reqState},
                "passed": True
            })

    return findings


def _check_transition_requires_gate(bp: dict, rule: dict, policy: dict) -> List[dict]:
    """Check if transitions matching a pattern have required gates."""
    findings = []
    condition = rule.get("condition", {})
    eventPattern = condition.get("on_event_pattern", ".*")
    reqGatePattern = rule.get("required_gate_pattern", ".*")

    eventRe = re.compile(eventPattern, re.IGNORECASE)
    gateRe = re.compile(reqGatePattern, re.IGNORECASE)
    bpGates = bp.get("gates", {})

    for trans in bp.get("transitions", []):
        event = trans.get("on_event", "")
        if not eventRe.match(event):
            continue

        # Check if transition has required gate
        tGates = trans.get("gates", [])
        if isinstance(trans.get("gate"), str):
            tGates = [trans.get("gate")] + tGates

        hasReqGate = False
        for g in tGates:
            if gateRe.match(g):
                hasReqGate = True
                break

        if not hasReqGate:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "transition_requires_gate",
                "severity": policy.get("severity", "error"),
                "message": f"Transition '{trans.get('id')}' ({event}) missing "
                f"required gate matching '{reqGatePattern}'",
                "element": {"type": "transition", "id": trans.get("id")},
                "passed": False,
                "remediation": f"Add a gate matching '{reqGatePattern}' to "
                f"transition '{trans.get('id')}'"
            })
        else:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "transition_requires_gate",
                "severity": "info",
                "message": f"Transition '{trans.get('id')}' has required gate",
                "element": {"type": "transition", "id": trans.get("id")},
                "passed": True
            })

    return findings


def _check_transition_requires_action(bp: dict, rule: dict, policy: dict) -> List[dict]:
    """Check if transitions matching a pattern have required actions."""
    findings = []
    condition = rule.get("condition", {})
    eventPattern = condition.get("on_event_pattern", ".*")
    reqActionPattern = rule.get("required_action_pattern", ".*")

    eventRe = re.compile(eventPattern, re.IGNORECASE)
    actionRe = re.compile(reqActionPattern, re.IGNORECASE)

    for trans in bp.get("transitions", []):
        event = trans.get("on_event", "")
        if not eventRe.match(event):
            continue

        tActions = trans.get("actions", [])
        hasReqAction = any(actionRe.match(a) for a in tActions)

        if not hasReqAction:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "transition_requires_action",
                "severity": policy.get("severity", "error"),
                "message": f"Transition '{trans.get('id')}' ({event}) missing "
                f"required action matching '{reqActionPattern}'",
                "element": {"type": "transition", "id": trans.get("id")},
                "passed": False,
                "remediation": f"Add an action matching '{reqActionPattern}' to "
                f"transition '{trans.get('id')}'"
            })
        else:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "transition_requires_action",
                "severity": "info",
                "message": f"Transition '{trans.get('id')}' has required action",
                "element": {"type": "transition", "id": trans.get("id")},
                "passed": True
            })

    return findings


def _check_gate_expression(bp: dict, rule: dict, policy: dict) -> List[dict]:
    """Check if gates contain required expression patterns."""
    findings = []
    gatePattern = rule.get("gate_pattern", ".*")
    reqExprPattern = rule.get("required_expression_pattern", ".*")

    gateRe = re.compile(gatePattern, re.IGNORECASE)
    exprRe = re.compile(reqExprPattern, re.IGNORECASE)

    for gid, gate in bp.get("gates", {}).items():
        if not gateRe.match(gid):
            continue

        expr = gate.get("expression", "")
        if not exprRe.search(expr):
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "gate_expression_check",
                "severity": policy.get("severity", "warning"),
                "message": f"Gate '{gid}' expression missing required pattern "
                f"'{reqExprPattern}'",
                "element": {"type": "gate", "id": gid},
                "passed": False,
                "remediation": f"Update gate '{gid}' expression to include "
                f"pattern matching '{reqExprPattern}'"
            })
        else:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "gate_expression_check",
                "severity": "info",
                "message": f"Gate '{gid}' contains required expression pattern",
                "element": {"type": "gate", "id": gid},
                "passed": True
            })

    return findings


def _check_action_type_required(bp: dict, rule: dict, policy: dict) -> List[dict]:
    """Check if blueprint has required action types."""
    findings = []
    reqTypes = rule.get("required_types", [])
    bpActions = bp.get("actions", {})

    existingTypes = set()
    for aid, action in bpActions.items():
        existingTypes.add(action.get("type"))

    for reqType in reqTypes:
        if reqType not in existingTypes:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "action_type_required",
                "severity": policy.get("severity", "warning"),
                "message": f"No action of type '{reqType}' found",
                "element": {"type": "action_type", "id": reqType},
                "passed": False,
                "remediation": f"Add at least one action of type '{reqType}'"
            })
        else:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "action_type_required",
                "severity": "info",
                "message": f"Action type '{reqType}' exists",
                "element": {"type": "action_type", "id": reqType},
                "passed": True
            })

    return findings


def _check_context_property(bp: dict, rule: dict, policy: dict) -> List[dict]:
    """Check if required context properties exist."""
    findings = []
    reqProps = rule.get("required_properties", [])
    ctxSchema = bp.get("context_schema", {})
    props = ctxSchema.get("properties", {})

    for reqProp in reqProps:
        if reqProp not in props:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "context_property_required",
                "severity": policy.get("severity", "error"),
                "message": f"Required context property '{reqProp}' not found",
                "element": {"type": "context_property", "id": reqProp},
                "passed": False,
                "remediation": f"Add property '{reqProp}' to context_schema"
            })
        else:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "context_property_required",
                "severity": "info",
                "message": f"Context property '{reqProp}' exists",
                "element": {"type": "context_property", "id": reqProp},
                "passed": True
            })

    return findings


def _check_no_direct_transition(bp: dict, rule: dict, policy: dict) -> List[dict]:
    """Check that there are no direct transitions between specified states."""
    findings = []
    fromStates = rule.get("from_states", [])
    toStates = rule.get("to_states", [])

    for trans in bp.get("transitions", []):
        fromS = trans.get("from")
        toS = trans.get("to")

        if fromS in fromStates and toS in toStates:
            findings.append({
                "policy_id": policy.get("policy_id"),
                "policy_name": policy.get("name"),
                "rule_type": "no_direct_transition",
                "severity": policy.get("severity", "error"),
                "message": f"Direct transition '{trans.get('id')}' from "
                f"'{fromS}' to '{toS}' is not allowed",
                "element": {"type": "transition", "id": trans.get("id")},
                "passed": False,
                "remediation": f"Add intermediate approval state between "
                f"'{fromS}' and '{toS}'"
            })

    if not findings:
        findings.append({
            "policy_id": policy.get("policy_id"),
            "policy_name": policy.get("name"),
            "rule_type": "no_direct_transition",
            "severity": "info",
            "message": "No prohibited direct transitions found",
            "element": None,
            "passed": True
        })

    return findings


def check_policy(params: Dict[str, Any]) -> Dict[str, Any]:
    """Check blueprint against a single policy."""
    blueprint = params.get("blueprint", {})
    policy = params.get("policy", {})

    allFindings = []

    for rule in policy.get("rules", []):
        result = evaluate_rule({
            "blueprint": blueprint,
            "rule": rule,
            "policy": policy
        })
        allFindings.extend(result.get("findings", []))

    return {"findings": allFindings, "error": None}


def check_all_policies(params: Dict[str, Any]) -> Dict[str, Any]:
    """Check blueprint against all loaded policies."""
    blueprint = params.get("blueprint", {})
    policies = params.get("policies", [])

    allFindings = []
    summary = {"error": 0, "warning": 0, "info": 0, "passed": 0, "failed": 0}

    for policy in policies:
        result = check_policy({"blueprint": blueprint, "policy": policy})
        pFindings = result.get("findings", [])
        allFindings.extend(pFindings)

        for f in pFindings:
            sev = f.get("severity", "info")
            if sev in summary:
                summary[sev] += 1
            if f.get("passed"):
                summary["passed"] += 1
            else:
                summary["failed"] += 1

    return {"findings": allFindings, "summary": summary, "error": None}


def calculate_score(params: Dict[str, Any]) -> Dict[str, Any]:
    """Calculate compliance score as percentage."""
    findings = params.get("findings", [])

    if not findings:
        return {"score": 100}

    # Filter out info-only findings
    checkFindings = [f for f in findings if f.get("severity") != "info"]
    if not checkFindings:
        return {"score": 100}

    passed = sum(1 for f in checkFindings if f.get("passed"))
    total = len(checkFindings)

    score = round((passed / total) * 100) if total > 0 else 100
    return {"score": score}


def generate_report(params: Dict[str, Any]) -> Dict[str, Any]:
    """Generate a comprehensive compliance report."""
    blueprint = params.get("blueprint", {})
    bpName = params.get("blueprint_name", blueprint.get("name", "Unknown"))
    policies = params.get("policies", [])
    findings = params.get("findings", [])
    summary = params.get("summary", {})

    # Calculate score
    scoreResult = calculate_score({"findings": findings})
    score = scoreResult["score"]

    # Group findings by severity
    byS = {"error": [], "warning": [], "info": []}
    for f in findings:
        sev = f.get("severity", "info")
        if sev in byS:
            byS[sev].append(f)

    # Group findings by policy
    byP = {}
    for f in findings:
        pid = f.get("policy_id", "unknown")
        if pid not in byP:
            byP[pid] = []
        byP[pid].append(f)

    report = {
        "title": f"Compliance Report: {bpName}",
        "generated_at": datetime.now().isoformat(),
        "blueprint": {
            "name": bpName,
            "id": blueprint.get("id"),
            "version": blueprint.get("version")
        },
        "policies_checked": [p.get("policy_id") for p in policies],
        "score": score,
        "summary": {
            "total_checks": len(findings),
            "passed": summary.get("passed", 0),
            "failed": summary.get("failed", 0),
            "by_severity": {
                "errors": len(byS["error"]),
                "warnings": len(byS["warning"]),
                "info": len(byS["info"])
            }
        },
        "status": "PASS" if score >= 80 else "WARNING" if score >= 50 else "FAIL",
        "findings_by_severity": byS,
        "findings_by_policy": byP,
        "remediations": [
            {
                "policy_id": f.get("policy_id"),
                "element": f.get("element"),
                "issue": f.get("message"),
                "fix": f.get("remediation")
            }
            for f in findings
            if not f.get("passed") and f.get("remediation")
        ]
    }

    return {"report": report, "score": score}


def export_report(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export compliance report to a file."""
    report = params.get("report", {})
    outPath = params.get("output_path", "./compliance_report.json")
    fmt = params.get("format", "json")

    try:
        outPath = Path(outPath)

        if fmt == "json":
            with open(outPath, "w") as f:
                json.dump(report, f, indent=2)
        elif fmt == "md" or fmt == "markdown":
            content = _format_report_markdown(report)
            outPath = outPath.with_suffix(".md")
            with open(outPath, "w") as f:
                f.write(content)
        elif fmt == "txt" or fmt == "text":
            content = _format_report_text(report)
            outPath = outPath.with_suffix(".txt")
            with open(outPath, "w") as f:
                f.write(content)
        else:
            return {"export_path": None, "error": f"Unknown format: {fmt}"}

        return {"export_path": str(outPath), "error": None}
    except Exception as e:
        return {"export_path": None, "error": str(e)}


def _format_report_markdown(report: dict) -> str:
    """Format report as Markdown."""
    lines = []
    lines.append(f"# {report.get('title', 'Compliance Report')}")
    lines.append("")
    lines.append(f"**Generated:** {report.get('generated_at', 'N/A')}")
    lines.append("")

    # Summary
    summary = report.get("summary", {})
    lines.append("## Summary")
    lines.append("")
    lines.append(f"| Metric | Value |")
    lines.append(f"|--------|-------|")
    lines.append(f"| Score | {report.get('score', 0)}% |")
    lines.append(f"| Status | {report.get('status', 'N/A')} |")
    lines.append(f"| Total Checks | {summary.get('total_checks', 0)} |")
    lines.append(f"| Passed | {summary.get('passed', 0)} |")
    lines.append(f"| Failed | {summary.get('failed', 0)} |")
    lines.append("")

    # Blueprint info
    bp = report.get("blueprint", {})
    lines.append("## Blueprint")
    lines.append("")
    lines.append(f"- **Name:** {bp.get('name', 'N/A')}")
    lines.append(f"- **ID:** {bp.get('id', 'N/A')}")
    lines.append(f"- **Version:** {bp.get('version', 'N/A')}")
    lines.append("")

    # Findings by severity
    byS = report.get("findings_by_severity", {})

    if byS.get("error"):
        lines.append("## Errors")
        lines.append("")
        for f in byS["error"]:
            lines.append(f"- **{f.get('policy_id')}**: {f.get('message')}")
            if f.get("remediation"):
                lines.append(f"  - Fix: {f.get('remediation')}")
        lines.append("")

    if byS.get("warning"):
        lines.append("## Warnings")
        lines.append("")
        for f in byS["warning"]:
            lines.append(f"- **{f.get('policy_id')}**: {f.get('message')}")
            if f.get("remediation"):
                lines.append(f"  - Fix: {f.get('remediation')}")
        lines.append("")

    # Remediations
    remediations = report.get("remediations", [])
    if remediations:
        lines.append("## Remediation Guide")
        lines.append("")
        for i, r in enumerate(remediations, 1):
            lines.append(f"{i}. **{r.get('policy_id')}** - {r.get('issue')}")
            lines.append(f"   - {r.get('fix')}")
        lines.append("")

    return "\n".join(lines)


def _format_report_text(report: dict) -> str:
    """Format report as plain text."""
    lines = []
    lines.append("=" * 60)
    lines.append(report.get("title", "Compliance Report").center(60))
    lines.append("=" * 60)
    lines.append("")

    lines.append(f"Score: {report.get('score', 0)}%")
    lines.append(f"Status: {report.get('status', 'N/A')}")
    lines.append(f"Generated: {report.get('generated_at', 'N/A')}")
    lines.append("")

    summary = report.get("summary", {})
    lines.append("-" * 40)
    lines.append("SUMMARY")
    lines.append("-" * 40)
    lines.append(f"  Total Checks: {summary.get('total_checks', 0)}")
    lines.append(f"  Passed: {summary.get('passed', 0)}")
    lines.append(f"  Failed: {summary.get('failed', 0)}")
    lines.append("")

    byS = report.get("findings_by_severity", {})
    if byS.get("error"):
        lines.append("-" * 40)
        lines.append("ERRORS")
        lines.append("-" * 40)
        for f in byS["error"]:
            lines.append(f"  [{f.get('policy_id')}] {f.get('message')}")
        lines.append("")

    if byS.get("warning"):
        lines.append("-" * 40)
        lines.append("WARNINGS")
        lines.append("-" * 40)
        for f in byS["warning"]:
            lines.append(f"  [{f.get('policy_id')}] {f.get('message')}")
        lines.append("")

    return "\n".join(lines)


# =============================================================================
# COMPUTE REGISTRY - Maps compute_unit names to functions
# =============================================================================

COMPLIANCE_REGISTRY = {
    ("compliance", "load_blueprint"): load_blueprint,
    ("compliance", "load_policy"): load_policy,
    ("compliance", "load_policies"): load_policies,
    ("compliance", "check_policy"): check_policy,
    ("compliance", "check_all_policies"): check_all_policies,
    ("compliance", "evaluate_rule"): evaluate_rule,
    ("compliance", "generate_report"): generate_report,
    ("compliance", "calculate_score"): calculate_score,
    ("compliance", "export_report"): export_report,
}

# Alias for standard import pattern
COMPUTE_REGISTRY = COMPLIANCE_REGISTRY
