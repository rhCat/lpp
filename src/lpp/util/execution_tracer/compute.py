"""
COMPUTE units for the L++ Execution Tracer.

These are pure computation functions for structured logging and tracing
of L++ blueprint execution with OpenTelemetry-compatible output.
"""

import json
import uuid
from pathlib import Path
from typing import Any, Dict, List, Optional
from datetime import datetime, timezone


# =============================================================================
# CONSTANTS
# =============================================================================

SPAN_TYPES = [
    "blueprint",
    "state_enter",
    "state_exit",
    "transition",
    "gate",
    "action",
    "event",
    "context_mutation"
]

OUTPUT_FORMATS = ["otlp", "jsonl", "human", "timeline"]

OTLP_SERVICE_NAME = "lpp-execution-tracer"
OTLP_SERVICE_VERSION = "1.0.0"


# =============================================================================
# UTILITY FUNCTIONS
# =============================================================================

def _now_iso() -> str:
    """Return current UTC timestamp in ISO 8601 format."""
    return datetime.now(timezone.utc).isoformat()


def _now_ns() -> int:
    """Return current time in nanoseconds since epoch."""
    return int(datetime.now(timezone.utc).timestamp() * 1e9)


def _gen_id() -> str:
    """Generate a UUID4 hex string."""
    return uuid.uuid4().hex


def _gen_trace_id() -> str:
    """Generate a 32-character trace ID (16 bytes hex)."""
    return uuid.uuid4().hex


def _gen_span_id() -> str:
    """Generate a 16-character span ID (8 bytes hex)."""
    return uuid.uuid4().hex[:16]


def _parse_iso(ts: str) -> datetime:
    """Parse ISO 8601 timestamp to datetime."""
    if ts:
        try:
            return datetime.fromisoformat(ts.replace("Z", "+00:00"))
        except ValueError:
            pass
    return datetime.now(timezone.utc)


def _duration_ms(start: str, end: str) -> float:
    """Calculate duration in milliseconds between two ISO timestamps."""
    if not start or not end:
        return 0.0
    try:
        s = _parse_iso(start)
        e = _parse_iso(end)
        return (e - s).total_seconds() * 1000
    except Exception:
        return 0.0


def _get_current_span_id(active_spans: dict) -> Optional[str]:
    """Get the most recent active span ID as parent."""
    if not active_spans:
        return None
    # Return most recently started span
    latest = None
    latest_time = None
    for sid, span in active_spans.items():
        st = span.get("start_time", "")
        if latest_time is None or st > latest_time:
            latest = sid
            latest_time = st
    return latest


# =============================================================================
# TRACER INITIALIZATION
# =============================================================================

def init_tracer(params: Dict[str, Any]) -> Dict[str, Any]:
    """Initialize tracer with configuration."""
    output_format = params.get("output_format", "human")
    include_context = params.get("include_context", True)
    include_timing = params.get("include_timing", True)
    max_spans = params.get("max_spans", 10000)

    if output_format not in OUTPUT_FORMATS:
        output_format = "human"

    config = {
        "output_format": output_format,
        "include_context": include_context,
        "include_timing": include_timing,
        "max_spans": max_spans,
        "initialized_at": _now_iso()
    }

    return {
        "config": config,
        "output_format": output_format,
        "output": f"Tracer initialized with format: {output_format}"
    }


# =============================================================================
# TRACE LIFECYCLE
# =============================================================================

def start_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Start a new trace for a blueprint execution."""
    config = params.get("config") or {}
    blueprint_id = params.get("blueprint_id", "unknown")
    blueprint_name = params.get("blueprint_name", "Unknown Blueprint")
    metadata = params.get("metadata") or {}

    trace_id = _gen_trace_id()
    root_span_id = _gen_span_id()
    start_time = _now_iso()

    # Create root span
    root_span = {
        "span_id": root_span_id,
        "trace_id": trace_id,
        "parent_span_id": None,
        "name": f"blueprint:{blueprint_name}",
        "span_type": "blueprint",
        "start_time": start_time,
        "end_time": None,
        "duration_ms": None,
        "status": "OK",
        "attributes": {
            "lpp.blueprint.id": blueprint_id,
            "lpp.blueprint.name": blueprint_name,
            "lpp.blueprint.metadata": metadata
        },
        "events": []
    }

    return {
        "trace_id": trace_id,
        "root_span_id": root_span_id,
        "spans": [root_span],
        "active_spans": {root_span_id: root_span},
        "events": [],
        "blueprint_id": blueprint_id,
        "blueprint_name": blueprint_name,
        "start_time": start_time,
        "output": f"Trace started: {trace_id} for {blueprint_name}"
    }


def end_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """End the current trace."""
    trace_id = params.get("trace_id")
    root_span_id = params.get("root_span_id")
    spans = params.get("spans", [])
    active_spans = params.get("active_spans", {})
    start_time = params.get("start_time")

    end_time = _now_iso()

    # Close all active spans
    new_spans = []
    for span in spans:
        if span["span_id"] in active_spans:
            span = dict(span)
            span["end_time"] = end_time
            span["duration_ms"] = _duration_ms(span["start_time"], end_time)
        new_spans.append(span)

    # Find and update root span
    for i, span in enumerate(new_spans):
        if span["span_id"] == root_span_id:
            new_spans[i] = dict(span)
            new_spans[i]["end_time"] = end_time
            new_spans[i]["duration_ms"] = _duration_ms(start_time, end_time)
            break

    total_duration = _duration_ms(start_time, end_time)

    return {
        "spans": new_spans,
        "active_spans": {},
        "end_time": end_time,
        "output": f"Trace ended: {trace_id} ({total_duration:.2f}ms, "
        f"{len(new_spans)} spans)"
    }


def clear_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Clear all trace data."""
    return {
        "trace_id": None,
        "root_span_id": None,
        "spans": None,
        "active_spans": None,
        "events": None,
        "start_time": None,
        "end_time": None,
        "analysis_result": None,
        "formatted_output": None,
        "output": "Trace cleared"
    }


# =============================================================================
# SPAN RECORDING
# =============================================================================

def record_span(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record a complete span (already timed)."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    span_type = params.get("span_type", "generic")
    name = params.get("name", "unnamed")
    parent_span_id = params.get("parent_span_id")
    attributes = params.get("attributes") or {}
    start_time = params.get("start_time") or _now_iso()
    end_time = params.get("end_time") or _now_iso()
    duration_ms = params.get("duration_ms")

    if duration_ms is None:
        duration_ms = _duration_ms(start_time, end_time)

    span_id = _gen_span_id()

    span = {
        "span_id": span_id,
        "trace_id": trace_id,
        "parent_span_id": parent_span_id,
        "name": name,
        "span_type": span_type,
        "start_time": start_time,
        "end_time": end_time,
        "duration_ms": duration_ms,
        "status": "OK",
        "attributes": attributes,
        "events": []
    }

    new_spans = spans + [span]

    return {
        "spans": new_spans,
        "output": f"Recorded span: {name} ({duration_ms:.2f}ms)"
    }


def start_span(params: Dict[str, Any]) -> Dict[str, Any]:
    """Start a new span (for timed events)."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    active_spans = params.get("active_spans", {})
    span_type = params.get("span_type", "generic")
    name = params.get("name", "unnamed")
    parent_span_id = params.get("parent_span_id")
    attributes = params.get("attributes") or {}

    # Auto-parent to current active span if not specified
    if parent_span_id is None:
        parent_span_id = _get_current_span_id(active_spans)

    span_id = _gen_span_id()
    start_time = _now_iso()

    span = {
        "span_id": span_id,
        "trace_id": trace_id,
        "parent_span_id": parent_span_id,
        "name": name,
        "span_type": span_type,
        "start_time": start_time,
        "end_time": None,
        "duration_ms": None,
        "status": "UNSET",
        "attributes": attributes,
        "events": []
    }

    new_spans = spans + [span]
    new_active = dict(active_spans)
    new_active[span_id] = span

    return {
        "spans": new_spans,
        "active_spans": new_active,
        "output": f"Started span: {name} [{span_id[:8]}]"
    }


def end_span(params: Dict[str, Any]) -> Dict[str, Any]:
    """End an active span."""
    span_id = params.get("span_id")
    spans = params.get("spans", [])
    active_spans = params.get("active_spans", {})
    attributes = params.get("attributes") or {}
    status = params.get("status", "OK")

    if not span_id:
        # End most recent active span
        span_id = _get_current_span_id(active_spans)

    if not span_id or span_id not in active_spans:
        return {
            "spans": spans,
            "active_spans": active_spans,
            "output": f"No active span to end: {span_id}"
        }

    end_time = _now_iso()

    new_spans = []
    span_name = "unknown"
    duration = 0.0

    for span in spans:
        if span["span_id"] == span_id:
            span = dict(span)
            span["end_time"] = end_time
            span["duration_ms"] = _duration_ms(span["start_time"], end_time)
            span["status"] = status
            span["attributes"].update(attributes)
            span_name = span["name"]
            duration = span["duration_ms"]
        new_spans.append(span)

    new_active = dict(active_spans)
    if span_id in new_active:
        del new_active[span_id]

    return {
        "spans": new_spans,
        "active_spans": new_active,
        "output": f"Ended span: {span_name} ({duration:.2f}ms)"
    }


# =============================================================================
# SPECIALIZED RECORDING FUNCTIONS
# =============================================================================

def record_state_change(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record a state transition event."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    active_spans = params.get("active_spans", {})
    from_state = params.get("from_state")
    to_state = params.get("to_state")
    transition_id = params.get("transition_id")
    trigger_event = params.get("trigger_event")

    timestamp = _now_iso()
    parent_span_id = _get_current_span_id(active_spans)

    # Create transition span
    span_id = _gen_span_id()
    span = {
        "span_id": span_id,
        "trace_id": trace_id,
        "parent_span_id": parent_span_id,
        "name": f"transition:{from_state}->{to_state}",
        "span_type": "transition",
        "start_time": timestamp,
        "end_time": timestamp,
        "duration_ms": 0,
        "status": "OK",
        "attributes": {
            "lpp.transition.id": transition_id,
            "lpp.transition.from": from_state,
            "lpp.transition.to": to_state,
            "lpp.transition.event": trigger_event
        },
        "events": []
    }

    # Create event entry
    event = {
        "timestamp": timestamp,
        "type": "state_change",
        "trace_id": trace_id,
        "span_id": span_id,
        "attributes": {
            "from_state": from_state,
            "to_state": to_state,
            "transition_id": transition_id,
            "trigger_event": trigger_event
        }
    }

    return {
        "spans": spans + [span],
        "events": events + [event],
        "output": f"State: {from_state} -> {to_state} [{trigger_event}]"
    }


def record_gate_eval(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record a gate evaluation."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    active_spans = params.get("active_spans", {})
    gate_id = params.get("gate_id")
    expression = params.get("expression")
    result = params.get("result")
    input_values = params.get("input_values") or {}

    timestamp = _now_iso()
    parent_span_id = _get_current_span_id(active_spans)

    span_id = _gen_span_id()
    span = {
        "span_id": span_id,
        "trace_id": trace_id,
        "parent_span_id": parent_span_id,
        "name": f"gate:{gate_id}",
        "span_type": "gate",
        "start_time": timestamp,
        "end_time": timestamp,
        "duration_ms": 0,
        "status": "OK" if result else "ERROR",
        "attributes": {
            "lpp.gate.id": gate_id,
            "lpp.gate.expression": expression,
            "lpp.gate.result": result,
            "lpp.gate.inputs": input_values
        },
        "events": []
    }

    event = {
        "timestamp": timestamp,
        "type": "gate_eval",
        "trace_id": trace_id,
        "span_id": span_id,
        "attributes": {
            "gate_id": gate_id,
            "expression": expression,
            "result": result,
            "input_values": input_values
        }
    }

    result_str = "PASS" if result else "FAIL"

    return {
        "spans": spans + [span],
        "events": events + [event],
        "output": f"Gate {gate_id}: {result_str}"
    }


def record_action(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record an action execution."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    active_spans = params.get("active_spans", {})
    action_id = params.get("action_id")
    action_type = params.get("action_type", "unknown")
    input_map = params.get("input_map") or {}
    output_map = params.get("output_map") or {}
    duration_ms = params.get("duration_ms", 0)

    timestamp = _now_iso()
    parent_span_id = _get_current_span_id(active_spans)

    span_id = _gen_span_id()
    span = {
        "span_id": span_id,
        "trace_id": trace_id,
        "parent_span_id": parent_span_id,
        "name": f"action:{action_id}",
        "span_type": "action",
        "start_time": timestamp,
        "end_time": timestamp,
        "duration_ms": duration_ms,
        "status": "OK",
        "attributes": {
            "lpp.action.id": action_id,
            "lpp.action.type": action_type,
            "lpp.action.input_map": input_map,
            "lpp.action.output_map": output_map
        },
        "events": []
    }

    event = {
        "timestamp": timestamp,
        "type": "action",
        "trace_id": trace_id,
        "span_id": span_id,
        "attributes": {
            "action_id": action_id,
            "action_type": action_type,
            "duration_ms": duration_ms
        }
    }

    return {
        "spans": spans + [span],
        "events": events + [event],
        "output": f"Action {action_id} ({action_type}) [{duration_ms:.2f}ms]"
    }


def record_event(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record an event dispatch."""
    trace_id = params.get("trace_id")
    events = params.get("events", [])
    active_spans = params.get("active_spans", {})
    event_name = params.get("event_name")
    event_payload = params.get("event_payload") or {}

    timestamp = _now_iso()
    span_id = _get_current_span_id(active_spans)

    event = {
        "timestamp": timestamp,
        "type": "event_dispatch",
        "trace_id": trace_id,
        "span_id": span_id,
        "attributes": {
            "event_name": event_name,
            "event_payload": event_payload
        }
    }

    return {
        "events": events + [event],
        "output": f"Event: {event_name}"
    }


def record_context_change(params: Dict[str, Any]) -> Dict[str, Any]:
    """Record a context mutation."""
    trace_id = params.get("trace_id")
    events = params.get("events", [])
    active_spans = params.get("active_spans", {})
    key = params.get("key")
    old_value = params.get("old_value")
    new_value = params.get("new_value")

    timestamp = _now_iso()
    span_id = _get_current_span_id(active_spans)

    event = {
        "timestamp": timestamp,
        "type": "context_mutation",
        "trace_id": trace_id,
        "span_id": span_id,
        "attributes": {
            "key": key,
            "old_value": old_value,
            "new_value": new_value
        }
    }

    old_str = _truncate(str(old_value), 20)
    new_str = _truncate(str(new_value), 20)

    return {
        "events": events + [event],
        "output": f"Context: {key} = {old_str} -> {new_str}"
    }


def _truncate(s: str, max_len: int) -> str:
    """Truncate string with ellipsis."""
    if len(s) > max_len:
        return s[:max_len - 3] + "..."
    return s


# =============================================================================
# OUTPUT FORMATTING
# =============================================================================

def format_otlp(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format trace as OpenTelemetry Protocol JSON."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    blueprint_id = params.get("blueprint_id")
    blueprint_name = params.get("blueprint_name")
    start_time = params.get("start_time")
    end_time = params.get("end_time")

    # Convert to OTLP format
    otlp_spans = []
    for span in spans:
        otlp_span = {
            "traceId": span.get("trace_id", ""),
            "spanId": span.get("span_id", ""),
            "parentSpanId": span.get("parent_span_id", ""),
            "name": span.get("name", ""),
            "kind": 1,  # SPAN_KIND_INTERNAL
            "startTimeUnixNano": _iso_to_ns(span.get("start_time")),
            "endTimeUnixNano": _iso_to_ns(span.get("end_time")),
            "attributes": _attrs_to_otlp(span.get("attributes", {})),
            "status": {
                "code": 1 if span.get("status") == "OK" else 2,
                "message": span.get("status", "OK")
            },
            "events": [
                {
                    "timeUnixNano": _iso_to_ns(e.get("timestamp")),
                    "name": e.get("type", "event"),
                    "attributes": _attrs_to_otlp(e.get("attributes", {}))
                }
                for e in span.get("events", [])
            ]
        }
        otlp_spans.append(otlp_span)

    # Add trace-level events as span events on root
    for evt in events:
        otlp_event = {
            "timeUnixNano": _iso_to_ns(evt.get("timestamp")),
            "name": evt.get("type", "event"),
            "attributes": _attrs_to_otlp(evt.get("attributes", {}))
        }
        # Add to first (root) span
        if otlp_spans:
            otlp_spans[0]["events"].append(otlp_event)

    otlp_doc = {
        "resourceSpans": [{
            "resource": {
                "attributes": [
                    {"key": "service.name",
                     "value": {"stringValue": OTLP_SERVICE_NAME}},
                    {"key": "service.version",
                     "value": {"stringValue": OTLP_SERVICE_VERSION}},
                    {"key": "lpp.blueprint.id",
                     "value": {"stringValue": blueprint_id or ""}},
                    {"key": "lpp.blueprint.name",
                     "value": {"stringValue": blueprint_name or ""}}
                ]
            },
            "scopeSpans": [{
                "scope": {
                    "name": "lpp-tracer",
                    "version": "1.0.0"
                },
                "spans": otlp_spans
            }]
        }]
    }

    formatted = json.dumps(otlp_doc, indent=2)

    return {
        "formatted_output": formatted,
        "output": f"Formatted as OTLP JSON ({len(otlp_spans)} spans)"
    }


def _iso_to_ns(iso_str: str) -> int:
    """Convert ISO timestamp to nanoseconds."""
    if not iso_str:
        return 0
    try:
        dt = _parse_iso(iso_str)
        return int(dt.timestamp() * 1e9)
    except Exception:
        return 0


def _attrs_to_otlp(attrs: dict) -> list:
    """Convert attributes dict to OTLP attribute list."""
    result = []
    for k, v in attrs.items():
        if isinstance(v, bool):
            result.append({"key": k, "value": {"boolValue": v}})
        elif isinstance(v, int):
            result.append({"key": k, "value": {"intValue": str(v)}})
        elif isinstance(v, float):
            result.append({"key": k, "value": {"doubleValue": v}})
        elif isinstance(v, (dict, list)):
            result.append({"key": k,
                           "value": {"stringValue": json.dumps(v)}})
        else:
            result.append({"key": k, "value": {"stringValue": str(v)}})
    return result


def format_jsonl(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format trace as JSON Lines (one JSON object per line)."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])

    lines = []

    # Add spans
    for span in spans:
        line = {
            "type": "span",
            "trace_id": trace_id,
            "span_id": span.get("span_id"),
            "parent_span_id": span.get("parent_span_id"),
            "name": span.get("name"),
            "span_type": span.get("span_type"),
            "start_time": span.get("start_time"),
            "end_time": span.get("end_time"),
            "duration_ms": span.get("duration_ms"),
            "status": span.get("status"),
            "attributes": span.get("attributes", {})
        }
        lines.append(json.dumps(line, default=str))

    # Add events
    for evt in events:
        line = {
            "type": "event",
            "trace_id": trace_id,
            "span_id": evt.get("span_id"),
            "timestamp": evt.get("timestamp"),
            "event_type": evt.get("type"),
            "attributes": evt.get("attributes", {})
        }
        lines.append(json.dumps(line, default=str))

    formatted = "\n".join(lines)

    return {
        "formatted_output": formatted,
        "output": f"Formatted as JSON Lines ({len(lines)} lines)"
    }


def format_human(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format trace as human-readable text."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    blueprint_name = params.get("blueprint_name", "Unknown")
    start_time = params.get("start_time")
    end_time = params.get("end_time")

    total_duration = _duration_ms(start_time, end_time) if end_time else 0

    lines = [
        "=" * 70,
        f"  L++ Execution Trace: {blueprint_name}",
        "=" * 70,
        f"  Trace ID: {trace_id}",
        f"  Started:  {start_time}",
        f"  Ended:    {end_time or 'in progress'}",
        f"  Duration: {total_duration:.2f}ms",
        f"  Spans:    {len(spans)}",
        f"  Events:   {len(events)}",
        "=" * 70,
        "",
        "SPANS:",
        "-" * 70
    ]

    # Sort spans by start time
    sorted_spans = sorted(spans, key=lambda s: s.get("start_time", ""))

    for span in sorted_spans:
        name = span.get("name", "unknown")
        span_type = span.get("span_type", "generic")
        dur = span.get("duration_ms", 0) or 0
        status = span.get("status", "?")

        lines.append(
            f"  [{span_type:12}] {name:40} {dur:8.2f}ms [{status}]"
        )

        # Show key attributes
        attrs = span.get("attributes", {})
        for k, v in attrs.items():
            if k.startswith("lpp."):
                short_key = k.replace("lpp.", "")
                val_str = _truncate(str(v), 40)
                lines.append(f"                  {short_key}: {val_str}")

    lines.extend([
        "",
        "EVENTS:",
        "-" * 70
    ])

    # Sort events by timestamp
    sorted_events = sorted(events, key=lambda e: e.get("timestamp", ""))

    for evt in sorted_events:
        ts = evt.get("timestamp", "")
        if ts:
            ts = ts.split("T")[1][:12]  # Just time portion
        evt_type = evt.get("type", "unknown")
        attrs = evt.get("attributes", {})

        summary = ""
        if evt_type == "state_change":
            summary = f"{attrs.get('from_state')} -> {attrs.get('to_state')}"
        elif evt_type == "gate_eval":
            result = "PASS" if attrs.get("result") else "FAIL"
            summary = f"{attrs.get('gate_id')}: {result}"
        elif evt_type == "action":
            summary = f"{attrs.get('action_id')} ({attrs.get('action_type')})"
        elif evt_type == "event_dispatch":
            summary = attrs.get("event_name", "")
        elif evt_type == "context_mutation":
            summary = f"{attrs.get('key')} changed"

        lines.append(f"  [{ts}] {evt_type:18} {summary}")

    lines.extend(["", "=" * 70])

    formatted = "\n".join(lines)

    return {
        "formatted_output": formatted,
        "output": f"Formatted as human-readable ({len(lines)} lines)"
    }


def format_timeline(params: Dict[str, Any]) -> Dict[str, Any]:
    """Format trace as ASCII timeline visualization."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    blueprint_name = params.get("blueprint_name", "Unknown")
    start_time = params.get("start_time")
    end_time = params.get("end_time")

    if not spans:
        return {
            "formatted_output": "No spans to visualize",
            "output": "No spans to visualize"
        }

    total_duration = _duration_ms(start_time, end_time) if end_time else 1000
    if total_duration == 0:
        total_duration = 1  # Avoid division by zero

    width = 60  # Timeline width in characters

    lines = [
        "=" * 70,
        f"  Timeline: {blueprint_name}",
        f"  Trace: {trace_id}",
        f"  Total Duration: {total_duration:.2f}ms",
        "=" * 70,
        "",
        f"{'Span':<30} {'Timeline':>{width}} {'ms':>8}",
        "-" * 100
    ]

    # Sort spans by start time
    sorted_spans = sorted(spans, key=lambda s: s.get("start_time", ""))

    trace_start = _parse_iso(start_time) if start_time else None

    for span in sorted_spans:
        name = span.get("name", "unknown")[:28]
        span_start = span.get("start_time")
        span_end = span.get("end_time") or end_time
        dur = span.get("duration_ms", 0) or 0

        # Calculate position on timeline
        if trace_start and span_start:
            start_offset = _duration_ms(start_time, span_start)
            end_offset = _duration_ms(start_time, span_end) if span_end else \
                start_offset + dur
        else:
            start_offset = 0
            end_offset = dur

        # Convert to character positions
        start_pos = int((start_offset / total_duration) * width)
        end_pos = int((end_offset / total_duration) * width)

        start_pos = max(0, min(width - 1, start_pos))
        end_pos = max(start_pos + 1, min(width, end_pos))

        # Build timeline bar
        bar = ["."] * width
        bar_char = "#"

        # Use different chars for different span types
        span_type = span.get("span_type", "")
        if span_type == "transition":
            bar_char = ">"
        elif span_type == "gate":
            bar_char = "?"
        elif span_type == "action":
            bar_char = "*"
        elif span_type == "blueprint":
            bar_char = "="

        for i in range(start_pos, end_pos):
            bar[i] = bar_char

        timeline_str = "".join(bar)
        lines.append(f"{name:<30} |{timeline_str}| {dur:>7.2f}")

    # Add legend
    lines.extend([
        "",
        "-" * 100,
        "Legend: = blueprint  > transition  ? gate  * action  # other",
        "",
        "Events:",
        "-" * 100
    ])

    # Show events on timeline
    sorted_events = sorted(events, key=lambda e: e.get("timestamp", ""))

    for evt in sorted_events[:20]:  # Limit to 20 events
        ts = evt.get("timestamp")
        evt_type = evt.get("type", "unknown")[:15]

        if trace_start and ts:
            offset = _duration_ms(start_time, ts)
            pos = int((offset / total_duration) * width)
            pos = max(0, min(width - 1, pos))
        else:
            pos = 0

        # Build marker line
        marker = [" "] * width
        marker[pos] = "v"
        marker_str = "".join(marker)

        lines.append(f"{evt_type:<30} |{marker_str}|")

    lines.append("=" * 70)

    formatted = "\n".join(lines)

    return {
        "formatted_output": formatted,
        "output": f"Formatted as timeline ({len(sorted_spans)} spans)"
    }


# =============================================================================
# EXPORT
# =============================================================================

def export_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Export trace to a file."""
    formatted_output = params.get("formatted_output")
    output_format = params.get("output_format", "human")
    path = params.get("path")
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    blueprint_id = params.get("blueprint_id")
    blueprint_name = params.get("blueprint_name")
    start_time = params.get("start_time")
    end_time = params.get("end_time")

    # Generate default path if not provided
    if not path:
        ext_map = {
            "otlp": "json",
            "jsonl": "jsonl",
            "human": "txt",
            "timeline": "txt"
        }
        ext = ext_map.get(output_format, "txt")
        path = f"trace_{trace_id[:8]}.{ext}"

    # Format if not already formatted
    if not formatted_output:
        format_params = {
            "trace_id": trace_id,
            "spans": spans,
            "events": events,
            "blueprint_id": blueprint_id,
            "blueprint_name": blueprint_name,
            "start_time": start_time,
            "end_time": end_time
        }

        if output_format == "otlp":
            result = format_otlp(format_params)
        elif output_format == "jsonl":
            result = format_jsonl(format_params)
        elif output_format == "timeline":
            result = format_timeline(format_params)
        else:
            result = format_human(format_params)

        formatted_output = result.get("formatted_output", "")

    # Write to file
    try:
        path_obj = Path(path)
        path_obj.parent.mkdir(parents=True, exist_ok=True)
        path_obj.write_text(formatted_output)

        return {
            "export_path": str(path_obj.absolute()),
            "output": f"Exported trace to: {path_obj.absolute()}"
        }
    except Exception as e:
        return {
            "export_path": None,
            "output": f"Export failed: {e}"
        }


# =============================================================================
# ANALYSIS
# =============================================================================

def analyze_trace(params: Dict[str, Any]) -> Dict[str, Any]:
    """Analyze trace data for insights."""
    trace_id = params.get("trace_id")
    spans = params.get("spans", [])
    events = params.get("events", [])
    start_time = params.get("start_time")
    end_time = params.get("end_time")

    total_duration = _duration_ms(start_time, end_time) if end_time else 0

    # Collect statistics
    span_count = len(spans)
    event_count = len(events)

    # Analyze by span type
    by_type = {}
    for span in spans:
        span_type = span.get("span_type", "unknown")
        if span_type not in by_type:
            by_type[span_type] = {"count": 0, "total_ms": 0, "spans": []}
        by_type[span_type]["count"] += 1
        dur = span.get("duration_ms", 0) or 0
        by_type[span_type]["total_ms"] += dur
        by_type[span_type]["spans"].append(span)

    # Find slowest spans
    sorted_by_duration = sorted(
        spans,
        key=lambda s: s.get("duration_ms", 0) or 0,
        reverse=True
    )
    slowest = sorted_by_duration[:5]

    # Analyze state transitions
    state_changes = [e for e in events if e.get("type") == "state_change"]
    state_visits = {}
    for sc in state_changes:
        attrs = sc.get("attributes", {})
        to_state = attrs.get("to_state")
        if to_state:
            state_visits[to_state] = state_visits.get(to_state, 0) + 1

    # Analyze gate results
    gate_evals = [e for e in events if e.get("type") == "gate_eval"]
    gate_stats = {"pass": 0, "fail": 0}
    for ge in gate_evals:
        attrs = ge.get("attributes", {})
        if attrs.get("result"):
            gate_stats["pass"] += 1
        else:
            gate_stats["fail"] += 1

    # Analyze events
    event_types = {}
    for evt in events:
        evt_type = evt.get("type", "unknown")
        event_types[evt_type] = event_types.get(evt_type, 0) + 1

    analysis = {
        "trace_id": trace_id,
        "total_duration_ms": total_duration,
        "span_count": span_count,
        "event_count": event_count,
        "spans_by_type": {
            k: {"count": v["count"], "total_ms": v["total_ms"]}
            for k, v in by_type.items()
        },
        "slowest_spans": [
            {
                "name": s.get("name"),
                "type": s.get("span_type"),
                "duration_ms": s.get("duration_ms", 0)
            }
            for s in slowest
        ],
        "state_visits": state_visits,
        "gate_stats": gate_stats,
        "event_types": event_types
    }

    # Format output
    lines = [
        "=" * 60,
        "  Trace Analysis",
        "=" * 60,
        f"  Trace ID:    {trace_id}",
        f"  Duration:    {total_duration:.2f}ms",
        f"  Spans:       {span_count}",
        f"  Events:      {event_count}",
        "",
        "  SPANS BY TYPE:",
        "  " + "-" * 50
    ]

    for st, stats in by_type.items():
        avg = stats["total_ms"] / stats["count"] if stats["count"] else 0
        lines.append(
            f"    {st:15} count: {stats['count']:4}  "
            f"total: {stats['total_ms']:8.2f}ms  avg: {avg:.2f}ms"
        )

    lines.extend([
        "",
        "  SLOWEST SPANS:",
        "  " + "-" * 50
    ])

    for s in slowest:
        lines.append(
            f"    {s.get('name', 'unknown')[:35]:35} "
            f"{s.get('duration_ms', 0):8.2f}ms"
        )

    lines.extend([
        "",
        "  STATE VISITS:",
        "  " + "-" * 50
    ])

    for state, count in sorted(state_visits.items(),
                               key=lambda x: x[1], reverse=True):
        lines.append(f"    {state:30} {count:4} visits")

    lines.extend([
        "",
        "  GATE EVALUATION:",
        "  " + "-" * 50,
        f"    Pass: {gate_stats['pass']}  Fail: {gate_stats['fail']}",
        "",
        "  EVENT TYPES:",
        "  " + "-" * 50
    ])

    for evt_type, count in sorted(event_types.items(),
                                  key=lambda x: x[1], reverse=True):
        lines.append(f"    {evt_type:30} {count:4}")

    lines.append("=" * 60)

    return {
        "analysis_result": analysis,
        "output": "\n".join(lines)
    }


# =============================================================================
# STATUS RENDERING
# =============================================================================

def render_status(params: Dict[str, Any]) -> Dict[str, Any]:
    """Render current tracer status."""
    trace_id = params.get("trace_id")
    blueprint_name = params.get("blueprint_name", "N/A")
    spans = params.get("spans") or []
    events = params.get("events") or []
    active_spans = params.get("active_spans") or {}
    start_time = params.get("start_time")
    output_format = params.get("output_format", "human")

    lines = [
        "=" * 50,
        "  L++ Execution Tracer Status",
        "=" * 50,
        f"  Trace ID:      {trace_id or 'None'}",
        f"  Blueprint:     {blueprint_name}",
        f"  Format:        {output_format}",
        f"  Started:       {start_time or 'N/A'}",
        f"  Spans:         {len(spans)}",
        f"  Active Spans:  {len(active_spans)}",
        f"  Events:        {len(events)}",
    ]

    if active_spans:
        lines.append("")
        lines.append("  Active Spans:")
        for sid, span in list(active_spans.items())[:5]:
            lines.append(f"    - {span.get('name', 'unknown')} [{sid[:8]}]")

    lines.append("=" * 50)

    return {
        "output": "\n".join(lines)
    }


# =============================================================================
# COMPUTE REGISTRY
# =============================================================================

COMPUTE_REGISTRY = {
    "tracer:init_tracer": init_tracer,
    "tracer:start_trace": start_trace,
    "tracer:end_trace": end_trace,
    "tracer:clear_trace": clear_trace,
    "tracer:record_span": record_span,
    "tracer:start_span": start_span,
    "tracer:end_span": end_span,
    "tracer:record_state_change": record_state_change,
    "tracer:record_gate_eval": record_gate_eval,
    "tracer:record_action": record_action,
    "tracer:record_event": record_event,
    "tracer:record_context_change": record_context_change,
    "tracer:format_otlp": format_otlp,
    "tracer:format_jsonl": format_jsonl,
    "tracer:format_human": format_human,
    "tracer:format_timeline": format_timeline,
    "tracer:export_trace": export_trace,
    "tracer:analyze_trace": analyze_trace,
    "tracer:render_status": render_status,
}
