# L++ Blueprint Schema Specification v0.1.2

## Overview

An L++ Blueprint is a JSON document that defines a complete, deterministic state machine for business logic execution. It reduces all software complexity to a "Trinity" of symbolic constructs: **Transitions, Gates, and Actions.**

---

## Root Structure

```json
{
  "$schema": "lpp/v0.2.0",
  "id": "string",
  "name": "string",
  "version": "string",
  "description": "string",
  "context_schema": {
    "properties": { }
  },
  "states": { },
  "transitions": [ ],
  "gates": { },
  "actions": { },
  "display": {
    "rules": [ ]
  },
  "entry_state": "string",
  "terminal_states": [ ]
}
```

### Root Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `$schema` | string | Yes | Schema version identifier |
| `id` | string | Yes | Unique blueprint identifier |
| `name` | string | Yes | Human-readable name |
| `version` | string | Yes | Blueprint version (semver) |
| `context_schema` | object | Yes | Defines the "Flange" (data properties) |
| `states` | object | Yes | State definitions (resting points) |
| `transitions` | array | Yes | Movement rules between states |
| `gates` | object | No | Boolean guard definitions |
| `actions` | object | Yes | Side-effect definitions |
| `entry_state` | string | Yes | The starting state ID |
| `terminal_states` | array | Yes | List of exit state IDs (can be `[]`) |

---

## The Atomic Operators

L++ logic is executed via four underlying atoms, represented in the schema by three primary constructs:

### 1. TRANSITION (The Navigator)

Moves the execution pointer from one state to another.

```json
{
  "id": "t_unique_id",
  "from": "state_a",
  "to": "state_b",
  "on_event": "EVENT_NAME",
  "gates": ["gate_id"],
  "actions": ["action_id"]
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | Unique ID for audit and TLA+ verification |
| `from` | string | Yes | Source state ID (or `"*"` for global) |
| `to` | string | Yes | Target state ID |
| `on_event` | string | Yes | Triggering event name |
| `gates` | array | No | List of Gates that must all pass |
| `actions` | array | No | List of Actions to execute during move |

### 2. GATE (The Judge)

A deterministic boolean check that guards a transition.

```json
{
  "gate_id": {
    "type": "expression | compute",
    "expression": "a > 10 and b is not None",
    "compute_unit": "namespace:op_id"
  }
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | enum | Yes | `"expression"` or `"compute"` |
| `expression` | string | Conditional | L++ Expression (required for type=expression) |
| `compute_unit` | string | Conditional | External unit ID (required for type=compute) |

### 3. ACTION (The Scribe & Messenger)

Side-effects that mutate context or interact with the external world.

| Action Type | Description | Key Fields |
|-------------|-------------|------------|
| **SET** | Mutates internal context | `target`, `value` OR `value_from` |
| **COMPUTE** | Calls a hermetic compute unit | `compute_unit`, `input_map`, `output_map` |
| **EMIT** | Sends an event to the environment | `event`, `payload_map` |

---

## Context Schema (The Flange)

The `context_schema` defines the data interface. All properties are initialized to `null` unless a default is provided.

```json
"context_schema": {
  "properties": {
    "status": { "type": "string", "enum": ["active", "error"] },
    "count": { "type": "number" }
  }
}
```

---

## Determinism & Logic Stacking

1.  **Sequential Integrity**: Transitions are evaluated in the order they appear in the array. The first transition whose trigger matches and whose gates pass is the **only** path taken.
2.  **Atomic Mutation**: Context changes (MUTATE) occur after the GATE passes but before the TRANSITION pointer updates.
3.  **Logic Stacking**: Complex workflows (like Parallelism) are achieved by stacking these units. A `COMPUTE` action can invoke another L++ Operator, treating it as a single unit of work with a defined input/output contract.

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.1.0 | 2024-01 | Initial specification |
| 0.1.1 | 2024-12 | Standardized `on_event` and `context_schema` |
| 0.1.2 | 2025-12 | **Trinity Refinement**: Removed `FORK/JOIN` from schema; moved parallelism to Design Patterns. |