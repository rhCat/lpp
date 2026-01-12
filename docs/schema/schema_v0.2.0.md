# L++ Blueprint Schema Specification v0.2.0

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
  "terminal_states": { }
}
```

### Root Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `$schema` | string | Yes | Must be `"lpp/v0.2.0"` |
| `id` | string | Yes | Unique blueprint identifier |
| `name` | string | Yes | Human-readable name |
| `version` | string | Yes | Blueprint version (semver) |
| `context_schema` | object | Yes | Defines the "Flange" (data properties) |
| `states` | object | Yes | State definitions (resting points) |
| `transitions` | array | Yes | Movement rules between states |
| `gates` | object | No | Boolean guard definitions |
| `actions` | object | Yes | Side-effect definitions |
| `entry_state` | string | Yes | The starting state ID |
| `terminal_states` | object | Yes | Terminal state definitions with contracts |

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

## Terminal States (The Formal Interface)

**Breaking Change in v0.2.0**: `terminal_states` is now an object, not an array. Each key is a terminal state ID, and its value is the **terminal contract** - the formal postconditions required for compositional TLAPS proofs.

### Basic Terminal (No Contract)

For simple blueprints that don't need compositional verification:

```json
"terminal_states": {
  "complete": {},
  "error": {}
}
```

### Terminal with Contract

For components used in assemblies, define output guarantees:

```json
"terminal_states": {
  "authenticated": {
    "description": "User successfully authenticated",
    "output_schema": {
      "token": { "type": "string", "non_null": true },
      "user_id": { "type": "string", "non_null": true },
      "permissions": { "type": "array", "items": { "type": "string" } }
    },
    "invariants_guaranteed": ["token_valid", "user_verified"]
  },
  "auth_failed": {
    "description": "Authentication failed",
    "output_schema": {
      "error_code": {
        "type": "string",
        "non_null": true,
        "enum": ["INVALID_CREDENTIALS", "ACCOUNT_LOCKED", "ACCOUNT_EXPIRED"]
      },
      "retry_allowed": { "type": "boolean", "non_null": true }
    },
    "invariants_guaranteed": ["no_token_issued", "attempt_logged"]
  }
}
```

### Terminal Contract Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `description` | string | No | Human-readable description of this terminal |
| `output_schema` | object | No | JSON Schema defining guaranteed outputs |
| `invariants_guaranteed` | array | No | List of invariant IDs proven to hold at this terminal |

### Output Schema Property Fields

| Field | Type | Description |
|-------|------|-------------|
| `type` | string | JSON type: `string`, `number`, `boolean`, `array`, `object` |
| `non_null` | boolean | If true, this field is guaranteed present and non-null |
| `enum` | array | If present, value is restricted to these options |
| `format` | string | Format hint: `iso8601`, `uuid`, `email`, etc. |
| `items` | object | For arrays, schema of array items |

### Why Terminal Contracts Matter

Terminal contracts are **formal postconditions** for TLAPS compositional proofs:

1. **Component A's contract**: "At terminal `done`, I guarantee `result != NULL`"
2. **Component B's precondition**: "I require `input != NULL`"
3. **TLAPS proves**: A→B composition is safe

Without contracts, you can verify components in isolation but cannot prove composition correctness.

---

## Determinism & Logic Stacking

1.  **Sequential Integrity**: Transitions are evaluated in the order they appear in the array. The first transition whose trigger matches and whose gates pass is the **only** path taken.
2.  **Atomic Mutation**: Context changes (MUTATE) occur after the GATE passes but before the TRANSITION pointer updates.
3.  **Logic Stacking**: Complex workflows are achieved by stacking blueprints. A `COMPUTE` action can invoke another L++ Operator, treating it as a single unit of work with a defined input/output contract.
4.  **Assembly Composition**: When used in an assembly, the blueprint's internal states are encapsulated. The assembly only sees terminal states and their contracts.

---

## Migration from v0.1.x

**Breaking Change**: `terminal_states` changed from array to object.

Before (v0.1.x):
```json
"terminal_states": ["complete", "error"]
```

After (v0.2.0):
```json
"terminal_states": {
  "complete": {},
  "error": {}
}
```

With contracts:
```json
"terminal_states": {
  "complete": {
    "output_schema": { "result": { "type": "string", "non_null": true } }
  },
  "error": {
    "output_schema": { "error_code": { "type": "string", "non_null": true } }
  }
}
```

---

## Complete Example

```json
{
  "$schema": "lpp/v0.2.0",
  "id": "auth_skill",
  "name": "Authentication Service",
  "version": "1.0.0",
  "description": "Handles user authentication",

  "context_schema": {
    "properties": {
      "username": { "type": "string" },
      "token": { "type": "string" },
      "user_id": { "type": "string" },
      "error_code": { "type": "string" }
    }
  },

  "states": {
    "idle": { "name": "Idle", "description": "Awaiting credentials" },
    "validating": { "name": "Validating", "description": "Checking credentials" },
    "authenticated": { "name": "Authenticated", "description": "Success" },
    "auth_failed": { "name": "Failed", "description": "Authentication failed" }
  },

  "transitions": [
    { "id": "t_submit", "from": "idle", "to": "validating", "on_event": "SUBMIT" },
    { "id": "t_valid", "from": "validating", "to": "authenticated", "on_event": "VALIDATE",
      "gates": ["g_creds_valid"], "actions": ["a_issue_token"] },
    { "id": "t_invalid", "from": "validating", "to": "auth_failed", "on_event": "VALIDATE",
      "gates": ["g_creds_invalid"], "actions": ["a_set_error"] }
  ],

  "gates": {
    "g_creds_valid": { "type": "expression", "expression": "validation_result == 'valid'" },
    "g_creds_invalid": { "type": "expression", "expression": "validation_result != 'valid'" }
  },

  "actions": {
    "a_issue_token": { "type": "compute", "compute_unit": "auth:issue_token",
      "input_map": { "username": "username" },
      "output_map": { "token": "token", "user_id": "user_id" } },
    "a_set_error": { "type": "set", "target": "error_code", "value": "INVALID_CREDENTIALS" }
  },

  "entry_state": "idle",

  "terminal_states": {
    "authenticated": {
      "description": "User successfully authenticated",
      "output_schema": {
        "token": { "type": "string", "non_null": true },
        "user_id": { "type": "string", "non_null": true }
      },
      "invariants_guaranteed": ["token_valid"]
    },
    "auth_failed": {
      "description": "Authentication failed",
      "output_schema": {
        "error_code": { "type": "string", "non_null": true }
      },
      "invariants_guaranteed": ["no_token_issued"]
    }
  }
}
```

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.1.0 | 2024-01 | Initial specification |
| 0.1.1 | 2024-12 | Standardized `on_event` and `context_schema` |
| 0.1.2 | 2025-12 | Trinity Refinement: Removed `FORK/JOIN` from schema |
| 0.1.3 | 2025-01 | Added `terminal_contracts` for assembly composition |
| 0.2.0 | 2025-01 | **Breaking**: Unified `terminal_states` as object with embedded contracts |
