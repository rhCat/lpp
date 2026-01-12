# L++ Blueprint Schema Specification v0.1.3

## Overview

An L++ Blueprint is a JSON document that defines a complete, deterministic state machine for business logic execution. It reduces all software complexity to a "Trinity" of symbolic constructs: **Transitions, Gates, and Actions.**

---

## Root Structure

```json
{
  "$schema": "lpp/v0.1.3",
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
  "terminal_states": [ ],
  "terminal_contracts": { }
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
| `terminal_contracts` | object | No | Output guarantees per terminal state (for assembly composition) |

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

## Terminal Contracts (The Output Guarantee)

When a blueprint is used as a component in an assembly, the `terminal_contracts` define what outputs are guaranteed when reaching each terminal state. This enables assembly-level verification without expanding the component's internal state machine.

```json
"terminal_states": ["authenticated", "auth_failed", "mfa_required"],
"terminal_contracts": {
  "authenticated": {
    "description": "User successfully authenticated",
    "output_schema": {
      "token": { "type": "string", "non_null": true },
      "user_id": { "type": "string", "non_null": true },
      "permissions": { "type": "array", "items": { "type": "string" } },
      "expires_at": { "type": "string", "format": "iso8601" }
    },
    "invariants_guaranteed": ["token_valid", "user_exists"]
  },
  "auth_failed": {
    "description": "Authentication failed",
    "output_schema": {
      "error_code": {
        "type": "string",
        "enum": ["INVALID_CREDENTIALS", "ACCOUNT_LOCKED", "ACCOUNT_EXPIRED"],
        "non_null": true
      },
      "retry_allowed": { "type": "boolean", "non_null": true },
      "lockout_remaining": { "type": "number" }
    },
    "invariants_guaranteed": ["no_token_issued", "attempt_logged"]
  },
  "mfa_required": {
    "description": "Multi-factor authentication required",
    "output_schema": {
      "mfa_method": {
        "type": "string",
        "enum": ["sms", "totp", "email", "hardware_key"],
        "non_null": true
      },
      "challenge_id": { "type": "string", "non_null": true },
      "expires_in": { "type": "number" }
    },
    "invariants_guaranteed": ["partial_auth_valid", "challenge_created"]
  }
}
```

### Terminal Contract Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `description` | string | No | Human-readable description of this terminal |
| `output_schema` | object | Yes | JSON Schema defining guaranteed outputs |
| `invariants_guaranteed` | array | No | List of invariant IDs that hold at this terminal |

### Output Schema Property Fields

| Field | Type | Description |
|-------|------|-------------|
| `type` | string | JSON type: `string`, `number`, `boolean`, `array`, `object` |
| `non_null` | boolean | If true, this field is guaranteed to be present and non-null |
| `enum` | array | If present, value is restricted to these options |
| `format` | string | Format hint: `iso8601`, `uuid`, `email`, etc. |
| `items` | object | For arrays, schema of array items |

### Usage in Assembly

When this blueprint is composed in an assembly, the assembly can:

1. **Branch on terminal**: `auth._terminal == 'authenticated'`
2. **Access guaranteed outputs**: `auth.output.token` (guaranteed non-null if terminal is 'authenticated')
3. **Verify interface compatibility**: Assembly validator checks that `auth.output.token.type` matches `payment.input.auth_token.type`

---

## Determinism & Logic Stacking

1.  **Sequential Integrity**: Transitions are evaluated in the order they appear in the array. The first transition whose trigger matches and whose gates pass is the **only** path taken.
2.  **Atomic Mutation**: Context changes (MUTATE) occur after the GATE passes but before the TRANSITION pointer updates.
3.  **Logic Stacking**: Complex workflows are achieved by stacking blueprints. A `COMPUTE` action can invoke another L++ Operator, treating it as a single unit of work with a defined input/output contract.
4.  **Assembly Composition**: When used in an assembly, the blueprint's internal states are encapsulated. The assembly only sees terminal states and their contracts.

---

## Complete Example: Auth Blueprint with Terminal Contracts

```json
{
  "$schema": "lpp/v0.1.3",
  "id": "auth_skill",
  "name": "Authentication Service",
  "version": "1.0.0",
  "description": "Handles user authentication with MFA support",

  "context_schema": {
    "properties": {
      "username": { "type": "string" },
      "password_hash": { "type": "string" },
      "token": { "type": "string" },
      "user_id": { "type": "string" },
      "permissions": { "type": "array" },
      "error_code": { "type": "string" },
      "mfa_method": { "type": "string" },
      "challenge_id": { "type": "string" },
      "attempt_count": { "type": "number" }
    }
  },

  "states": {
    "idle": { "name": "Idle", "description": "Awaiting credentials" },
    "validating": { "name": "Validating", "description": "Checking credentials" },
    "checking_mfa": { "name": "Checking MFA", "description": "Determining if MFA needed" },
    "authenticated": { "name": "Authenticated", "description": "Success" },
    "auth_failed": { "name": "Failed", "description": "Authentication failed" },
    "mfa_required": { "name": "MFA Required", "description": "Awaiting second factor" }
  },

  "transitions": [
    { "id": "t_submit", "from": "idle", "to": "validating", "on_event": "SUBMIT_CREDENTIALS",
      "actions": ["a_store_creds"] },
    { "id": "t_valid", "from": "validating", "to": "checking_mfa", "on_event": "VALIDATE",
      "gates": ["g_creds_valid"], "actions": ["a_load_user"] },
    { "id": "t_invalid", "from": "validating", "to": "auth_failed", "on_event": "VALIDATE",
      "gates": ["g_creds_invalid"], "actions": ["a_set_error"] },
    { "id": "t_no_mfa", "from": "checking_mfa", "to": "authenticated", "on_event": "CHECK_MFA",
      "gates": ["g_mfa_not_required"], "actions": ["a_issue_token"] },
    { "id": "t_need_mfa", "from": "checking_mfa", "to": "mfa_required", "on_event": "CHECK_MFA",
      "gates": ["g_mfa_required"], "actions": ["a_create_challenge"] }
  ],

  "gates": {
    "g_creds_valid": { "type": "expression", "expression": "password_hash == stored_hash" },
    "g_creds_invalid": { "type": "expression", "expression": "password_hash != stored_hash" },
    "g_mfa_required": { "type": "expression", "expression": "user.mfa_enabled == True" },
    "g_mfa_not_required": { "type": "expression", "expression": "user.mfa_enabled != True" }
  },

  "actions": {
    "a_store_creds": { "type": "set", "target": "username", "value_from": "event.payload.username" },
    "a_load_user": { "type": "compute", "compute_unit": "auth:load_user",
      "input_map": { "username": "username" },
      "output_map": { "user_id": "id", "permissions": "permissions" } },
    "a_issue_token": { "type": "compute", "compute_unit": "auth:issue_token",
      "input_map": { "user_id": "user_id" },
      "output_map": { "token": "token" } },
    "a_set_error": { "type": "set", "target": "error_code", "value": "INVALID_CREDENTIALS" },
    "a_create_challenge": { "type": "compute", "compute_unit": "auth:create_mfa_challenge",
      "input_map": { "user_id": "user_id" },
      "output_map": { "challenge_id": "challenge_id", "mfa_method": "method" } }
  },

  "entry_state": "idle",
  "terminal_states": ["authenticated", "auth_failed", "mfa_required"],

  "terminal_contracts": {
    "authenticated": {
      "description": "User successfully authenticated",
      "output_schema": {
        "token": { "type": "string", "non_null": true },
        "user_id": { "type": "string", "non_null": true },
        "permissions": { "type": "array", "items": { "type": "string" } }
      },
      "invariants_guaranteed": ["token_valid", "user_authenticated"]
    },
    "auth_failed": {
      "description": "Authentication failed",
      "output_schema": {
        "error_code": { "type": "string", "non_null": true, "enum": ["INVALID_CREDENTIALS", "ACCOUNT_LOCKED"] }
      },
      "invariants_guaranteed": ["no_token_issued"]
    },
    "mfa_required": {
      "description": "Multi-factor authentication required to proceed",
      "output_schema": {
        "mfa_method": { "type": "string", "non_null": true, "enum": ["sms", "totp", "email"] },
        "challenge_id": { "type": "string", "non_null": true }
      },
      "invariants_guaranteed": ["partial_auth_valid"]
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
| 0.1.2 | 2025-12 | **Trinity Refinement**: Removed `FORK/JOIN` from schema; moved parallelism to Design Patterns. |
| 0.1.3 | 2025-01 | **Assembly Support**: Added `terminal_contracts` for component composition in assemblies. |
