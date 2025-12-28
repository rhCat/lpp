# L++ Blueprint Schema Specification v0.1

## Overview

An L++ Blueprint is a JSON document that defines a complete, deterministic state machine for business logic execution. This document specifies the canonical syntax and semantics.

---

## Root Structure

```json
{
  "$schema": "lpp/v0.1",
  "id": "string",
  "name": "string",
  "version": "string",
  "description": "string",
  "context_schema": { },
  "states": { },
  "transitions": [ ],
  "gates": { },
  "actions": { },
  "display": { },
  "entry_state": "string",
  "terminal_states": [ ]
}
```

### Root Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `$schema` | string | Yes | Schema version identifier |
| `id` | string | Yes | Unique blueprint identifier (UUID recommended) |
| `name` | string | Yes | Human-readable name |
| `version` | string | Yes | Blueprint version (semver) |
| `description` | string | No | Blueprint description |
| `context_schema` | object | Yes | Context properties schema (for initialization) |
| `states` | object | Yes | State definitions |
| `transitions` | array | Yes | Transition rules |
| `gates` | object | No | Gate (guard condition) definitions |
| `actions` | object | Yes | Action definitions |
| `display` | object | No | Display rules for UI rendering |
| `entry_state` | string | Yes | Initial state identifier |
| `terminal_states` | array | Yes | List of terminal state identifiers (can be empty `[]`) |

---

## The Four Atomic Operators

L++ reduces all logic to four fundamental operations:

### 1. TRANSITION

Moves the machine from one state to another.

```json
{
  "id": "t1",
  "from": "state_a",
  "to": "state_b",
  "on_event": "EVENT_NAME",
  "gates": ["gate_id"],
  "actions": ["action_id"]
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `id` | string | Yes | Unique transition identifier (for audit trails) |
| `from` | string | Yes | Source state ID (or `"*"` for any state) |
| `to` | string | Yes | Target state ID |
| `on_event` | string | Yes | Event name that triggers this transition |
| `gates` | array | No | Gate IDs to evaluate (all must pass) |
| `actions` | array | No | Action IDs to execute on transition |

### 2. GATE

A boolean guard condition that must pass for a transition to occur.

```json
{
  "gate_id": {
    "type": "expression | compute",
    "expression": "context.amount > 1000",
    "compute_unit": "validate_user",
    "description": "Check if amount exceeds threshold"
  }
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | enum | Yes | `"expression"` (inline eval) or `"compute"` (external unit) |
| `expression` | string | Conditional | Boolean expression (required if type=expression) |
| `compute_unit` | string | Conditional | Compute unit ID (required if type=compute) |
| `description` | string | No | Human-readable description |

#### Expression Syntax

Gates support a minimal expression language:

```
// Comparisons
context.field == value
context.field != value
context.field > value
context.field >= value
context.field < value
context.field <= value

// Logical operators
expr AND expr
expr OR expr
NOT expr

// Membership
context.field IN [value1, value2]
context.field NOT IN [value1, value2]

// Null checks
context.field IS NULL
context.field IS NOT NULL
```

### 3. ACTION

A side-effect operation executed during a transition.

```json
{
  "action_id": {
    "type": "set | compute | emit | fork",
    "target": "context.field",
    "value": "new_value",
    "compute_unit": "process_payment",
    "input_map": { },
    "output_map": { },
    "description": "Update field value"
  }
}
```

#### Action Types

**SET** - Direct context mutation
```json
{
  "set_status": {
    "type": "set",
    "target": "context.status",
    "value": "approved"
  }
}
```

**COMPUTE** - Invoke external compute unit
```json
{
  "call_api": {
    "type": "compute",
    "compute_unit": "payment_processor",
    "input_map": {
      "amount": "context.order.total",
      "currency": "context.order.currency"
    },
    "output_map": {
      "context.payment.transaction_id": "result.tx_id",
      "context.payment.status": "result.status"
    }
  }
}
```

**EMIT** - Emit an event (internal or external)
```json
{
  "notify": {
    "type": "emit",
    "event": "ORDER_COMPLETED",
    "payload_map": {
      "order_id": "context.order.id"
    }
  }
}
```

### 4. FORK/JOIN

Parallel execution branches that must synchronize.

```json
{
  "fork_id": {
    "type": "fork",
    "branches": [
      {
        "id": "branch_a",
        "actions": ["action_1", "action_2"]
      },
      {
        "id": "branch_b", 
        "actions": ["action_3"]
      }
    ],
    "join": "all | any | n_of_m",
    "join_count": 2,
    "timeout_ms": 30000,
    "on_timeout": "abort | continue"
  }
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `type` | string | Yes | Must be `"fork"` |
| `branches` | array | Yes | Parallel execution branches |
| `join` | string | Yes | Join strategy: `all`, `any`, `n_of_m` |
| `join_count` | number | Conditional | Required count for `n_of_m` |
| `timeout_ms` | number | No | Timeout in milliseconds |
| `on_timeout` | string | No | Timeout behavior |

---

## States

```json
{
  "states": {
    "state_id": {
      "name": "Human Readable Name",
      "description": "What this state represents",
      "on_enter": ["action_id"],
      "on_exit": ["action_id"],
      "metadata": { }
    }
  }
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `name` | string | Yes | Human-readable state name |
| `description` | string | No | State description |
| `on_enter` | array | No | Actions to execute when entering state |
| `on_exit` | array | No | Actions to execute when leaving state |
| `metadata` | object | No | Arbitrary metadata for tooling |

---

## Context Schema

The context schema defines properties that will be initialized (all to `null` by default) and tracked:

```json
{
  "context_schema": {
    "properties": {
      "user_id": { "type": "string" },
      "amount": { "type": "number" },
      "status": { "type": "string", "enum": ["pending", "approved", "rejected"] }
    }
  }
}
```

All properties are initialized to `null` at startup. The compiler uses this to build the initial context.

---

## Display Rules

Display rules define how to render the current state for UI purposes. Rules are evaluated in order; first matching gate wins.

```json
{
  "display": {
    "rules": [
      { "gate": "is_error", "template": "ERROR: {error}" },
      { "gate": "has_value", "template": "{value}" },
      { "template": "0" }
    ]
  }
}
```

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `rules` | array | Yes | Ordered list of display rules |

### Display Rule

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `gate` | string | No | Gate ID to evaluate (if omitted, rule always matches) |
| `template` | string | Yes | Format string with `{field}` placeholders from context |

The compiled operator provides a `display()` method that evaluates rules and returns the formatted string.

---

## Compute Unit Contract

Compute units are external, hermetic functions with strict I/O:

```json
{
  "compute_units": {
    "unit_id": {
      "type": "sync | async",
      "input_schema": {
        "type": "object",
        "properties": { },
        "required": [ ]
      },
      "output_schema": {
        "type": "object", 
        "properties": { },
        "required": [ ]
      },
      "error_codes": ["TIMEOUT", "INVALID_INPUT", "EXTERNAL_FAILURE"],
      "timeout_ms": 5000,
      "retry_policy": {
        "max_attempts": 3,
        "backoff_ms": 1000
      }
    }
  }
}
```

---

## Events

Events trigger transitions. Standard event structure:

```json
{
  "event": "EVENT_NAME",
  "payload": { },
  "timestamp": "ISO8601",
  "correlation_id": "string",
  "source": "string"
}
```

### Reserved Events

| Event | Description |
|-------|-------------|
| `$INIT` | Blueprint initialization |
| `$TIMEOUT` | Timer expiration |
| `$ERROR` | Error condition |
| `$TERMINATE` | Force termination |

---

## Complete Example

```json
{
  "$schema": "lpp/v0.1",
  "id": "order-approval-workflow",
  "name": "Order Approval Workflow",
  "version": "1.0.0",
  "description": "Simple order approval with amount threshold",
  
  "context_schema": {
    "properties": {
      "order_id": { "type": "string" },
      "amount": { "type": "number" },
      "approved_by": { "type": "string" }
    }
  },
  
  "states": {
    "pending": {
      "name": "Pending Review",
      "description": "Order awaiting approval"
    },
    "auto_approved": {
      "name": "Auto-Approved",
      "description": "Order auto-approved (under threshold)"
    },
    "manual_review": {
      "name": "Manual Review Required",
      "description": "Order requires human approval"
    },
    "approved": {
      "name": "Approved",
      "on_enter": ["notify_approved"]
    },
    "rejected": {
      "name": "Rejected",
      "on_enter": ["notify_rejected"]
    }
  },
  
  "entry_state": "pending",
  "terminal_states": ["approved", "rejected"],
  
  "gates": {
    "is_under_threshold": {
      "type": "expression",
      "expression": "context.amount < 1000"
    },
    "is_over_threshold": {
      "type": "expression", 
      "expression": "context.amount >= 1000"
    }
  },
  
  "actions": {
    "notify_approved": {
      "type": "emit",
      "event": "ORDER_APPROVED",
      "payload_map": {
        "order_id": "context.order_id"
      }
    },
    "notify_rejected": {
      "type": "emit",
      "event": "ORDER_REJECTED",
      "payload_map": {
        "order_id": "context.order_id"
      }
    },
    "set_approver": {
      "type": "set",
      "target": "context.approved_by",
      "value_from": "event.payload.approver"
    }
  },
  
  "transitions": [
    {
      "id": "auto_approve",
      "from": "pending",
      "to": "auto_approved",
      "on_event": "SUBMIT",
      "gates": ["is_under_threshold"]
    },
    {
      "id": "require_review",
      "from": "pending", 
      "to": "manual_review",
      "on_event": "SUBMIT",
      "gates": ["is_over_threshold"]
    },
    {
      "id": "finalize_auto",
      "from": "auto_approved",
      "to": "approved",
      "on_event": "$ENTER"
    },
    {
      "id": "manual_approve",
      "from": "manual_review",
      "to": "approved",
      "on_event": "APPROVE",
      "actions": ["set_approver"]
    },
    {
      "id": "manual_reject",
      "from": "manual_review",
      "to": "rejected",
      "on_event": "REJECT"
    }
  ]
}
```

---

## Determinism Guarantees

1. **Transition Selection**: When multiple transitions match, they are evaluated in array order. First match wins.
2. **Gate Evaluation**: All gates for a transition must pass (logical AND).
3. **Action Execution**: Actions execute in array order, synchronously by default.
4. **Context Isolation**: Context mutations are atomic per transition.

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.1 | 2024-01 | Initial specification || 0.1.1 | 2024-12 | Clarifications: `on` → `on_event`, `context` → `context_schema`, added `display.rules` |