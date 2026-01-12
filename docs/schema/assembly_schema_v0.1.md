# L++ Assembly Blueprint Schema Specification v0.1

## Overview

An Assembly Blueprint is a meta-level JSON document that **composes pre-verified component blueprints** into a workflow. Components are treated as atomic actions with defined terminal outcomes - their internal state machines are encapsulated.

**Key Principle:** Assembly verification reasons about component terminals and contracts, not internal states. This enables hierarchical verification without combinatorial explosion.

```
Assembly Blueprint
       │
       ├── Component A (atomic action)
       │   └── Terminal: done → {output: X}
       │   └── Terminal: error → {output: Y}
       │
       ├── Component B (atomic action)
       │   └── Terminal: success → {output: Z}
       │
       └── Wiring: A.done → B.entry, passing A.output.X to B.input
```

---

## Root Structure

```json
{
  "$schema": "lpp/assembly/v0.1",
  "id": "string",
  "name": "string",
  "version": "string",
  "description": "string",
  "components": { },
  "context_schema": { },
  "states": { },
  "transitions": [ ],
  "gates": { },
  "assembly_invariants": [ ],
  "entry_state": "string",
  "terminal_states": [ ]
}
```

### Root Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `$schema` | string | Yes | Must be `"lpp/assembly/v0.1"` |
| `id` | string | Yes | Unique assembly identifier |
| `name` | string | Yes | Human-readable name |
| `version` | string | Yes | Assembly version (semver) |
| `components` | object | Yes | Component blueprint references |
| `context_schema` | object | Yes | Assembly-level context (aggregates component outputs) |
| `states` | object | Yes | Assembly states (may reference component execution) |
| `transitions` | array | Yes | Assembly transitions triggered by component terminals |
| `gates` | object | No | Assembly-level gates (can reference component outputs) |
| `assembly_invariants` | array | No | Cross-component invariants to verify |
| `entry_state` | string | Yes | Starting state |
| `terminal_states` | array | Yes | Assembly exit states |

---

## Components Section

Declares the component blueprints used in this assembly. Each component is treated as an atomic action.

```json
"components": {
  "auth": {
    "blueprint": "skills/auth/auth.json",
    "alias": "auth",
    "required_terminals": ["authenticated", "auth_failed"],
    "input_map": {
      "credentials": "assembly.context.user_credentials"
    }
  },
  "payment": {
    "blueprint": "skills/payment/payment.json",
    "alias": "payment",
    "required_terminals": ["payment_complete", "payment_failed"],
    "input_map": {
      "auth_token": "auth.output.token",
      "amount": "assembly.context.amount"
    }
  }
}
```

### Component Fields

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `blueprint` | string | Yes | Path to component blueprint JSON |
| `alias` | string | No | Short name for referencing (defaults to key) |
| `required_terminals` | array | No | Terminal states this assembly depends on |
| `input_map` | object | No | Maps assembly/component context to component input |

---

## States Section

Assembly states include both coordination states and component execution states.

```json
"states": {
  "idle": {
    "type": "coordination",
    "description": "Awaiting workflow trigger"
  },
  "authenticating": {
    "type": "component_execution",
    "component": "auth",
    "description": "Executing auth component"
  },
  "processing_payment": {
    "type": "component_execution",
    "component": "payment",
    "description": "Executing payment component"
  },
  "complete": {
    "type": "coordination",
    "description": "Workflow complete"
  },
  "failed": {
    "type": "coordination",
    "description": "Workflow failed"
  }
}
```

### State Types

| Type | Description |
|------|-------------|
| `coordination` | Assembly-level state (not executing a component) |
| `component_execution` | State where a component blueprint is active |

---

## Transitions Section

Transitions at assembly level are triggered by:
1. External events (like component blueprints)
2. **Component terminal events** - when a component reaches a terminal state

```json
"transitions": [
  {
    "id": "t_start",
    "from": "idle",
    "to": "authenticating",
    "on_event": "START_WORKFLOW",
    "actions": ["init_context"]
  },
  {
    "id": "t_auth_success",
    "from": "authenticating",
    "to": "processing_payment",
    "on_event": "auth:TERMINAL",
    "gates": ["g_auth_succeeded"],
    "actions": ["capture_auth_output"]
  },
  {
    "id": "t_auth_failed",
    "from": "authenticating",
    "to": "failed",
    "on_event": "auth:TERMINAL",
    "gates": ["g_auth_failed"],
    "actions": ["capture_error"]
  },
  {
    "id": "t_payment_success",
    "from": "processing_payment",
    "to": "complete",
    "on_event": "payment:TERMINAL",
    "gates": ["g_payment_succeeded"]
  }
]
```

### Component Terminal Events

When a component reaches a terminal state, it emits `{component_alias}:TERMINAL`. The assembly uses gates to branch based on which terminal was reached:

```json
"gates": {
  "g_auth_succeeded": {
    "type": "expression",
    "expression": "auth._terminal == 'authenticated'"
  },
  "g_auth_failed": {
    "type": "expression",
    "expression": "auth._terminal == 'auth_failed'"
  }
}
```

---

## Actions Section

Assembly actions can:
1. Initialize assembly context
2. Capture component outputs into assembly context
3. Transform data between components

```json
"actions": {
  "init_context": {
    "type": "set",
    "target": "workflow_id",
    "value_from": "event.payload.workflow_id"
  },
  "capture_auth_output": {
    "type": "set",
    "target": "auth_token",
    "value_from": "auth.output.token"
  },
  "capture_error": {
    "type": "set",
    "target": "error",
    "value_from": "auth.output.error_code"
  }
}
```

### Referencing Component Outputs

Component outputs are accessed via `{alias}.output.{field}` where fields are defined by the component's `terminal_contracts`.

---

## Assembly Invariants

Cross-component properties that must hold. These are verified at assembly level.

```json
"assembly_invariants": [
  {
    "id": "AI_001",
    "name": "Payment requires authentication",
    "type": "state_dependency",
    "expression": "_state == 'processing_payment' => auth_token != None",
    "severity": "critical"
  },
  {
    "id": "AI_002",
    "name": "Interface compatibility",
    "type": "contract_match",
    "check": {
      "source": "auth.terminal_contracts.authenticated.output.token",
      "target": "payment.context_schema.properties.auth_token",
      "match": "type"
    }
  },
  {
    "id": "AI_003",
    "name": "No orphan payments",
    "type": "sequence",
    "expression": "payment._terminal == 'payment_complete' => auth._terminal == 'authenticated'",
    "severity": "critical"
  }
]
```

### Invariant Types

| Type | Description | Verification |
|------|-------------|--------------|
| `state_dependency` | Context must satisfy condition in state | TLA+ invariant |
| `contract_match` | Component interfaces are compatible | Static schema check |
| `sequence` | Component executions follow required order | TLA+ temporal property |

---

## Context Schema

Assembly-level context aggregates data flowing through the workflow.

```json
"context_schema": {
  "properties": {
    "workflow_id": {"type": "string"},
    "auth_token": {"type": "string", "source": "auth.output.token"},
    "user_id": {"type": "string", "source": "auth.output.user_id"},
    "payment_id": {"type": "string", "source": "payment.output.payment_id"},
    "amount": {"type": "number", "source": "input"},
    "error": {"type": "string"}
  }
}
```

The `source` field documents where each property originates, enabling dataflow analysis.

---

## TLA+ Generation for Assembly

The assembly validator generates TLA+ that treats components as atomic:

```tla
--------------------------- MODULE PaymentWorkflow ---------------------------
VARIABLES meta_state, auth_token, user_id, payment_id, error,
          auth_terminal, payment_terminal

(* Component terminals are non-deterministically chosen from their contracts *)
AuthTerminals == {"authenticated", "auth_failed", "mfa_required"}
PaymentTerminals == {"payment_complete", "payment_failed", "insufficient_funds"}

(* Auth component as atomic action *)
ExecuteAuth ==
    /\ meta_state = "authenticating"
    /\ auth_terminal' \in AuthTerminals
    /\ IF auth_terminal' = "authenticated"
       THEN /\ auth_token' \in STRING  \* Contract guarantees token
            /\ user_id' \in STRING
       ELSE /\ auth_token' = NULL
            /\ error' \in {"INVALID_CREDS", "LOCKED", "EXPIRED"}
    /\ UNCHANGED <<payment_id, payment_terminal>>

(* Assembly-level invariant *)
PaymentRequiresAuth ==
    meta_state = "processing_payment" => auth_token /= NULL

=============================================================================
```

---

## Verification Levels

| Level | What's Verified | Tool |
|-------|-----------------|------|
| Component | Internal state machine correctness | TLA+/TLC per component |
| Assembly - Static | Interface compatibility, type matching | Schema validator |
| Assembly - Dynamic | Cross-component invariants, sequencing | TLA+/TLC on assembly |

**Key insight:** Assembly TLA+ has bounded state space because components are atomic actions with enumerated terminals, not expanded state machines.

---

## Example: Payment Workflow Assembly

```json
{
  "$schema": "lpp/assembly/v0.1",
  "id": "payment_workflow",
  "name": "Payment Processing Workflow",
  "version": "1.0.0",
  "description": "Orchestrates auth, payment, and audit components",

  "components": {
    "auth": {
      "blueprint": "skills/auth/auth.json",
      "required_terminals": ["authenticated", "auth_failed"]
    },
    "payment": {
      "blueprint": "skills/payment/payment.json",
      "required_terminals": ["payment_complete", "payment_failed"]
    },
    "audit": {
      "blueprint": "skills/audit/audit.json",
      "required_terminals": ["logged"]
    }
  },

  "context_schema": {
    "properties": {
      "workflow_id": {"type": "string"},
      "auth_token": {"type": "string"},
      "user_id": {"type": "string"},
      "amount": {"type": "number"},
      "payment_id": {"type": "string"},
      "error": {"type": "string"},
      "error_source": {"type": "string"}
    }
  },

  "states": {
    "idle": {"type": "coordination"},
    "authenticating": {"type": "component_execution", "component": "auth"},
    "processing_payment": {"type": "component_execution", "component": "payment"},
    "logging_success": {"type": "component_execution", "component": "audit"},
    "logging_failure": {"type": "component_execution", "component": "audit"},
    "complete": {"type": "coordination"},
    "failed": {"type": "coordination"}
  },

  "transitions": [
    {"id": "t_start", "from": "idle", "to": "authenticating", "on_event": "START"},
    {"id": "t_auth_ok", "from": "authenticating", "to": "processing_payment",
     "on_event": "auth:TERMINAL", "gates": ["g_auth_ok"], "actions": ["a_capture_auth"]},
    {"id": "t_auth_fail", "from": "authenticating", "to": "logging_failure",
     "on_event": "auth:TERMINAL", "gates": ["g_auth_fail"], "actions": ["a_set_error_auth"]},
    {"id": "t_pay_ok", "from": "processing_payment", "to": "logging_success",
     "on_event": "payment:TERMINAL", "gates": ["g_pay_ok"], "actions": ["a_capture_payment"]},
    {"id": "t_pay_fail", "from": "processing_payment", "to": "logging_failure",
     "on_event": "payment:TERMINAL", "gates": ["g_pay_fail"], "actions": ["a_set_error_pay"]},
    {"id": "t_logged_ok", "from": "logging_success", "to": "complete", "on_event": "audit:TERMINAL"},
    {"id": "t_logged_fail", "from": "logging_failure", "to": "failed", "on_event": "audit:TERMINAL"}
  ],

  "gates": {
    "g_auth_ok": {"type": "expression", "expression": "auth._terminal == 'authenticated'"},
    "g_auth_fail": {"type": "expression", "expression": "auth._terminal == 'auth_failed'"},
    "g_pay_ok": {"type": "expression", "expression": "payment._terminal == 'payment_complete'"},
    "g_pay_fail": {"type": "expression", "expression": "payment._terminal == 'payment_failed'"}
  },

  "actions": {
    "a_capture_auth": {"type": "set", "target": "auth_token", "value_from": "auth.output.token"},
    "a_capture_payment": {"type": "set", "target": "payment_id", "value_from": "payment.output.payment_id"},
    "a_set_error_auth": {"type": "set", "target": "error_source", "value": "auth"},
    "a_set_error_pay": {"type": "set", "target": "error_source", "value": "payment"}
  },

  "assembly_invariants": [
    {"id": "AI_001", "type": "state_dependency",
     "expression": "_state == 'processing_payment' => auth_token != None",
     "severity": "critical"},
    {"id": "AI_002", "type": "sequence",
     "expression": "payment._terminal != None => auth._terminal == 'authenticated'",
     "severity": "critical"}
  ],

  "entry_state": "idle",
  "terminal_states": ["complete", "failed"]
}
```

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 0.1 | 2025-01 | Initial assembly schema specification |
