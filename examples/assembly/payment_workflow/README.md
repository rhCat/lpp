# Payment Workflow Assembly Example

This example demonstrates L++ assembly blueprints - meta-level orchestration of pre-verified component blueprints.

## Architecture

```
payment_workflow.json (Assembly)
       │
       ├── auth.json (Component)
       │   └── Terminals: authenticated, auth_failed
       │
       ├── payment.json (Component)
       │   └── Terminals: payment_complete, payment_failed
       │
       └── audit.json (Component)
           └── Terminal: logged
```

## Key Concepts

### Components as Atomic Actions

At the assembly level, each component is treated as an **atomic action** with defined terminal outcomes. The assembly doesn't see the component's internal states - only its terminals and output contracts.

### Terminal Contracts

Each component defines what outputs are guaranteed at each terminal state:

```json
"terminal_contracts": {
  "authenticated": {
    "output_schema": {
      "token": {"type": "string", "non_null": true},
      "user_id": {"type": "string", "non_null": true}
    }
  }
}
```

### Assembly Invariants

Cross-component properties verified at the assembly level:

- **AI_001**: Payment requires authentication - cannot reach `processing_payment` without `auth_token`
- **AI_002**: Auth before payment - payment terminal implies auth succeeded
- **AI_003**: All paths audited - every terminal path goes through audit
- **AI_004**: Interface compatibility - auth token type matches payment input

## State Machine

```
idle
  │
  └─[START_WORKFLOW]→ authenticating
                           │
              ┌────────────┴────────────┐
              │                         │
        [auth:OK]                 [auth:FAILED]
              │                         │
              ▼                         │
      processing_payment                │
              │                         │
     ┌────────┴────────┐                │
     │                 │                │
[pay:OK]          [pay:FAILED]          │
     │                 │                │
     ▼                 ▼                ▼
logging_success   logging_failure ◄─────┘
     │                 │
     ▼                 ▼
  complete          failed
```

## Validation

```bash
# Validate assembly (checks interfaces, terminals, invariants)
python -m frame_py.assembly_validator payment_workflow.json

# Generate TLA+ for assembly-level verification
python -m frame_py.assembly_validator payment_workflow.json --tla ./tla
```

## Verification Levels

| Level | Scope | What's Checked |
|-------|-------|----------------|
| Component | auth.json | Internal state machine, gates, transitions |
| Component | payment.json | Internal state machine, gates, transitions |
| Component | audit.json | Internal state machine, gates, transitions |
| Assembly | payment_workflow.json | Interface compatibility, sequencing, cross-component invariants |

The key insight: Assembly TLA+ has bounded state space because components are atomic actions with enumerated terminals, not expanded state machines.

## Files

```
payment_workflow/
├── payment_workflow.json    # Assembly blueprint
├── components/
│   ├── auth.json           # Auth component (pre-verified)
│   ├── payment.json        # Payment component (pre-verified)
│   └── audit.json          # Audit component (pre-verified)
├── tla/                    # Generated TLA+ specs
│   ├── payment_workflow.tla
│   └── payment_workflow.cfg
└── README.md
```
