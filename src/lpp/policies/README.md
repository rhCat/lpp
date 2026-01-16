# L++ Policy Library

## Philosophy

> "The stage must be solid. Actors perform, audience judges."

Policies are **verified state machine templates** that guarantee structural correctness.
Users customize behavior through **flesh bindings** - compute functions that plug into policy slots.

## Policy vs Blueprint

| Aspect | Blueprint | Policy |
|--------|-----------|--------|
| Purpose | Specific implementation | Reusable pattern |
| Compute | Concrete functions | Abstract slots |
| Verification | Instance-level | Pattern-level |
| Customization | Fixed | Flesh bindings |

## Available Policies

### 1. `api_gateway` - Request/Response Pattern
```
idle → validating → processing → responding → complete
                 ↘ error_handling → error
```
**Slots:** `validate`, `process`, `format_response`, `handle_error`

### 2. `llm_governance` - AI Safety Pattern
```
idle → input_guard → inference → output_guard → complete
    ↘ blocked                  ↘ filtered → complete
```
**Slots:** `check_input`, `call_model`, `check_output`, `apply_filter`

### 3. `approval_chain` - Multi-Stage Approval
```
idle → submitted → reviewing[n] → approved → complete
                 ↘ rejected → error
```
**Slots:** `submit`, `review`, `approve`, `reject`, `notify`

### 4. `circuit_breaker` - Resilience Pattern
```
closed → call → success → closed
             ↘ failure → open → half_open → call
```
**Slots:** `execute`, `on_success`, `on_failure`, `health_check`

### 5. `audit_trail` - Compliance Pattern
```
idle → capture → validate → store → complete
                        ↘ quarantine → review → complete/error
```
**Slots:** `capture_event`, `validate_event`, `store_event`, `quarantine`

## Usage

```python
from lpp.policies import load_policy

# Load a policy
policy = load_policy("api_gateway")

# Bind flesh to slots
policy.bind({
    "validate": my_validator,
    "process": my_processor,
    "format_response": my_formatter,
    "handle_error": my_error_handler
})

# Run
result = policy.run(request)
```

## Verification Guarantee

Every policy in this library has:
- TLAPS proof of type invariants
- TLAPS proof of transition preservation
- TLAPS proof of terminal reachability
- TLC model checking for safety properties

**The stage is PROVED. Your actors determine the show.**
