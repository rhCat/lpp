# L++ Policy Theory: The Golden Rules

## The Engineering Question

> "What is the minimal set of provable structures from which ALL correct policies derive?"

Like Chemical Engineering derives all process designs from 3 conservation laws,
L++ should derive all policies from a minimal set of proven atoms.

## Analysis: Policy Decomposition

### Observed Policies

| Policy | Pattern |
|--------|---------|
| API Gateway | receive → validate → process → respond |
| LLM Governance | guard → process → guard → deliver |
| Approval Chain | submit → review* → decide |
| Circuit Breaker | closed ⇄ open ⇄ half-open |
| Saga | try → (compensate)? → complete |
| Audit Trail | capture → validate → store |

### Decomposition into Atoms

Every policy above can be decomposed into combinations of:

```
ATOM 1: SEQUENCE
        A → B
        "After A completes, B begins"

ATOM 2: BRANCH
        A → B | C
        "After A, either B or C based on condition"

ATOM 3: GUARD
        [condition] → A
        "A only proceeds if condition holds"

ATOM 4: LOOP
        A → B → A
        "Repeat until condition"

ATOM 5: TERMINAL
        A → ⊥
        "End state with contract"
```

### Policy = Composition of Atoms

```
API Gateway     = GUARD + SEQUENCE + SEQUENCE + TERMINAL
                  [valid] → validate → process → respond → ⊥

LLM Governance  = GUARD + SEQUENCE + GUARD + BRANCH + TERMINAL
                  [safe] → infer → [safe] → deliver|filter → ⊥

Approval Chain  = SEQUENCE + LOOP(GUARD + BRANCH) + TERMINAL
                  submit → ([approved] → next | reject)* → ⊥

Circuit Breaker = LOOP(BRANCH + GUARD)
                  (closed → [fail] → open → [timeout] → half → [success])*
```

## The Golden Rules (Candidate)

### Rule 1: State Conservation
> Every state in a policy must be reachable from init AND reach a terminal.

```tla
∀ s ∈ States: Reachable(init, s) ∧ Reachable(s, terminal)
```

**Analogous to**: Conservation of Mass - no mass created or destroyed

### Rule 2: Information Preservation
> Context can only be modified by explicit actions; never implicitly lost.

```tla
∀ t ∈ Transitions: context' = action(context) ∨ context' = context
```

**Analogous to**: Conservation of Energy - energy transforms, never disappears

### Rule 3: Causal Ordering
> Every transition requires an event; no spontaneous state changes.

```tla
∀ t ∈ Transitions: ∃ e ∈ Events: triggers(e, t)
```

**Analogous to**: Newton's First Law - no motion without force

### Rule 4: Guard Completeness
> At any non-terminal state, exactly one transition must be enabled.

```tla
∀ s ∈ States \ Terminals: ∃! t ∈ Transitions: enabled(t, s)
```

**Analogous to**: Determinism in process design - one path, no ambiguity

### Rule 5: Terminal Contracts
> Every terminal state must guarantee its declared output schema.

```tla
∀ s ∈ Terminals: state = s ⇒ satisfies(context, output_schema[s])
```

**Analogous to**: Product specifications - output meets requirements

## Minimal Provable Structure

If a policy satisfies Rules 1-5, it is **structurally correct**.

```
Policy Correctness = Rule1 ∧ Rule2 ∧ Rule3 ∧ Rule4 ∧ Rule5
```

Any policy that satisfies these rules:
- Cannot deadlock (Rule 1)
- Cannot lose information (Rule 2)
- Cannot have race conditions (Rule 3)
- Cannot have ambiguous paths (Rule 4)
- Cannot violate contracts (Rule 5)

## Over-Engineering Detection

A policy is **over-engineered** if:

1. **Redundant States**: States that are bisimilar (same behavior)
2. **Redundant Guards**: Guards that are logically equivalent
3. **Unnecessary Loops**: Loops that always execute exactly once
4. **Dead Branches**: Branches where one path is never taken

### Minimality Criterion

A policy is **minimal** if:
- No state can be removed without violating Rules 1-5
- No transition can be merged without losing distinct behavior
- No guard can be simplified without changing reachability

## The Design Process

### Step 1: Identify Required Terminals
What are the possible end states? (success, error, timeout, etc.)

### Step 2: Identify Required Guards
What conditions must be checked? (validation, authorization, safety)

### Step 3: Compose from Atoms
Build the minimal structure using SEQUENCE, BRANCH, GUARD, LOOP

### Step 4: Verify Golden Rules
Prove Rules 1-5 hold

### Step 5: Check Minimality
Remove redundancy

## Example: Deriving LLM Governance

```
Required Terminals: complete, blocked, error
Required Guards:    input_safe, output_safe

Minimal Composition:
  GUARD(has_input) →
    GUARD(input_safe) →
      SEQUENCE(inference) →
        GUARD(output_safe) →
          TERMINAL(complete)
        | SEQUENCE(filter) →
            TERMINAL(complete)
    | TERMINAL(blocked)

States: 6 (minimum for this requirement set)
Transitions: 7 (minimum to connect all paths)
```

## Comparison to Engineering Design

| Engineering | L++ |
|-------------|-----|
| Start with requirements | Start with terminals |
| Apply conservation laws | Apply golden rules |
| Design unit operations | Design state atoms |
| Compose into flowsheet | Compose into policy |
| Verify mass/energy balance | Verify TLAPS proofs |
| Optimize for cost/efficiency | Minimize states/transitions |

## Open Questions

1. Are 5 rules sufficient? Or can we reduce further?
2. Is there a canonical form for minimal policies?
3. Can we automate the minimality check?
4. How do golden rules compose for assemblies?
