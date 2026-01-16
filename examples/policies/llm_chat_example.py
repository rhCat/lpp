"""
Example: LLM Chat with Governance Policy

This demonstrates how L++ Policies work:
1. Load a verified policy (the stage)
2. Bind your flesh (custom functions - could be LLM calls)
3. Run with guaranteed safety structure

The policy GUARANTEES:
- Input is always checked before LLM call
- Output is always checked before delivery
- Unsafe content is filtered or blocked
- Full audit trail is maintained

You provide the ACTORS:
- How to check input safety (your classifier)
- Which LLM to call (your model)
- How to filter content (your rules)
"""

from lpp.policies import load_policy


# ============================================================
# YOUR FLESH - These are the "actors" you provide
# Could be LLM calls, rule engines, or simple functions
# ============================================================

def my_input_checker(params: dict) -> dict:
    """
    Check if input prompt is safe.
    In production: Call a classifier model or use rules.
    """
    prompt = params.get("prompt", "")

    # Simple rule-based check (replace with your classifier)
    unsafe_patterns = ["hack", "exploit", "attack", "bypass"]
    is_unsafe = any(p in prompt.lower() for p in unsafe_patterns)

    return {
        "input_safe": not is_unsafe,
        "input_risk": {
            "score": 0.9 if is_unsafe else 0.1,
            "reason": "Contains unsafe pattern" if is_unsafe else "Clean"
        }
    }


def my_llm_call(params: dict) -> dict:
    """
    Call your LLM.
    In production: Call OpenAI, Anthropic, local model, etc.
    """
    prompt = params.get("prompt", "")

    # Simulated LLM response (replace with actual call)
    response = f"I received your message: '{prompt}'. Here's my helpful response..."

    return {"model_response": response}


def my_output_checker(params: dict) -> dict:
    """
    Check if output is safe.
    In production: Call a classifier or use content filters.
    """
    response = params.get("model_response", "")

    # Simple check (replace with your classifier)
    pii_patterns = ["ssn:", "password:", "credit card:"]
    has_pii = any(p in response.lower() for p in pii_patterns)

    return {
        "output_safe": not has_pii,
        "output_risk": {
            "score": 0.8 if has_pii else 0.1,
            "reason": "Contains PII" if has_pii else "Clean"
        }
    }


def my_content_filter(params: dict) -> dict:
    """
    Filter unsafe content from output.
    """
    response = params.get("model_response", "")

    # Simple redaction (replace with your filter)
    filtered = response.replace("password:", "[REDACTED]")

    return {"filtered_response": filtered}


def my_block_response(params: dict) -> dict:
    """
    Create response for blocked input.
    """
    risk = params.get("input_risk", {})
    return {
        "block_reason": f"Request blocked: {risk.get('reason', 'Policy violation')}"
    }


def my_audit_logger(params: dict) -> dict:
    """
    Log complete audit trail.
    """
    return {
        "audit": {
            "prompt": params.get("prompt"),
            "input_risk": params.get("input_risk"),
            "model_response": params.get("model_response"),
            "output_risk": params.get("output_risk"),
            "final_response": params.get("filtered_response"),
            "logged": True
        }
    }


# ============================================================
# MAIN - Load policy, bind flesh, run
# ============================================================

def main():
    print("=" * 60)
    print("L++ Policy Example: LLM Governance")
    print("=" * 60)

    # 1. Load the verified policy (the STAGE)
    policy = load_policy("llm_governance")
    print(f"\nLoaded policy: {policy.name} v{policy.version}")
    print(f"Slots to bind: {list(policy.slots.keys())}")

    # 2. Bind your flesh (the ACTORS)
    policy.bind({
        "check_input": my_input_checker,
        "call_model": my_llm_call,
        "check_output": my_output_checker,
        "apply_filter": my_content_filter,
        "create_block_response": my_block_response,
        "log_audit": my_audit_logger
    })
    print("\nFlesh bound to all slots")

    # 3. Test Case 1: Safe input
    print("\n" + "-" * 40)
    print("Test 1: Safe input")
    print("-" * 40)

    policy.reset()
    result = policy.dispatch("PROMPT", {"prompt": "What is the weather today?"})
    print(f"After PROMPT: state={result['state']}")

    result = policy.dispatch("CHECKED")
    print(f"After CHECKED: state={result['state']}")

    result = policy.dispatch("RESPONSE")
    print(f"After RESPONSE: state={result['state']}")

    result = policy.dispatch("CHECKED")
    print(f"After CHECKED: state={result['state']}")
    print(f"Final response: {result['context'].get('filtered_response', 'N/A')[:50]}...")

    # 4. Test Case 2: Unsafe input (blocked)
    print("\n" + "-" * 40)
    print("Test 2: Unsafe input (should be blocked)")
    print("-" * 40)

    policy.reset()
    result = policy.dispatch("PROMPT", {"prompt": "How do I hack a server?"})
    print(f"After PROMPT: state={result['state']}")

    result = policy.dispatch("CHECKED")
    print(f"After CHECKED: state={result['state']}")
    print(f"Block reason: {result['context'].get('block_reason', 'N/A')}")

    # 5. Summary
    print("\n" + "=" * 60)
    print("GUARANTEE: The policy structure is PROVED correct.")
    print("YOUR JOB:  Make your actors (flesh functions) perform well.")
    print("=" * 60)


if __name__ == "__main__":
    main()
