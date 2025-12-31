"""
L++ Safe Expression Evaluator

A deterministic, secure expression parser for gate conditions.
Replaces Python's eval() with a minimal subset that only understands:

    - Boolean logic: and, or, not
    - Comparisons: ==, !=, <, >, <=, >=
    - Membership: in, not in
    - Null checks: is None, is not None
    - Context variable access: identifiers resolve to context dict
    - Literals: numbers, strings, True, False, None

This ensures the "Judge" cannot be bribed by external chaos.
No access to: imports, builtins, time, random, files, network.

State Machine (from safe_eval_blueprint.json):
    idle → parsing → validating → evaluating → complete
             ↓           ↓            ↓
           error       error        error

Transitions:
    EVALUATE: idle → parsing
    PARSE_DONE: parsing → validating
    PARSE_ERROR: parsing → error
    VALIDATION_PASSED: validating → evaluating
    UNSAFE_EXPRESSION: validating → error
    EVAL_DONE: evaluating → complete
    EVAL_ERROR: evaluating → error
    RESET: * → idle
"""

import re
import ast
import operator
from typing import Any, Dict, Union, Optional, Tuple
from enum import Enum


class SafeEvalState(Enum):
    """Safe evaluator state machine states."""
    IDLE = "idle"
    PARSING = "parsing"
    VALIDATING = "validating"
    EVALUATING = "evaluating"
    COMPLETE = "complete"
    ERROR = "error"


class SafeEvalError(Exception):
    """Raised when safe evaluation fails."""
    def __init__(self, message: str, state: SafeEvalState = None):
        self.state = state or SafeEvalState.ERROR
        super().__init__(message)


# Allowed AST node types (whitelist approach)
ALLOWED_NODES = {
    # Expressions
    ast.Expression,
    ast.BoolOp,
    ast.BinOp,
    ast.UnaryOp,
    ast.Compare,
    ast.IfExp,  # ternary: x if cond else y
    ast.Call,   # function calls (only from SAFE_FUNCTIONS)

    # Operators
    ast.And,
    ast.Or,
    ast.Not,
    ast.Eq,
    ast.NotEq,
    ast.Lt,
    ast.LtE,
    ast.Gt,
    ast.GtE,
    ast.Is,
    ast.IsNot,
    ast.In,
    ast.NotIn,
    ast.Add,
    ast.Sub,
    ast.Mult,
    ast.Div,
    ast.FloorDiv,
    ast.Mod,

    # Values
    ast.Constant,
    ast.Name,
    ast.Load,
    ast.Tuple,
    ast.List,
    ast.Set,

    # Attribute access (for nested context: event.payload.value)
    ast.Attribute,

    # Subscript (for context["key"] access)
    ast.Subscript,
}


# Pure Function Registry
# These are deterministic functions with no side effects.
# Only functions in this registry can be called in L++ expressions.
SAFE_FUNCTIONS = {
    'len': len,
    'abs': abs,
    'min': min,
    'max': max,
    'sum': sum,
    'any': any,
    'all': all,
    'round': round,
    'bool': bool,
    'int': int,
    'float': float,
    'str': str,
    # Add domain-specific pure functions here
}


def _validate_ast(node: ast.AST, depth: int = 0) -> None:
    """
    Recursively validate AST nodes against whitelist.
    Raises SafeEvalError if disallowed construct is found.
    """
    if depth > 50:
        raise SafeEvalError("Expression too deeply nested")

    if type(node) not in ALLOWED_NODES:
        raise SafeEvalError(
            f"Disallowed construct: {type(node).__name__}"
        )

    # Check for dangerous names
    if isinstance(node, ast.Name):
        dangerous = {
            '__import__', '__builtins__', '__class__', '__bases__',
            'eval', 'exec', 'compile', 'open', 'input', 'print',
            'globals', 'locals', 'vars', 'dir', 'getattr', 'setattr',
            'delattr', 'hasattr', 'type', 'isinstance', 'issubclass',
            'import', 'breakpoint', 'exit', 'quit', 'help',
        }
        if node.id in dangerous:
            raise SafeEvalError(f"Forbidden identifier: {node.id}")

    # Recurse into child nodes
    for child in ast.iter_child_nodes(node):
        _validate_ast(child, depth + 1)


def _resolve_name(name: str, context: Dict[str, Any]) -> Any:
    """Resolve a name to a value from context."""
    # Check special values first
    if name == 'True':
        return True
    if name == 'False':
        return False
    if name == 'None':
        return None

    # Look up in context
    if name in context:
        return context[name]

    # Check for _state (special L++ variable)
    if name == '_state':
        return context.get('_state')

    raise SafeEvalError(f"Undefined variable: {name}")


def _resolve_attr(obj: Any, attr: str) -> Any:
    """Safely resolve attribute access."""
    if obj is None:
        return None

    if isinstance(obj, dict):
        return obj.get(attr)

    # Only allow attribute access on safe types
    if isinstance(obj, (int, float, str, bool)):
        raise SafeEvalError(
            f"Cannot access attributes on primitive type: {type(obj).__name__}"
        )

    # For objects, use getattr but block dunders
    if attr.startswith('_'):
        raise SafeEvalError(f"Cannot access private attribute: {attr}")

    return getattr(obj, attr, None)


class SafeEvaluator(ast.NodeVisitor):
    """
    AST-based safe expression evaluator.
    Visits AST nodes and evaluates them against a context dict.
    """
    # Engineering Thresholds
    MAX_DEPTH = 5         # Deep nesting is hard to audit
    MAX_LENGTH = 120      # Long strings should be Compute Units
    MAX_CALLS = 3         # Chaining too many functions is "Flesh" logic

    def __init__(self, context: Dict[str, Any]):
        self.context = context
        self.current_depth = 0
        self.call_count = 0

    def _check_complexity(self, node, depth=0):
        """Recursive check for AST depth and call density."""
        if depth > self.MAX_DEPTH:
            print(
                "[L++ LINT WARNING] Expression "
                f"depth exceeds {self.MAX_DEPTH}. "
                "This logic is becoming 'Brittle Bone'. Move to COMPUTE."
            )

        if isinstance(node, ast.Call):
            self.call_count += 1
            if self.call_count > self.MAX_CALLS:
                print(
                    "[L++ LINT WARNING] Too many "
                    f"function calls ({self.call_count}). "
                    "The 'Judge' is doing too much work. Move to COMPUTE."
                )

        for child in ast.iter_child_nodes(node):
            self._check_complexity(child, depth + 1)

    def evaluate(self, expr: str) -> Any:
        """
        Safely evaluate an expression string.

        Args:
            expr: Expression string to evaluate

        Returns:
            The result of evaluating the expression

        Raises:
            SafeEvalError: If expression contains disallowed constructs
        """

        if len(expr) > self.MAX_LENGTH:
            print(
                "[L++ LINT WARNING] Expression is "
                f"too long ({len(expr)} chars). "
                "Consider moving this logic to a COMPUTE unit."
            )

        try:
            tree = ast.parse(expr, mode='eval')
        except SyntaxError as e:
            raise SafeEvalError(f"Syntax error: {e}")

        # Validate AST structure
        _validate_ast(tree)

        # Pre-check complexity
        self._check_complexity(tree)

        # Evaluate
        return self.visit(tree)

    def visit_Expression(self, node: ast.Expression) -> Any:
        return self.visit(node.body)

    def visit_Constant(self, node: ast.Constant) -> Any:
        return node.value

    def visit_Name(self, node: ast.Name) -> Any:
        return _resolve_name(node.id, self.context)

    def visit_Attribute(self, node: ast.Attribute) -> Any:
        obj = self.visit(node.value)
        return _resolve_attr(obj, node.attr)

    def visit_Subscript(self, node: ast.Subscript) -> Any:
        obj = self.visit(node.value)
        key = self.visit(node.slice)
        if obj is None:
            return None
        if isinstance(obj, dict):
            return obj.get(key)
        if isinstance(obj, (list, tuple)):
            if isinstance(key, int) and -len(obj) <= key < len(obj):
                return obj[key]
            return None
        raise SafeEvalError(f"Cannot subscript type: {type(obj).__name__}")

    def visit_BoolOp(self, node: ast.BoolOp) -> bool:
        if isinstance(node.op, ast.And):
            for value in node.values:
                if not self.visit(value):
                    return False
            return True
        elif isinstance(node.op, ast.Or):
            for value in node.values:
                if self.visit(value):
                    return True
            return False
        raise SafeEvalError(f"Unknown BoolOp: {type(node.op).__name__}")

    def visit_UnaryOp(self, node: ast.UnaryOp) -> Any:
        operand = self.visit(node.operand)
        if isinstance(node.op, ast.Not):
            return not operand
        raise SafeEvalError(f"Unknown UnaryOp: {type(node.op).__name__}")

    def visit_BinOp(self, node: ast.BinOp) -> Any:
        left = self.visit(node.left)
        right = self.visit(node.right)

        ops = {
            ast.Add: operator.add,
            ast.Sub: operator.sub,
            ast.Mult: operator.mul,
            ast.Div: operator.truediv,
            ast.FloorDiv: operator.floordiv,
            ast.Mod: operator.mod,
        }

        op_func = ops.get(type(node.op))
        if op_func is None:
            raise SafeEvalError(f"Unknown BinOp: {type(node.op).__name__}")

        # Handle None in arithmetic
        if left is None or right is None:
            return None

        return op_func(left, right)

    def visit_Compare(self, node: ast.Compare) -> bool:
        left = self.visit(node.left)

        for op, comparator in zip(node.ops, node.comparators):
            right = self.visit(comparator)

            if isinstance(op, ast.Eq):
                result = left == right
            elif isinstance(op, ast.NotEq):
                result = left != right
            elif isinstance(op, ast.Lt):
                result = left < right if (
                    left is not None and right is not None) else False
            elif isinstance(op, ast.LtE):
                result = left <= right if (
                    left is not None and right is not None) else False
            elif isinstance(op, ast.Gt):
                result = left > right if (
                    left is not None and right is not None) else False
            elif isinstance(op, ast.GtE):
                result = left >= right if (
                    left is not None and right is not None) else False
            elif isinstance(op, ast.Is):
                result = left is right
            elif isinstance(op, ast.IsNot):
                result = left is not right
            elif isinstance(op, ast.In):
                if right is None:
                    result = False
                else:
                    result = left in right
            elif isinstance(op, ast.NotIn):
                if right is None:
                    result = True
                else:
                    result = left not in right
            else:
                raise SafeEvalError(f"Unknown comparison: {type(op).__name__}")

            if not result:
                return False
            left = right

        return True

    def visit_IfExp(self, node: ast.IfExp) -> Any:
        """Ternary expression: x if condition else y"""
        if self.visit(node.test):
            return self.visit(node.body)
        return self.visit(node.orelse)

    def visit_Tuple(self, node: ast.Tuple) -> tuple:
        return tuple(self.visit(el) for el in node.elts)

    def visit_List(self, node: ast.List) -> list:
        return [self.visit(el) for el in node.elts]

    def visit_Set(self, node: ast.Set) -> set:
        return {self.visit(el) for el in node.elts}

    def visit_Call(self, node: ast.Call) -> Any:
        """
        Safely handle function calls.
        Only allows functions defined in SAFE_FUNCTIONS.
        """
        # 1. Resolve the function name - only simple names allowed
        if not isinstance(node.func, ast.Name):
            raise SafeEvalError("Only simple function calls are allowed")

        func_name = node.func.id
        func = SAFE_FUNCTIONS.get(func_name)

        if func is None:
            raise SafeEvalError(
                f"Function '{func_name}' is not in the safe whitelist")

        # 2. Evaluate arguments
        args = [self.visit(arg) for arg in node.args]

        # 3. Block keyword arguments for simplicity/security
        if node.keywords:
            raise SafeEvalError(
                "Keyword arguments are not allowed in L++ expressions")

        # 4. Execute the pure function
        try:
            return func(*args)
        except Exception as e:
            raise SafeEvalError(f"Error executing {func_name}(): {e}")


def safe_eval(expression: str, context: Dict[str, Any]) -> Tuple[Any, Optional[str]]:
    """
    Safely evaluate an L++ expression.

    This is the main entry point for deterministic, secure evaluation.

    Args:
        expression: Boolean expression string
        context: Context dictionary with variable values

    Returns:
        Tuple of (result, error):
        - result: Result of expression evaluation, None on error
        - error: None on success, error message on failure

    State machine: idle → parsing → validating → evaluating → complete | error

    Examples:
        >>> safe_eval("a > 5", {"a": 10})
        (True, None)
        >>> safe_eval("a is None", {"a": None})
        (True, None)
    """
    evaluator = SafeEvaluator(context)
    try:
        result = evaluator.evaluate(expression)
        return result, None  # EVAL_DONE → complete
    except SafeEvalError as e:
        return None, str(e)  # → error


def safe_eval_bool(expression: str, context: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
    """
    Safely evaluate an expression and return boolean result.

    This is the drop-in replacement for atom_EVALUATE.

    Args:
        expression: Boolean expression string
        context: Context dictionary

    Returns:
        Tuple of (result, error):
        - result: True if expression evaluates truthy, False otherwise
        - error: None on success, error message on failure

    State machine: idle → parsing → validating → evaluating → complete | error
    """
    try:
        result, error = safe_eval(expression, context)
        if error:
            print(f"[L++ SAFE EVAL WARNING] {error} in '{expression}'")
            return False, error
        return bool(result), None
    except SafeEvalError as e:
        # In deterministic system, failed evaluation = False
        print(f"[L++ SAFE EVAL WARNING] {e} in '{expression}'")
        return False, str(e)
    except Exception as e:
        print(f"[L++ SAFE EVAL ERROR] Unexpected: {e} in '{expression}'")
        return False, f"EVAL_ERROR: {str(e)}"


# =========================================================================
# CLI for testing
# =========================================================================

if __name__ == "__main__":
    import sys

    # Test cases - generic L++ expressions
    tests = [
        # Basic comparisons
        ("a > 5", {"a": 10}, True),
        ("a < 5", {"a": 10}, False),
        ("a == 10", {"a": 10}, True),
        ("a != 10", {"a": 10}, False),

        # None checks
        ("a is None", {"a": None}, True),
        ("a is not None", {"a": 10}, True),
        ("a is not None", {"a": None}, False),

        # Boolean logic
        ("a > 5 and b < 10", {"a": 7, "b": 3}, True),
        ("a > 5 or b > 10", {"a": 3, "b": 15}, True),
        ("not a", {"a": False}, True),

        # Membership
        ("status in ('pending', 'approved', 'rejected')",
            {"status": "approved"}, True),
        ("status in ('pending', 'approved', 'rejected')",
            {"status": "unknown"}, False),

        # Nested access (event.payload pattern common in L++)
        ("event.payload.value == 42", {
         "event": {"payload": {"value": 42}}}, True),
        ("event.payload.value > 0", {
         "event": {"payload": {"value": 42}}}, True),

        # Complex gate expression
        (
            "x is not None and y is not None and x > 0",
            {"x": 5, "y": 3},
            True
        ),
        (
            "mode == 'strict' and count == 0",
            {"mode": "strict", "count": 0},
            True
        ),

        # L++ special _state variable
        ("_state == 'active'", {"_state": "active"}, True),
        ("_state in ('idle', 'active', 'complete')",
         {"_state": "active"}, True),

        # Arithmetic in conditions
        ("a + b > 10", {"a": 5, "b": 8}, True),
        ("a * 2 == b", {"a": 5, "b": 10}, True),

        # Pure function calls
        ("len(items) > 0", {"items": [1, 2, 3]}, True),
        ("len(items) == 0", {"items": []}, True),
        ("max(a, b) == 10", {"a": 5, "b": 10}, True),
        ("min(a, b, c) == 1", {"a": 5, "b": 1, "c": 10}, True),
        ("abs(x) == 5", {"x": -5}, True),
        ("sum(values) > 10", {"values": [3, 4, 5]}, True),
        ("all(flags)", {"flags": [True, True, True]}, True),
        ("any(flags)", {"flags": [False, True, False]}, True),
        ("round(x) == 3", {"x": 3.14}, True),

        # Subscript access
        ("items[0] == 'first'", {"items": ["first", "second"]}, True),
        ("data['key'] == 'value'", {"data": {"key": "value"}}, True),
    ]

    print("L++ Safe Eval Test Suite")
    print("=" * 50)

    passed = 0
    failed = 0

    for expr, ctx, expected in tests:
        result = safe_eval_bool(expr, ctx)
        status = "✓" if result == expected else "✗"
        if result == expected:
            passed += 1
        else:
            failed += 1
            status = f"✗ (got {result})"
        print(f"  {status} {expr}")

    print("=" * 50)
    print(f"Passed: {passed}/{len(tests)}")

    if failed > 0:
        sys.exit(1)

    # Test security - these should fail gracefully
    print("\nSecurity Tests (should all return False):")
    dangerous = [
        "__import__('os')",
        "eval('1+1')",
        "open('/etc/passwd')",
        "__builtins__",
        "globals()",
    ]

    for expr in dangerous:
        result = safe_eval_bool(expr, {})
        status = "✓ (blocked)" if not result else "✗ (SECURITY BREACH!)"
        print(f"  {status} {expr}")
