"""
L++ Operational Validator

Validates generated Python files for syntax, imports, and structure.
Catches common LLM generation errors before runtime.

Validation Stages:
    1. Content - LLM-specific errors (literal newlines, placeholders)
    2. Syntax - AST parsing with line numbers
    3. Import - Module reference validation
    4. Structure - Required elements (COMPUTE_UNITS, etc.)

Sanitization:
    - Auto-fix literal newlines inside strings (common LLM error)
    - Auto-fix unterminated string literals where possible
"""

import ast
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple


def sanitize_python_code(
    code: str, filename: str = "code.py", verbose: bool = False
) -> Tuple[str, List[str]]:
    """
    Sanitize Python code by fixing common LLM generation errors.

    Primary fix: Literal newlines inside strings.
    LLMs often generate:
        print("Hello
        World")
    Instead of:
        print("Hello\\nWorld")

    Args:
        code: Python source code string
        filename: For error messages
        verbose: Print fixes applied

    Returns:
        Tuple of (sanitized_code, fixes_applied):
        - sanitized_code: Fixed code string
        - fixes_applied: List of descriptions of fixes
    """
    fixes = []
    result = code

    # Try parsing first - if it works, no fixes needed
    try:
        ast.parse(code, filename=filename)
        return code, []
    except SyntaxError:
        pass  # Need to attempt fixes

    # Fix 1: Literal newlines in f-strings and regular strings
    # Pattern: string quote followed by actual newline before closing quote
    result, fix_count = _fix_literal_newlines_in_strings(result)
    if fix_count > 0:
        fixes.append(f"Fixed {fix_count} literal newlines in strings")
        if verbose:
            print(
                f"  [SANITIZE] {filename}: Fixed {fix_count} literal newlines")

    # Verify fix worked
    try:
        ast.parse(result, filename=filename)
        if verbose and fixes:
            print(f"  [SANITIZE] {filename}: Code now valid after fixes")
    except SyntaxError as e:
        # Fix didn't fully work, but return what we have
        if verbose:
            print(
                f"  [SANITIZE] {filename}: "
                f"Still has syntax error after fixes: {e.msg}"
            )

    return result, fixes


def _fix_literal_newlines_in_strings(code: str) -> Tuple[str, int]:
    """
    Fix literal newlines inside string literals.

    Handles:
    - print("Hello
            World")  -> print("Hello\\nWorld")
    - f"Results:
         {var}"      -> f"Results:\\n{var}"
    """
    fix_count = 0
    lines = code.split('\n')
    result_lines = []
    i = 0

    while i < len(lines):
        line = lines[i]

        # Check if line has an unclosed string literal
        # Look for lines ending with
        # unclosed quotes in print, f-string, or assignment
        unclosed_match = _find_unclosed_string(line)

        if unclosed_match:
            # Found unclosed string - try to find where it closes
            quote_char = unclosed_match['quote']
            prefix = unclosed_match['prefix']
            is_fstring = 'f' in prefix.lower()

            # Accumulate subsequent lines until we find the closing quote
            accumulated = line
            j = i + 1
            found_close = False

            while j < len(lines) and not found_close:
                next_line = lines[j]
                stripped = next_line.strip()

                # Check if this line closes the string
                if _closes_string(stripped, quote_char, is_fstring):
                    # Join with \n escape
                    accumulated = accumulated.rstrip() + \
                        '\\n' + stripped.lstrip()
                    found_close = True
                    fix_count += 1
                    j += 1
                elif _could_be_string_continuation(
                    stripped, quote_char, is_fstring
                ):
                    # Continue accumulating
                    accumulated = accumulated.rstrip() + \
                        '\\n' + stripped.lstrip()
                    fix_count += 1
                    j += 1
                else:
                    # Not a continuation - stop
                    break

            result_lines.append(accumulated)
            i = j
        else:
            result_lines.append(line)
            i += 1

    return '\n'.join(result_lines), fix_count


def _find_unclosed_string(line: str) -> Optional[Dict]:
    """
    Check if line has an unclosed string literal.
    Returns dict with quote type and prefix if found, None otherwise.
    """
    # Common patterns that may have unclosed strings
    patterns = [
        # print("..., print('...
        r'(print\s*\(\s*)(f?)(["\'])(?!["\'])',
        # input("..., input('...
        r'(input\s*\(\s*)(f?)(["\'])(?!["\'])',
        # = "..., = '...
        r'(=\s*)(f?)(["\'])(?!["\'])',
        # return "..., return '...
        r'(return\s+)(f?)(["\'])(?!["\'])',
    ]

    for pattern in patterns:
        match = re.search(pattern, line)
        if match:
            prefix = match.group(1) + match.group(2)
            quote = match.group(3)

            # Check if string is actually unclosed
            after_quote = line[match.end()-1:]  # from the quote char onwards
            # Count quotes (accounting for escapes)
            if not _is_string_closed(after_quote, quote):
                return {'prefix': prefix, 'quote': quote, 'pos': match.start()}

    return None


def _is_string_closed(text: str, quote: str) -> bool:
    """Check if string starting with quote is properly closed."""
    if len(text) < 2:
        return False

    in_string = False
    escape = False

    for i, ch in enumerate(text):
        if escape:
            escape = False
            continue
        if ch == '\\':
            escape = True
            continue
        if ch == quote:
            if i == 0:
                in_string = True
            else:
                return True  # Found closing quote
        # Handle f-string braces
        if ch == '{' and in_string:
            # Skip to matching }
            depth = 1
            j = i + 1
            while j < len(text) and depth > 0:
                if text[j] == '{':
                    depth += 1
                elif text[j] == '}':
                    depth -= 1
                j += 1

    return False


def _closes_string(line: str, quote: str, is_fstring: bool) -> bool:
    """Check if line closes a string (ends with quote + optional parens)."""
    stripped = line.rstrip()

    # Patterns that close strings
    close_patterns = [
        f'{quote}\\s*\\)',      # ends with ") or ')
        f'{quote}$',            # just ends with quote
        f'}}\\s*{quote}\\s*\\)',  # f-string: }" or }'
        f'}}\\s*{quote}$',      # f-string ending
    ]

    for pattern in close_patterns:
        if re.search(pattern, stripped):
            return True

    return False


def _could_be_string_continuation(
    line: str, quote: str, is_fstring: bool
) -> bool:
    """Check if line could be continuation of unclosed string."""
    stripped = line.strip()

    # Empty or whitespace-only - probably continuation
    if not stripped:
        return True

    # Contains variable reference in f-string context
    if is_fstring and '{' in stripped and '}' in stripped:
        return True

    # Ends with closing quote - this is the last line
    if stripped.endswith(quote) or stripped.endswith(f'{quote})'):
        return True

    # Simple text content (no Python keywords suggesting code)
    keywords = ['def ', 'class ', 'if ', 'for ',
                'while ', 'return ', 'import ', 'from ']
    if not any(stripped.startswith(kw) for kw in keywords):
        return True

    return False


class OperationalValidationError(Exception):
    """Raised when Python files fail operational validation."""
    pass


def validate_python_file(
    file_path: str, verbose: bool = False
) -> Tuple[bool, List[str]]:
    """
    Validate a single Python file.

    Args:
        file_path: Path to the Python file
        verbose: Print progress messages

    Returns:
        Tuple of (passed, errors):
        - passed: True if all checks pass
        - errors: List of error messages (empty if passed)
    """
    path = Path(file_path)
    errors = []

    if not path.exists():
        return False, [f"File not found: {file_path}"]

    if not path.suffix == ".py":
        return False, [f"Not a Python file: {file_path}"]

    try:
        content = path.read_text()
    except Exception as e:
        return False, [f"Cannot read file: {e}"]

    # Stage 1: Content validation
    content_issues = _check_content_issues(content, path.name)
    if content_issues and verbose:
        for issue in content_issues:
            print(f"  [CONTENT] {path.name}: WARN - {issue}")

    # Stage 2: Syntax validation (AST parse)
    syntax_error = _check_syntax(content, path.name)
    if syntax_error:
        errors.append(syntax_error)
        if verbose:
            print(f"  [SYNTAX] {path.name}: FAIL - {syntax_error}")
        return False, errors
    elif verbose:
        print(f"  [SYNTAX] {path.name}: PASS")

    return True, errors


def validate_skill_directory(
    skill_dir: str,
    verbose: bool = False
) -> Dict[str, Any]:
    """
    Validate all Python files in an L++ skill directory.

    Args:
        skill_dir: Path to skill directory (contains src/, *.py)
        verbose: Print progress messages

    Returns:
        Dict with keys:
        - passed: bool - overall pass/fail
        - files_checked: int - number of files validated
        - errors: List[str] - all error messages
        - results: Dict[str, dict] - per-file results
        - feedback: str - human-readable summary
    """
    skill_path = Path(skill_dir)
    results = {
        "passed": True,
        "files_checked": 0,
        "errors": [],
        "results": {},
        "feedback": ""
    }

    if not skill_path.exists():
        results["passed"] = False
        results["errors"].append(f"Directory not found: {skill_dir}")
        results["feedback"] = f"Directory not found: {skill_dir}"
        return results

    # Collect Python files
    py_files = []
    py_files.extend(skill_path.glob("*.py"))
    src_dir = skill_path / "src"
    if src_dir.exists():
        py_files.extend(src_dir.glob("*.py"))

    if not py_files:
        results["feedback"] = "No Python files found"
        return results

    if verbose:
        print(f"[OPERATIONAL] Checking {len(py_files)} Python files")

    # Validate each file
    for py_file in py_files:
        results["files_checked"] += 1
        passed, errors = validate_python_file(str(py_file), verbose)

        results["results"][py_file.name] = {
            "passed": passed,
            "errors": errors
        }

        if not passed:
            results["passed"] = False
            results["errors"].extend(errors)

    # Check structure (COMPUTE_UNITS in compute files)
    compute_files = [f for f in py_files if "_compute.py" in f.name]
    for compute_file in compute_files:
        struct_error = _check_structure(compute_file)
        if struct_error:
            results["passed"] = False
            results["errors"].append(struct_error)
            results["results"][compute_file.name]["errors"].append(
                struct_error)
            if verbose:
                print(
                    f"  [STRUCTURE] {compute_file.name}: "
                    f"FAIL - {struct_error}"
                )
        elif verbose:
            print(f"  [STRUCTURE] {compute_file.name}: PASS")

    # Check import references
    interactive_file = skill_path / "interactive.py"
    if interactive_file.exists():
        import_errors = _check_imports(
            interactive_file, src_dir, compute_files)
        if import_errors:
            results["passed"] = False
            results["errors"].extend(import_errors)
            results["results"]["interactive.py"]["errors"].extend(
                import_errors)
            if verbose:
                for err in import_errors:
                    print(f"  [IMPORT] interactive.py: FAIL - {err}")
        elif verbose:
            print("  [IMPORT] interactive.py: PASS")

    # Build feedback
    results["feedback"] = _build_feedback(results)

    return results


def _check_content_issues(content: str, filename: str) -> List[str]:
    """Check for common LLM generation errors in content."""
    issues = []
    lines = content.split('\n')

    # Check for literal newlines in strings (common LLM error)
    for i, line in enumerate(lines, 1):
        stripped = line.rstrip()
        # Line ending with unclosed quote
        if stripped.endswith(
            (
                'print("',
                "print('",
                '= "',
                "= '",
                'f"',
                "f'",
                'input("',
                "input('"
            )
        ):
            if i < len(lines):
                next_line = lines[i].strip() if i < len(lines) else ""
                if next_line and not next_line.startswith(
                    (
                        '#', 'def ', 'class ', 'if ',
                        'for ', 'while ', '"""', "'''"
                    )
                ):
                    issues.append(
                        f"Line {i}: Possible unclosed string literal")

    # Check for incomplete code markers
    if '...' in content and 'Ellipsis' not in content:
        issues.append("Contains '...' which may indicate incomplete code")

    # Check for placeholder comments
    placeholders = ['# TODO', '# FIXME',
                    '# Add code here', '# Implement', 'pass  #']
    for ph in placeholders:
        if ph.lower() in content.lower():
            issues.append(f"Contains placeholder: {ph}")

    # Check for empty functions
    func_pattern = r'def \w+\([^)]*\):\s*\n\s*pass\s*\n'
    if re.search(func_pattern, content):
        issues.append("Contains empty function with only 'pass'")

    return issues


def _check_syntax(content: str, filename: str) -> Optional[str]:
    """Check Python syntax using AST parser."""
    try:
        ast.parse(content, filename=filename)
        return None
    except SyntaxError as e:
        error_msg = f"Line {e.lineno}: {e.msg}"
        if e.text:
            error_msg += f" -> '{e.text.strip()[:50]}'"
        return f"Syntax error in {filename}: {error_msg}"
    except Exception as e:
        return f"Parse error in {filename}: {e}"


def _check_structure(compute_file: Path) -> Optional[str]:
    """Check compute file has required COMPUTE_UNITS dict."""
    try:
        content = compute_file.read_text()
        tree = ast.parse(content)

        has_compute_units = False
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(
                        target, ast.Name
                    ) and target.id == "COMPUTE_UNITS":
                        has_compute_units = True
                        break

        if not has_compute_units:
            return f"{compute_file.name}: Missing COMPUTE_UNITS dictionary"

        return None
    except Exception as e:
        return f"{compute_file.name}: Cannot check structure - {e}"


def _check_imports(
    interactive_file: Path,
    src_dir: Path,
    compute_files: List[Path]
) -> List[str]:
    """Check interactive.py imports reference existing modules."""
    errors = []

    try:
        content = interactive_file.read_text()

        # Check for src imports
        if "from src." in content:
            import_matches = re.findall(r'from src\.(\w+)', content)
            for mod_name in import_matches:
                mod_file = src_dir / f"{mod_name}.py"
                if not mod_file.exists():
                    errors.append(f"Missing module: src/{mod_name}.py")

        # Check COMPUTE_UNITS reference
        if "COMPUTE_UNITS" in content and not compute_files:
            errors.append(
                "References COMPUTE_UNITS but no compute module found")

    except Exception as e:
        errors.append(f"Cannot check imports: {e}")

    return errors


def _build_feedback(results: Dict[str, Any]) -> str:
    """Build human-readable feedback for LLM correction."""
    if results["passed"]:
        return "Operational validation PASSED: " + \
            f"{results['files_checked']} files valid"

    feedback_parts = ["PYTHON VALIDATION ERRORS - FILES WILL NOT RUN:"]

    for err in results["errors"]:
        feedback_parts.append(f"  • {err}")

    # Add specific fix instructions based on error patterns
    all_errors = " ".join(results["errors"])

    if "EOL while scanning string literal" in all_errors \
            or "unterminated string" in all_errors:
        feedback_parts.append("")
        feedback_parts.append(
            "FIX REQUIRED: You have literal newlines inside strings.")
        feedback_parts.append("WRONG: print(\"Hello")
        feedback_parts.append("       World\")")
        feedback_parts.append("RIGHT: print(\"Hello\\nWorld\")")
        feedback_parts.append(
            "Use \\n for newlines inside strings, NOT actual line breaks!")

    if "Missing COMPUTE_UNITS" in all_errors:
        feedback_parts.append("")
        feedback_parts.append(
            "FIX REQUIRED: Compute module must export COMPUTE_UNITS dict.")
        feedback_parts.append(
            "Add at bottom: COMPUTE_UNITS = {\"process\": process_func, ...}")

    if "Missing module" in all_errors:
        feedback_parts.append("")
        feedback_parts.append(
            "FIX REQUIRED: interactive.py "
            "imports a module that doesn't exist."
        )
        feedback_parts.append(
            "Ensure src/ contains the compute module referenced in import.")

    return "\n".join(feedback_parts)


# Convenience function for build_skill.sh integration
def validate_skill(skill_dir: str, verbose: bool = True) -> bool:
    """
    Validate skill Python files.

    Args:
        skill_dir: Path to skill directory
        verbose: Print progress

    Returns:
        True if all validations pass, False otherwise
    """
    results = validate_skill_directory(skill_dir, verbose)

    if not results["passed"]:
        print(f"\n{results['feedback']}\n")

    return results["passed"]
