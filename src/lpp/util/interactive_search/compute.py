"""
Interactive Search Compute Functions

Provides search, refinement, and export capabilities for the
refined interactive search tool.
"""

import os
import re
import json
import fnmatch
from pathlib import Path
from typing import Dict, List, Any, Optional
from dataclasses import dataclass, asdict
from datetime import datetime


@dataclass
class SearchMatch:
    """A single search match."""
    file: str
    line_number: int
    line_content: str
    context_before: List[str]
    context_after: List[str]
    match_start: int
    match_end: int
    score: float = 1.0


@dataclass
class SearchResult:
    """Aggregated results for a file."""
    file: str
    matches: List[Dict]
    match_count: int
    preview: str


def init(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Initialize search session with defaults.

    Input:
        searchPath: Optional starting path

    Output:
        path: Resolved search path
        excludes: Default exclude patterns
        context: Default context lines
        maxResults: Default max results
        history: Empty query history
    """
    search_path = params.get("searchPath") or os.getcwd()

    # Resolve path
    path = Path(search_path).resolve()
    if not path.exists():
        path = Path.cwd()

    return {
        "path": str(path),
        "excludes": [
            "**/node_modules/**",
            "**/.git/**",
            "**/__pycache__/**",
            "**/venv/**",
            "**/.venv/**",
            "**/dist/**",
            "**/build/**",
            "**/*.pyc",
            "**/*.min.js",
            "**/*.min.css",
        ],
        "context": 2,
        "maxResults": 100,
        "history": [],
    }


def execute(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Execute search query.

    Input:
        searchPath: Path to search
        query: Search query
        filePattern: Glob pattern for files
        excludePatterns: Patterns to exclude
        caseSensitive: Case-sensitive flag
        useRegex: Regex flag
        contextLines: Lines of context
        maxResults: Max results

    Output:
        results: List of SearchResult dicts
        count: Total match count
        files: File count with matches
        error: Error message if any
    """
    search_path = params.get("searchPath", ".")
    query = params.get("query", "")
    file_pattern = params.get("filePattern", "*")
    exclude_patterns = params.get("excludePatterns", [])
    case_sensitive = params.get("caseSensitive", False)
    use_regex = params.get("useRegex", False)
    context_lines = params.get("contextLines", 2)
    max_results = params.get("maxResults", 100)

    if not query:
        return {"results": [], "count": 0, "files": 0, "error": None}

    try:
        # Compile pattern
        flags = 0 if case_sensitive else re.IGNORECASE
        if use_regex:
            pattern = re.compile(query, flags)
        else:
            # Escape special chars for literal search
            pattern = re.compile(re.escape(query), flags)

        results = []
        total_matches = 0
        files_with_matches = set()

        # Walk directory
        root = Path(search_path)
        for file_path in _find_files(root, file_pattern, exclude_patterns):
            if total_matches >= max_results:
                break

            file_matches = _search_file(
                file_path, pattern, context_lines, max_results - total_matches
            )

            if file_matches:
                files_with_matches.add(str(file_path))
                total_matches += len(file_matches)

                # Create preview from first match
                first = file_matches[0]
                preview = f"L{first['line_number']}: {first['line_content'][:80]}"

                results.append({
                    "file": str(file_path.relative_to(root)),
                    "matches": file_matches,
                    "match_count": len(file_matches),
                    "preview": preview,
                })

        return {
            "results": results,
            "count": total_matches,
            "files": len(files_with_matches),
            "error": None,
        }

    except re.error as e:
        return {
            "results": [],
            "count": 0,
            "files": 0,
            "error": f"Invalid regex: {e}",
        }
    except Exception as e:
        return {
            "results": [],
            "count": 0,
            "files": 0,
            "error": str(e),
        }


def _find_files(
    root: Path,
    pattern: str,
    excludes: List[str]
) -> List[Path]:
    """Find files matching pattern, excluding specified patterns."""
    files = []

    # Handle multiple patterns (comma-separated)
    patterns = [p.strip() for p in pattern.split(",")]

    for path in root.rglob("*"):
        if not path.is_file():
            continue

        # Check if file matches any pattern
        rel_path = str(path.relative_to(root))
        matches_pattern = any(
            fnmatch.fnmatch(path.name, p) or fnmatch.fnmatch(rel_path, p)
            for p in patterns
        )

        if not matches_pattern:
            continue

        # Check excludes
        excluded = any(
            fnmatch.fnmatch(rel_path, exc) or fnmatch.fnmatch(str(path), exc)
            for exc in excludes
        )

        if excluded:
            continue

        # Skip binary files
        if _is_binary(path):
            continue

        files.append(path)

    return sorted(files)


def _is_binary(path: Path) -> bool:
    """Check if file is binary."""
    try:
        with open(path, "rb") as f:
            chunk = f.read(8192)
            return b"\x00" in chunk
    except Exception:
        return True


def _search_file(
    path: Path,
    pattern: re.Pattern,
    context_lines: int,
    max_matches: int
) -> List[Dict]:
    """Search a single file for pattern matches."""
    matches = []

    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            lines = f.readlines()

        for i, line in enumerate(lines):
            if len(matches) >= max_matches:
                break

            match = pattern.search(line)
            if match:
                # Get context
                start = max(0, i - context_lines)
                end = min(len(lines), i + context_lines + 1)

                matches.append({
                    "line_number": i + 1,
                    "line_content": line.rstrip(),
                    "context_before": [l.rstrip() for l in lines[start:i]],
                    "context_after": [l.rstrip() for l in lines[i + 1:end]],
                    "match_start": match.start(),
                    "match_end": match.end(),
                    "score": _calculate_score(line, match),
                })

    except Exception:
        pass

    return matches


def _calculate_score(line: str, match: re.Match) -> float:
    """Calculate relevance score for a match."""
    score = 1.0

    # Boost for whole word match
    start, end = match.start(), match.end()
    if (start == 0 or not line[start - 1].isalnum()) and \
       (end == len(line) or not line[end].isalnum()):
        score += 0.5

    # Boost for match at start of line (after whitespace)
    stripped = line.lstrip()
    if line.find(stripped) == start:
        score += 0.3

    # Penalty for very long lines
    if len(line) > 200:
        score -= 0.2

    return round(score, 2)


def getDetail(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Get detailed view of a search result.

    Input:
        results: List of search results
        index: Selected result index

    Output:
        detail: Detailed result with full context
        error: Error message if any
    """
    results = params.get("results", [])
    index = params.get("index", 0)

    if not results:
        return {"detail": None, "error": "No results"}

    if index < 0 or index >= len(results):
        return {"detail": None, "error": f"Invalid index: {index}"}

    result = results[index]
    file_path = result.get("file", "")

    # Read full file content around matches
    try:
        with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
            lines = f.readlines()

        # Expand context for detailed view
        expanded_matches = []
        for match in result.get("matches", []):
            line_num = match["line_number"]
            start = max(0, line_num - 6)
            end = min(len(lines), line_num + 5)

            expanded_matches.append({
                **match,
                "full_context": [
                    {"line": i + 1, "content": lines[i].rstrip()}
                    for i in range(start, end)
                ],
            })

        return {
            "detail": {
                "file": file_path,
                "total_lines": len(lines),
                "matches": expanded_matches,
                "match_count": len(expanded_matches),
            },
            "error": None,
        }

    except Exception as e:
        return {"detail": None, "error": str(e)}


def refine(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Apply refinement to search query.

    Input:
        query: Current query
        type: Refinement type (narrow, expand, filter, exclude, filetype)
        value: Refinement value
        history: Query history

    Output:
        newQuery: Updated query
        history: Updated history
        filePattern: Updated file pattern (if type=filetype)
        excludes: Updated excludes (if type=exclude)
    """
    query = params.get("query", "")
    ref_type = params.get("type", "narrow")
    value = params.get("value", "")
    history = params.get("history", [])

    new_query = query
    file_pattern = None
    excludes = None

    if ref_type == "narrow":
        # Add term to narrow results
        new_query = f"{query} {value}".strip()

    elif ref_type == "expand":
        # OR with new term
        new_query = f"({query})|({value})"

    elif ref_type == "filter":
        # Filter to specific term
        new_query = value

    elif ref_type == "exclude":
        # Negative lookahead to exclude
        new_query = f"(?!.*{re.escape(value)}){query}"

    elif ref_type == "filetype":
        # Set file pattern
        file_pattern = value

    elif ref_type == "regex":
        # Convert to regex mode
        new_query = value

    return {
        "newQuery": new_query,
        "history": history,
        "filePattern": file_pattern,
        "excludes": excludes,
    }


def recordQuery(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Record query in history.

    Input:
        query: Current query
        history: Existing history
        count: Result count

    Output:
        history: Updated history
    """
    query = params.get("query", "")
    history = params.get("history", []) or []
    count = params.get("count", 0)

    # Add to history
    entry = {
        "query": query,
        "count": count,
        "timestamp": datetime.now().isoformat(),
    }

    # Keep last 20 entries, avoid duplicates
    new_history = [e for e in history if e.get("query") != query]
    new_history.append(entry)
    new_history = new_history[-20:]

    return {"history": new_history}


def export(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    Export search results.

    Input:
        results: Search results
        query: Search query
        path: Export path
        format: Export format (json, csv, markdown)

    Output:
        exported: Path to exported file
        error: Error message if any
    """
    results = params.get("results", [])
    query = params.get("query", "")
    export_path = params.get("path", "search_results.json")
    export_format = params.get("format", "json")

    try:
        path = Path(export_path)

        if export_format == "json":
            data = {
                "query": query,
                "exported_at": datetime.now().isoformat(),
                "result_count": sum(r["match_count"] for r in results),
                "file_count": len(results),
                "results": results,
            }
            with open(path, "w") as f:
                json.dump(data, f, indent=2)

        elif export_format == "csv":
            import csv
            with open(path, "w", newline="") as f:
                writer = csv.writer(f)
                writer.writerow(["File", "Line", "Content", "Score"])
                for result in results:
                    for match in result["matches"]:
                        writer.writerow([
                            result["file"],
                            match["line_number"],
                            match["line_content"],
                            match.get("score", 1.0),
                        ])

        elif export_format == "markdown":
            with open(path, "w") as f:
                f.write(f"# Search Results: `{query}`\n\n")
                f.write(f"Exported: {datetime.now().isoformat()}\n\n")
                f.write(f"**{sum(r['match_count'] for r in results)}** ")
                f.write(f"matches in **{len(results)}** files\n\n")

                for result in results:
                    f.write(f"## {result['file']}\n\n")
                    for match in result["matches"]:
                        f.write(f"**Line {match['line_number']}:**\n")
                        f.write(f"```\n{match['line_content']}\n```\n\n")

        return {"exported": str(path), "error": None}

    except Exception as e:
        return {"exported": None, "error": str(e)}


# Compute registry for L++ framework
COMPUTE_REGISTRY = {
    "search:init": init,
    "search:execute": execute,
    "search:getDetail": getDetail,
    "search:refine": refine,
    "search:recordQuery": recordQuery,
    "search:export": export,
}
