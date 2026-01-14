#!/usr/bin/env python3
"""
Interactive Search CLI

A refined interactive search tool with iterative refinement capabilities.

Usage:
    lpp-search [path] [query]           # Start search
    lpp-search --help                   # Show help

Interactive Commands:
    /s <query>    - New search
    /n <term>     - Narrow (add term)
    /e <term>     - Expand (OR with term)
    /f <pattern>  - Filter files (e.g., *.py)
    /x <term>     - Exclude term
    /r            - Toggle regex mode
    /c            - Toggle case sensitivity
    /<number>     - View result details
    /b            - Back to results
    /h            - Show history
    /w <path>     - Export results
    /q            - Quit
"""

import sys
import os
import json
import argparse
from pathlib import Path
from typing import Optional, Dict, Any

# ANSI colors
class Colors:
    HEADER = "\033[95m"
    BLUE = "\033[94m"
    CYAN = "\033[96m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    BOLD = "\033[1m"
    DIM = "\033[2m"
    UNDERLINE = "\033[4m"
    END = "\033[0m"


def colored(text: str, color: str) -> str:
    """Apply color if terminal supports it."""
    if sys.stdout.isatty():
        return f"{color}{text}{Colors.END}"
    return text


class InteractiveSearch:
    """Interactive search session manager."""

    def __init__(self, search_path: str = "."):
        self.search_path = Path(search_path).resolve()
        self.query = ""
        self.results = []
        self.result_count = 0
        self.file_count = 0
        self.file_pattern = "*"
        self.exclude_patterns = []
        self.case_sensitive = False
        self.use_regex = False
        self.context_lines = 2
        self.max_results = 100
        self.query_history = []
        self.selected_index = -1

        # Import compute functions
        from .compute import COMPUTE_REGISTRY
        self.compute = COMPUTE_REGISTRY

        # Initialize
        result = self.compute[("search", "init")]({"searchPath": str(self.search_path)})
        self.search_path = Path(result["path"])
        self.exclude_patterns = result["excludes"]
        self.context_lines = result["context"]
        self.max_results = result["maxResults"]

    def search(self, query: str) -> None:
        """Execute a search."""
        self.query = query
        print(colored(f"\nSearching for: {query}", Colors.CYAN))
        print(colored(f"In: {self.search_path}", Colors.DIM))

        if self.use_regex:
            print(colored("Mode: regex", Colors.DIM))
        if self.case_sensitive:
            print(colored("Mode: case-sensitive", Colors.DIM))
        if self.file_pattern != "*":
            print(colored(f"Files: {self.file_pattern}", Colors.DIM))

        result = self.compute[("search", "execute")]({
            "searchPath": str(self.search_path),
            "query": query,
            "filePattern": self.file_pattern,
            "excludePatterns": self.exclude_patterns,
            "caseSensitive": self.case_sensitive,
            "useRegex": self.use_regex,
            "contextLines": self.context_lines,
            "maxResults": self.max_results,
        })

        if result.get("error"):
            print(colored(f"Error: {result['error']}", Colors.RED))
            return

        self.results = result["results"]
        self.result_count = result["count"]
        self.file_count = result["files"]

        # Record in history
        self.compute[("search", "recordQuery")]({
            "query": query,
            "history": self.query_history,
            "count": self.result_count,
        })
        self.query_history.append({
            "query": query,
            "count": self.result_count,
        })

        self._display_results()

    def _display_results(self) -> None:
        """Display search results."""
        print()
        if not self.results:
            print(colored("No matches found.", Colors.YELLOW))
            return

        print(colored(
            f"Found {self.result_count} matches in {self.file_count} files",
            Colors.GREEN
        ))
        print()

        for i, result in enumerate(self.results[:20]):  # Show first 20
            file_display = result["file"]
            if len(file_display) > 60:
                file_display = "..." + file_display[-57:]

            count = result["match_count"]
            preview = result["preview"]
            if len(preview) > 60:
                preview = preview[:57] + "..."

            print(f"  {colored(f'[{i}]', Colors.CYAN)} {file_display}")
            print(f"      {colored(f'{count} match(es)', Colors.DIM)} - {preview}")

        if len(self.results) > 20:
            print(colored(f"\n  ... and {len(self.results) - 20} more files", Colors.DIM))

        print()

    def show_detail(self, index: int) -> None:
        """Show detailed view of a result."""
        if index < 0 or index >= len(self.results):
            print(colored(f"Invalid index: {index}", Colors.RED))
            return

        self.selected_index = index
        result = self.results[index]

        print()
        print(colored(f"File: {result['file']}", Colors.BOLD))
        print(colored(f"Matches: {result['match_count']}", Colors.DIM))
        print()

        for match in result["matches"][:10]:  # Show first 10 matches
            line_num = match["line_number"]

            # Show context before
            for ctx in match.get("context_before", []):
                print(colored(f"  {' ' * 6} {ctx}", Colors.DIM))

            # Show matching line with highlight
            line = match["line_content"]
            start = match.get("match_start", 0)
            end = match.get("match_end", len(line))

            highlighted = (
                line[:start] +
                colored(line[start:end], Colors.YELLOW + Colors.BOLD) +
                line[end:]
            )
            print(f"  {colored(str(line_num).rjust(5), Colors.CYAN)}:{highlighted}")

            # Show context after
            for ctx in match.get("context_after", []):
                print(colored(f"  {' ' * 6} {ctx}", Colors.DIM))

            print()

        if len(result["matches"]) > 10:
            print(colored(f"  ... and {len(result['matches']) - 10} more matches", Colors.DIM))

        print()
        print(colored("Commands: /b (back), /<n> (next result), /q (quit)", Colors.DIM))

    def refine(self, ref_type: str, value: str) -> None:
        """Apply refinement to search."""
        result = self.compute[("search", "refine")]({
            "query": self.query,
            "type": ref_type,
            "value": value,
            "history": self.query_history,
        })

        new_query = result.get("newQuery", self.query)
        if result.get("filePattern"):
            self.file_pattern = result["filePattern"]

        print(colored(f"Refined: {new_query}", Colors.CYAN))
        self.search(new_query)

    def export(self, path: str, fmt: str = "json") -> None:
        """Export results."""
        result = self.compute[("search", "export")]({
            "results": self.results,
            "query": self.query,
            "path": path,
            "format": fmt,
        })

        if result.get("error"):
            print(colored(f"Export error: {result['error']}", Colors.RED))
        else:
            print(colored(f"Exported to: {result['exported']}", Colors.GREEN))

    def show_history(self) -> None:
        """Show query history."""
        print()
        print(colored("Query History:", Colors.BOLD))
        for i, entry in enumerate(self.query_history[-10:]):
            print(f"  {i + 1}. {entry['query']} ({entry['count']} results)")
        print()

    def run(self, initial_query: Optional[str] = None) -> None:
        """Run interactive session."""
        print(colored("\n=== L++ Interactive Search ===", Colors.BOLD + Colors.CYAN))
        print(colored(f"Path: {self.search_path}", Colors.DIM))
        print(colored("Type /h for help, /q to quit", Colors.DIM))
        print()

        if initial_query:
            self.search(initial_query)

        while True:
            try:
                prompt = colored("search> ", Colors.GREEN)
                if self.selected_index >= 0:
                    prompt = colored("detail> ", Colors.BLUE)

                user_input = input(prompt).strip()

                if not user_input:
                    continue

                # Handle commands
                if user_input.startswith("/"):
                    self._handle_command(user_input)
                else:
                    # New search
                    self.selected_index = -1
                    self.search(user_input)

            except KeyboardInterrupt:
                print("\n")
                break
            except EOFError:
                break

        print(colored("\nGoodbye!", Colors.CYAN))

    def _handle_command(self, cmd: str) -> None:
        """Handle a command."""
        parts = cmd[1:].split(maxsplit=1)
        action = parts[0].lower() if parts else ""
        arg = parts[1] if len(parts) > 1 else ""

        if action == "q" or action == "quit":
            raise EOFError()

        elif action == "h" or action == "help":
            self._show_help()

        elif action == "s" or action == "search":
            if arg:
                self.selected_index = -1
                self.search(arg)
            else:
                print(colored("Usage: /s <query>", Colors.YELLOW))

        elif action == "n" or action == "narrow":
            if arg:
                self.refine("narrow", arg)
            else:
                print(colored("Usage: /n <term>", Colors.YELLOW))

        elif action == "e" or action == "expand":
            if arg:
                self.refine("expand", arg)
            else:
                print(colored("Usage: /e <term>", Colors.YELLOW))

        elif action == "f" or action == "filter":
            if arg:
                self.file_pattern = arg
                self.search(self.query)
            else:
                print(colored("Usage: /f <pattern> (e.g., *.py)", Colors.YELLOW))

        elif action == "x" or action == "exclude":
            if arg:
                self.refine("exclude", arg)
            else:
                print(colored("Usage: /x <term>", Colors.YELLOW))

        elif action == "r" or action == "regex":
            self.use_regex = not self.use_regex
            mode = "enabled" if self.use_regex else "disabled"
            print(colored(f"Regex mode {mode}", Colors.CYAN))
            if self.query:
                self.search(self.query)

        elif action == "c" or action == "case":
            self.case_sensitive = not self.case_sensitive
            mode = "enabled" if self.case_sensitive else "disabled"
            print(colored(f"Case sensitivity {mode}", Colors.CYAN))
            if self.query:
                self.search(self.query)

        elif action == "b" or action == "back":
            self.selected_index = -1
            self._display_results()

        elif action == "w" or action == "write":
            if arg:
                fmt = "json"
                if arg.endswith(".csv"):
                    fmt = "csv"
                elif arg.endswith(".md"):
                    fmt = "markdown"
                self.export(arg, fmt)
            else:
                self.export("search_results.json", "json")

        elif action == "history":
            self.show_history()

        elif action.isdigit():
            self.show_detail(int(action))

        else:
            print(colored(f"Unknown command: /{action}", Colors.RED))
            print(colored("Type /h for help", Colors.DIM))

    def _show_help(self) -> None:
        """Show help."""
        print("""
Interactive Search Commands:

  Search:
    <query>         New search (without /)
    /s <query>      New search
    /n <term>       Narrow results (AND)
    /e <term>       Expand results (OR)
    /x <term>       Exclude term

  Filters:
    /f <pattern>    Filter by file pattern (e.g., *.py, *.json)
    /r              Toggle regex mode
    /c              Toggle case sensitivity

  Navigation:
    /<number>       View result details
    /b              Back to results list

  Other:
    /w [path]       Export results (json/csv/md)
    /history        Show query history
    /h              Show this help
    /q              Quit
""")


def main(argv=None) -> int:
    """Main entry point."""
    parser = argparse.ArgumentParser(
        prog="lpp-search",
        description="L++ Interactive Search - Refined search with iterative refinement",
    )
    parser.add_argument(
        "path",
        nargs="?",
        default=".",
        help="Path to search in (default: current directory)",
    )
    parser.add_argument(
        "query",
        nargs="?",
        help="Initial search query",
    )
    parser.add_argument(
        "-p", "--pattern",
        default="*",
        help="File pattern to search (e.g., *.py)",
    )
    parser.add_argument(
        "-i", "--ignore-case",
        action="store_true",
        help="Case-insensitive search (default)",
    )
    parser.add_argument(
        "-c", "--case-sensitive",
        action="store_true",
        help="Case-sensitive search",
    )
    parser.add_argument(
        "-r", "--regex",
        action="store_true",
        help="Treat query as regex",
    )
    parser.add_argument(
        "-n", "--max-results",
        type=int,
        default=100,
        help="Maximum results (default: 100)",
    )

    args = parser.parse_args(argv)

    search = InteractiveSearch(args.path)
    search.file_pattern = args.pattern
    search.case_sensitive = args.case_sensitive
    search.use_regex = args.regex
    search.max_results = args.max_results

    search.run(args.query)
    return 0


if __name__ == "__main__":
    sys.exit(main())
