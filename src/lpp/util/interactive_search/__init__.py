"""
L++ Interactive Search

A refined interactive search tool with iterative refinement capabilities.

Usage:
    from lpp.util.interactive_search import InteractiveSearch

    search = InteractiveSearch("/path/to/search")
    search.run("initial query")

CLI:
    lpp-search [path] [query]
    lpp-search --help
"""

from .compute import COMPUTE_REGISTRY
from .cli import InteractiveSearch, main

__all__ = [
    "COMPUTE_REGISTRY",
    "InteractiveSearch",
    "main",
]
