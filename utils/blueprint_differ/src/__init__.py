"""
COMPUTE units for L++ Blueprint Differ.

This package provides the computation functions for:
- diff: Semantic diffing and merging of L++ blueprints
"""

from .differ_compute import COMPUTE_REGISTRY as DIFF_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["DIFF_REGISTRY"]
