"""
COMPUTE units for L++ Test Case Generator.

This package provides the computation functions for:
- testgen: Test generation operations (load, analyze, generate, format, export)
"""

from .test_compute import COMPUTE_REGISTRY as TEST_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["TEST_REGISTRY"]
