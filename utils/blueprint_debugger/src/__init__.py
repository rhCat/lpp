"""
COMPUTE units for L++ Blueprint Debugger.

This package provides the computation functions for:
- debug: Debugging operations (load, step, breakpoint, inspect, time-travel)
"""

from .debugger_compute import COMPUTE_REGISTRY as DEBUG_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["DEBUG_REGISTRY"]
