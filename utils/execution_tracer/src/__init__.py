"""
COMPUTE units for L++ Execution Tracer.

This package provides the computation functions for:
- tracer: Trace recording, formatting, and analysis operations
"""

from .tracer_compute import COMPUTE_REGISTRY as TRACER_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["TRACER_REGISTRY"]
