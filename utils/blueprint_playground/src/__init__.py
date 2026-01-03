"""
COMPUTE units for L++ Blueprint Playground.

This package provides the computation functions for:
- play: Playground operations (load, validate, format, simulate, share)
"""

from .playground_compute import COMPUTE_REGISTRY as PLAY_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["PLAY_REGISTRY"]
