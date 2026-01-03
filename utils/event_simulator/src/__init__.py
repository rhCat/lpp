"""
COMPUTE units for L++ Event Sequence Simulator.

This package provides the computation functions for:
- sim: Simulation operations (load, dispatch, fork, fuzz, explore)
"""

from .simulator_compute import COMPUTE_REGISTRY as SIM_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["SIM_REGISTRY"]
