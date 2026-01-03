"""
COMPUTE units for L++ Blueprint Registry.

This package provides the computation functions for:
- bpreg: Blueprint registry operations (register, update, search, version control)
"""

from .registry_compute import COMPUTE_REGISTRY as BPREG_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["BPREG_REGISTRY"]
