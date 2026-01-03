"""
COMPUTE units for L++ Documentation Generator.

This package provides the computation functions for:
- doc: Documentation generation operations (load, extract, generate, assemble, export)
"""

from .doc_compute import COMPUTE_REGISTRY as DOC_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["DOC_REGISTRY"]
