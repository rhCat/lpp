"""
COMPUTE units for L++ Blueprint Composer.

This package provides the computation functions for:
- compose: Hierarchical blueprint composition and embedding
"""

from .composer_compute import COMPUTE_REGISTRY as COMPOSE_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["COMPOSE_REGISTRY"]
