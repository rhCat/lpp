"""
COMPUTE units for L++ Schema Migrator.

This package provides the computation functions for:
- migrate: Migration operations (load, detect, plan, apply, validate, export)
"""

from .migrator_compute import COMPUTE_REGISTRY as MIGRATE_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["MIGRATE_REGISTRY"]
