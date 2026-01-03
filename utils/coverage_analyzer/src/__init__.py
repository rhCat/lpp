"""
COMPUTE units for L++ Coverage Analyzer.

This package provides the computation functions for:
- cov: Coverage tracking operations (load, record, compute, report, export)
"""

from .coverage_compute import COMPUTE_REGISTRY as COVERAGE_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["COVERAGE_REGISTRY"]
