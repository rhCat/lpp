"""
COMPUTE units for L++ Compliance Checker.

This package provides the computation functions for:
- compliance: Policy loading, rule evaluation, report generation
"""

from .compliance_compute import COMPLIANCE_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["COMPLIANCE_REGISTRY"]
