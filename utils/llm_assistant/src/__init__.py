"""
COMPUTE units for L++ LLM Schema Assistant.
Per build_rules.md: Hermetic functions, pure I/O, no global state.
"""

from .llm_compute import COMPUTE_REGISTRY as LLM_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path FIRST (before other imports)
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))


__all__ = ["LLM_REGISTRY"]
