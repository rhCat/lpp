"""
COMPUTE units for L++ Visualizer example.

This package provides the computation functions for:
- viz: Visualizer operations (load, render, zoom, toggle)
- rdm: README generation operations (header, mermaid, tables, assemble, write)
"""

from .readme_compute import COMPUTE_REGISTRY as README_REGISTRY
from .viz_compute import COMPUTE_REGISTRY as VIZ_REGISTRY
import sys
from pathlib import Path

# Add L++ framework to path
_FRAMEWORK_PATH = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK_PATH) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK_PATH))

__all__ = ["VIZ_REGISTRY", "README_REGISTRY"]
