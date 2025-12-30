"""
COMPUTE units for Research Scraper.
Hermetic functions for arXiv, Semantic Scholar, and web scraping.
"""

from .scraper_compute import COMPUTE_REGISTRY as SCRAPER_REGISTRY
import sys
from pathlib import Path

_FRAMEWORK = Path(__file__).parent.parent.parent.parent / "src"
if str(_FRAMEWORK) not in sys.path:
    sys.path.insert(0, str(_FRAMEWORK))


__all__ = ["SCRAPER_REGISTRY"]
