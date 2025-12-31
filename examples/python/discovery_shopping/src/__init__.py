"""Discovery Shopping compute module."""

from .shopping_compute import COMPUTE_REGISTRY
from .shopping_view import renderPage

__all__ = ["COMPUTE_REGISTRY", "renderPage"]
