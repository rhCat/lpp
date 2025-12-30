"""Task Orchestrator COMPUTE module."""
from .orchestrator_compute import COMPUTE_REGISTRY

ORCH_REGISTRY = COMPUTE_REGISTRY

__all__ = ["COMPUTE_REGISTRY", "ORCH_REGISTRY"]
