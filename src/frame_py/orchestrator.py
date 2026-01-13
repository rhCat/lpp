"""
DEPRECATED: frame_py.orchestrator is deprecated.
Use lpp.core.orchestrator instead.
"""
import warnings
warnings.warn(
    "frame_py.orchestrator is deprecated. Use 'lpp.core.orchestrator' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.orchestrator import *
