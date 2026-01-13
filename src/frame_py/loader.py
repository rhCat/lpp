"""
DEPRECATED: frame_py.loader is deprecated.
Use lpp.core.loader instead.
"""
import warnings
warnings.warn(
    "frame_py.loader is deprecated. Use 'lpp.core.loader' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.loader import *
