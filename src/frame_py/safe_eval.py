"""
DEPRECATED: frame_py.safe_eval is deprecated.
Use lpp.core.safe_eval instead.
"""
import warnings
warnings.warn(
    "frame_py.safe_eval is deprecated. Use 'lpp.core.safe_eval' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.safe_eval import *
