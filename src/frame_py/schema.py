"""
DEPRECATED: frame_py.schema is deprecated.
Use lpp.core.schema instead.
"""
import warnings
warnings.warn(
    "frame_py.schema is deprecated. Use 'lpp.core.schema' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.schema import *
