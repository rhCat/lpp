"""
DEPRECATED: frame_py.compiler is deprecated.
Use lpp.core.compiler instead.
"""
import warnings
warnings.warn(
    "frame_py.compiler is deprecated. Use 'lpp.core.compiler' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.compiler import *
