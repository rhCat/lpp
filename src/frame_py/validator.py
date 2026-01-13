"""
DEPRECATED: frame_py.validator is deprecated.
Use lpp.core.validators.blueprint instead.
"""
import warnings
warnings.warn(
    "frame_py.validator is deprecated. Use 'lpp.core.validators.blueprint' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.validators.blueprint import *
