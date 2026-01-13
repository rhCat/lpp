"""
DEPRECATED: frame_py.tla_validator is deprecated.
Use lpp.core.validators.tla instead.
"""
import warnings
warnings.warn(
    "frame_py.tla_validator is deprecated. Use 'lpp.core.validators.tla' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.validators.tla import *
