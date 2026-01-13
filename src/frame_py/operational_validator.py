"""
DEPRECATED: frame_py.operational_validator is deprecated.
Use lpp.core.validators.operational instead.
"""
import warnings
warnings.warn(
    "frame_py.operational_validator is deprecated. Use 'lpp.core.validators.operational' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.validators.operational import *
