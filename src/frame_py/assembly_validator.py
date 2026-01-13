"""
DEPRECATED: frame_py.assembly_validator is deprecated.
Use lpp.core.validators.assembly instead.
"""
import warnings
warnings.warn(
    "frame_py.assembly_validator is deprecated. Use 'lpp.core.validators.assembly' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.validators.assembly import *
