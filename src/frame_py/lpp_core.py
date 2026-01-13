"""
DEPRECATED: frame_py.lpp_core is deprecated.
Use lpp.core.atoms instead.
"""
import warnings
warnings.warn(
    "frame_py.lpp_core is deprecated. Use 'lpp.core.atoms' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.atoms import *
