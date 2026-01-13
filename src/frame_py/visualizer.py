"""
DEPRECATED: frame_py.visualizer is deprecated.
Use lpp.core.visualizer instead.
"""
import warnings
warnings.warn(
    "frame_py.visualizer is deprecated. Use 'lpp.core.visualizer' instead.",
    DeprecationWarning,
    stacklevel=2
)

from lpp.core.visualizer import *
