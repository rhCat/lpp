"""Run graph_visualizer as a module: python -m lpp.util.graph_visualizer"""
from .cli import main
import sys

if __name__ == "__main__":
    sys.exit(main())
