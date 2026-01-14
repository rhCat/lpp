"""Run doc_generator as a module: python -m lpp.util.doc_generator"""
from .cli import main
import sys

if __name__ == "__main__":
    sys.exit(main())
