"""Run tlaps_prover as a module: python -m lpp.util.tlaps_prover"""
from .cli import main
import sys

if __name__ == "__main__":
    sys.exit(main())
