"""Alias entry point: ``python -m refactorproof.evaluate_reference`` (see survival.py)."""
import sys

from .survival import main

if __name__ == "__main__":
    sys.exit(main())
