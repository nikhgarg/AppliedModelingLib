#!/usr/bin/env python3
"""Stable CLI for the current graph-native closeout planner."""

from __future__ import annotations

import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.current_closeout.planner import main


if __name__ == "__main__":
    raise SystemExit(main())
