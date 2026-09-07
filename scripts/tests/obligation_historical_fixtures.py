"""Frozen paper evidence inputs for obligation projection unit tests.

These private snapshots preserve historical review inputs for regression tests.
Their provenance stays with the private fixtures. Public distributions omit the
snapshots and retain the synthetic tests. Tests must not read these inputs from
mutable paper closeout directories.
"""

from __future__ import annotations

import json
import unittest
from pathlib import Path
from typing import Any


FIXTURE_ROOT = Path(__file__).resolve().parent / "fixtures"

IM05_PAPER = "IM05MarriageHonestyStability"
IM05_REPOSITORY_ROOT = FIXTURE_ROOT / "obligation_im05_2026_09_03"
IM05_PAPER_DIR = IM05_REPOSITORY_ROOT / "papers" / IM05_PAPER
IM05_AUDIT_DIR = IM05_PAPER_DIR / "audit"

GKGMM_PAPER_DIR = (
    FIXTURE_ROOT
    / "obligation_gkgmm_2026_08_25"
    / "papers"
    / "GKGMM19IterativeLocalVoting"
)
NOOTHIGATTU_PAPER_DIR = (
    FIXTURE_ROOT
    / "obligation_noothigattu_2026_08_26"
    / "papers"
    / "NoothigattuEtAl2020PairwiseComparisons"
)
SESHADRI_PAPER_DIR = (
    FIXTURE_ROOT
    / "obligation_seshadri_2026_08_27"
    / "papers"
    / "SeshadriUgander2020IIATesting"
)


def load_audit_json(paper_dir: Path, name: str) -> dict[str, Any]:
    """Load one fresh copy of a frozen historical audit input."""

    require_historical_fixture(paper_dir)
    path = paper_dir / "audit" / name
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"frozen obligation fixture is not an object: {path}")
    return value


def load_im05_audit_json(name: str) -> dict[str, Any]:
    require_im05_fixture()
    return load_audit_json(IM05_PAPER_DIR, name)


def require_im05_fixture() -> None:
    """Keep source-backed private regressions optional in the public package."""

    require_historical_fixture(IM05_REPOSITORY_ROOT)


def require_historical_fixture(folder: Path) -> None:
    """Skip only integrations whose complete private snapshot was omitted."""

    if not folder.is_dir():
        raise unittest.SkipTest("private historical review fixture is not distributed publicly")
