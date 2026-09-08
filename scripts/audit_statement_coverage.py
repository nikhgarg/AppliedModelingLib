#!/usr/bin/env python3
"""Run CI statement/coverage checks against each paper's canonical evidence.

Accepted obligation graphs bind source coverage, source-to-Spec judgments and
the current Lean dependency closure. Their strict validator owns these checks;
reconstructing old dashboard rows is not another source of acceptance. Papers
without a graph credential retain the historical row-level audit.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Sequence

if __package__ in {None, ""}:
    repository_root = str(Path(__file__).resolve().parents[1])
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts import audit_evidence_integrity, review_dashboard


def audit_paper(folder: Path, kind: str, *, require_source_bytes: bool = True) -> bool:
    """Return whether the selected gate fails; never fall back from a bad graph."""

    if kind not in {"statement", "coverage"}:
        raise ValueError(f"unknown audit kind: {kind}")
    findings = audit_evidence_integrity.graph_native_closure_fast_path_findings(
        folder, release=False, require_source_bytes=require_source_bytes,
    )
    if findings is not None:
        failed = False
        for finding in findings:
            print(f"{finding.severity} {folder.name}: {finding.message}", flush=True)
            failed = failed or finding.severity == "ERROR"
        if not failed:
            print(
                f"{folder.name}: {kind} audit current under the validated accepted graph.",
                flush=True,
            )
        return failed

    legacy_check = (
        review_dashboard.print_statement_audit_status
        if kind == "statement"
        else review_dashboard.print_paper_coverage_audit_status
    )
    return legacy_check(folder.name)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--kind", choices=("statement", "coverage"), required=True)
    parser.add_argument("--paper", help="Check one paper instead of the normal dashboard cohort.")
    parser.add_argument(
        "--allow-missing-source-bytes", action="store_true",
        help="Validate the public source projection when private source artifacts are absent.",
    )
    args = parser.parse_args(argv)
    folders = review_dashboard.iter_paper_folders(args.paper)
    if not folders:
        parser.error("no paper review surfaces selected")
    failures = 0
    for folder in folders:
        print(f"Checking {args.kind} evidence: {folder.name}", flush=True)
        try:
            failed = audit_paper(
                folder, args.kind,
                require_source_bytes=not args.allow_missing_source_bytes,
            )
        except (OSError, RuntimeError, ValueError) as exc:
            print(f"ERROR {folder.name}: {exc}", flush=True)
            failed = True
        failures += int(failed)
    print(f"{args.kind.capitalize()} audit: {failures} failed paper(s) across {len(folders)} paper(s).")
    return int(bool(failures))


if __name__ == "__main__":
    raise SystemExit(main())
