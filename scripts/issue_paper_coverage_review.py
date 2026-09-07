#!/usr/bin/env python3
"""Issue a current semantic source-to-dashboard coverage receipt."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard as dashboard  # noqa: E402
from scripts import seed_paper_coverage as seed  # noqa: E402


class CoverageIssueError(RuntimeError):
    """Raised when current source-to-row evidence cannot be issued safely."""


def _load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CoverageIssueError(f"cannot read {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise CoverageIssueError(f"{path} is not a JSON object")
    return payload


def _source_evidence(item: Mapping[str, Any]) -> str:
    anchors = item.get("source_anchor_evidence")
    if not isinstance(anchors, list) or not anchors:
        raise CoverageIssueError("source item has no byte-pinned anchor bundle")
    parts: list[str] = []
    for anchor in anchors:
        if not isinstance(anchor, dict):
            raise CoverageIssueError("source anchor is not an object")
        path = str(anchor.get("path") or "").strip()
        start = anchor.get("line_start")
        end = anchor.get("line_end")
        quote = anchor.get("quoted_text")
        if not path or not isinstance(start, int) or not isinstance(end, int) or not isinstance(quote, str):
            raise CoverageIssueError("source anchor is incomplete")
        parts.append(f"Byte-pinned source anchor {path}:{start}-{end}: {quote}")
    return "\n\n".join(parts)


def issue(folder: Path, decisions: Mapping[str, Any]) -> dict[str, Any]:
    current_hashes = dashboard._cache_source_hashes(folder)
    rows = dashboard.load_cached_review_rows(
        folder, source_hashes=current_hashes, persist_rebind=False
    )
    if rows is None:
        raise CoverageIssueError(
            "dashboard cache is not bound to the current Lean/source surface; "
            "run review_dashboard.py --refresh-cache first"
        )
    _full, inventory, _mode, mode_error = dashboard.paper_coverage_inventory(folder)
    if mode_error:
        raise CoverageIssueError(mode_error)
    rows_by_name = {row.name: row for row in rows}
    for name, prerequisite in (
        dashboard.paper_semantic_prerequisite_coverage_review_items(
            folder,
            inventory,
            rows,
        ).items()
    ):
        if name in rows_by_name:
            raise CoverageIssueError(
                f"coverage target name is ambiguous between a result row and "
                f"paper prerequisite: {name}"
            )
        rows_by_name[name] = prerequisite
    raw_decisions = decisions.get("items")
    if not isinstance(raw_decisions, dict) or set(raw_decisions) != set(inventory):
        missing = sorted(set(inventory) - set(raw_decisions or {}))
        extra = sorted(set(raw_decisions or {}) - set(inventory))
        raise CoverageIssueError(
            f"decisions must cover the exact current inventory; missing={missing}, extra={extra}"
        )

    validator = str(decisions.get("validator") or "").strip()
    validator_type = str(decisions.get("validator_type") or "agent").strip()
    if not validator or not validator_type:
        raise CoverageIssueError("validator and validator_type are required")
    payload = seed.seed_payload(
        folder, validator, validator_type, cached_rows=rows
    )
    validated_at = datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
        "+00:00", "Z"
    )
    payload.update(
        {
            "prompt_version": dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
            "audit_kind": "source_to_dashboard_agent",
            "source_grounded": True,
            "seed_scaffold": False,
            "validator": validator,
            "validator_type": validator_type,
            "validated_at": validated_at,
            "source_input_protocol": "verbatim_source_anchor_bundle_v1",
            "semantic_contract": "paper-coverage-verbatim-source-anchor-proof-row-signature-v6",
            "comment": "Independent source-first review of every selected byte-pinned source item against current transparent Specs or explicit support/nonresult dispositions.",
        }
    )

    for key, item in inventory.items():
        decision = raw_decisions[key]
        if not isinstance(decision, dict):
            raise CoverageIssueError(f"{key}: decision is not an object")
        output = payload["items"][key]
        coverage = str(decision.get("coverage") or "").strip()
        reason = str(decision.get("reason") or "").strip()
        dashboard_evidence = str(decision.get("dashboard_evidence") or "").strip()
        if not coverage or len(reason) < 20 or len(dashboard_evidence) < 20:
            raise CoverageIssueError(f"{key}: coverage, reason, and dashboard evidence are required")
        review_rows = [str(value).strip() for value in decision.get("review_rows", [])]
        support = [str(value).strip() for value in decision.get("support_declarations", [])]
        if any(not value for value in review_rows + support):
            raise CoverageIssueError(f"{key}: empty route name")
        signature_pins: dict[str, str] = {}
        for row_name in review_rows:
            row = rows_by_name.get(row_name)
            if row is None or not dashboard._current_row_signature_digest(row):
                raise CoverageIssueError(f"{key}: current review row unavailable: {row_name}")
            signature_pins[row_name] = dashboard._current_row_signature_digest(row)
        anchor_identity, anchor_error = dashboard.source_anchor_quote_identity(item)
        if anchor_error:
            raise CoverageIssueError(f"{key}: {anchor_error}")
        output.update(
            {
                "coverage": coverage,
                "review_rows": review_rows,
                "review_row_signature_sha256": signature_pins,
                "support_declarations": support,
                "reason": reason,
                "source_evidence": _source_evidence(item),
                "dashboard_evidence": dashboard_evidence,
                "source_anchor_quote_identity_sha256": anchor_identity,
                "audit_kind": "source_to_dashboard_agent",
                "source_grounded": True,
                "seed_scaffold": False,
                "validator": validator,
                "validator_type": validator_type,
                "validated_at": validated_at,
            }
        )
        # A corrected-target judgment is pinned to the approved mathematical
        # target, while retaining the archival source statement separately.
        # The generic seed scaffold stores the archival statement digest, so
        # an evidence issuer must replace that transport field and record the
        # complete correction identity rather than leaving a receipt that is
        # stale at creation time.
        _coverage_statement, coverage_statement_sha256 = (
            dashboard._source_item_coverage_statement(dict(item))
        )
        output["statement_sha256"] = coverage_statement_sha256
        if dashboard._source_item_is_corrected_target(dict(item)):
            corrected_target = dashboard._source_item_corrected_target(dict(item))
            if not isinstance(corrected_target, dict):
                raise CoverageIssueError(
                    f"{key}: corrected source item has no approved target record"
                )
            output.update(
                {
                    "target_kind": dashboard.CORRECTED_TARGET_ROUTE_KIND,
                    "archival_statement_sha256": str(
                        item.get("statement_sha256") or ""
                    ).strip().lower(),
                    "corrected_target_sha256": dashboard.corrected_target_digest(
                        corrected_target
                    ),
                    "governing_defect_ids": dashboard._normalize_string_list(
                        corrected_target.get("governing_defect_ids")
                    ),
                    "archival_equivalence_claimed": False,
                }
            )
        if str(item.get("source_scope_classification") or "").strip():
            quote, quote_error = dashboard._source_inventory_anchor_quote_text(item)
            if quote_error:
                raise CoverageIssueError(f"{key}: {quote_error}")
            output["source_scope_judgment"] = str(
                decision.get("source_scope_judgment") or ""
            ).strip()
            output["source_anchor_quote_sha256"] = hashlib.sha256(
                quote.encode("utf-8")
            ).hexdigest()
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--decisions", required=True, type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    folder = ROOT / "papers" / args.paper
    payload = issue(folder, _load_json(args.decisions))
    rendered = json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    if args.write:
        target = folder / "audit" / "paper_coverage_llm.json"
        target.write_text(rendered, encoding="utf-8")
        print(target.relative_to(ROOT))
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
