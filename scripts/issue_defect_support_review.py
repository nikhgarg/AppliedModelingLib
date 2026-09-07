#!/usr/bin/env python3
"""Issue exact Lean-bound judgments for quarantined source-defect support."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard as dashboard  # noqa: E402


class DefectSupportIssueError(RuntimeError):
    """Raised when a requested semantic receipt cannot be issued safely."""


def _load_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise DefectSupportIssueError(f"cannot read {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise DefectSupportIssueError(f"{path} is not a JSON object")
    return payload


def issue(folder: Path, decisions: Mapping[str, Any]) -> dict[str, Any]:
    """Materialize reviewer decisions against current source and Lean inputs."""

    statement_map = dashboard.paper_statement_map_payload(folder)
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, dict):
        raise DefectSupportIssueError("paper statement map has no item dictionary")
    _full, inventory, _mode, mode_error = dashboard.paper_coverage_inventory(folder)
    if mode_error:
        raise DefectSupportIssueError(mode_error)

    fidelity = _load_json(folder / "audit" / "source_proof_fidelity.json")
    defects = {
        str(raw.get("id") or "").strip(): raw
        for raw in fidelity.get("defects", [])
        if isinstance(raw, dict) and str(raw.get("id") or "").strip()
    }

    # Loading current rows also authenticates and restores the separately
    # cached quarantined-support surface. It does not add those rows to the
    # human dashboard denominator.
    current_hashes = dashboard._cache_source_hashes(folder)
    if dashboard.load_cached_review_rows(
        folder,
        source_hashes=current_hashes,
        persist_rebind=False,
    ) is None:
        raise DefectSupportIssueError(
            "dashboard cache is not bound to the current Lean/source surface; "
            "run review_dashboard.py --refresh-cache first"
        )
    support_rows = dashboard.quarantined_support_review_items(folder)
    raw_decisions = decisions.get("items")
    if not isinstance(raw_decisions, dict) or not raw_decisions:
        raise DefectSupportIssueError("decision ledger has no item decisions")

    issued: dict[str, Any] = {}
    seen_pairs: set[tuple[str, str, str]] = set()
    for key, raw_decision in sorted(raw_decisions.items()):
        if not isinstance(raw_decision, dict):
            raise DefectSupportIssueError(f"{key}: decision is not an object")
        source_key = str(raw_decision.get("source_item") or "").strip()
        defect_id = str(raw_decision.get("defect_id") or "").strip()
        support_name = str(raw_decision.get("support_declaration") or "").strip()
        source_item = inventory.get(source_key)
        defect = defects.get(defect_id)
        row = support_rows.get(support_name) or support_rows.get(
            support_name.rsplit(".", 1)[-1]
        )
        if source_item is None or defect is None or row is None:
            raise DefectSupportIssueError(
                f"{key}: unknown source item, defect, or quarantined support row"
            )
        pair = (source_key, defect_id, row.name)
        if pair in seen_pairs:
            raise DefectSupportIssueError(f"{key}: duplicate semantic support pair")
        seen_pairs.add(pair)

        manifest = row.lean_signature_manifest
        if not isinstance(manifest, dict):
            raise DefectSupportIssueError(f"{key}: Lean manifest is unavailable")
        raw_obligations = raw_decision.get("lean_obligations")
        if not isinstance(raw_obligations, dict):
            raise DefectSupportIssueError(f"{key}: lean_obligations must be keyed by ref")
        obligations: list[dict[str, str]] = []
        for atom in manifest.get("atoms", []):
            if not isinstance(atom, dict):
                raise DefectSupportIssueError(f"{key}: malformed Lean manifest atom")
            ref = str(atom.get("ref") or "").strip()
            annotation = raw_obligations.get(ref)
            if not isinstance(annotation, dict):
                raise DefectSupportIssueError(f"{key}: missing obligation annotation {ref}")
            obligations.append(
                {
                    "signature_ref": ref,
                    "role": str(atom.get("role") or "").strip(),
                    "signature_atom_sha256": dashboard.signature_manifest_atom_digest(atom),
                    "defect_relevance": str(
                        annotation.get("defect_relevance") or ""
                    ).strip(),
                    "semantic_explanation": str(
                        annotation.get("semantic_explanation") or ""
                    ).strip(),
                }
            )
        judgment = {
            "source_item": source_key,
            "source_statement_sha256": dashboard.statement_digest(
                str(source_item.get("statement") or "")
            ),
            "defect_id": defect_id,
            "source_defect": dashboard.source_proof_defect_snapshot(defect),
            "source_defect_sha256": dashboard.source_proof_defect_digest(defect),
            "support_declaration": row.name,
            "lean_statement": row.lean_statement,
            "lean_statement_sha256": dashboard.statement_digest(row.lean_statement),
            "lean_signature_sha256": str(manifest.get("sha256") or "").strip(),
            "judgment": str(raw_decision.get("judgment") or "").strip(),
            "reason": str(raw_decision.get("reason") or "").strip(),
            "lean_obligations": obligations,
            "obligation_alignment": raw_decision.get("obligation_alignment"),
        }
        error = dashboard.defect_support_judgment_error(
            judgment,
            source_key=source_key,
            source_item=source_item,
            defect=defect,
            support_declaration=row.name,
            row_item=row,
        )
        if error:
            raise DefectSupportIssueError(f"{key}: {error}")
        issued[str(key)] = judgment

    validator = str(decisions.get("validator") or "").strip()
    validator_type = str(decisions.get("validator_type") or "agent").strip()
    if not validator or not validator_type:
        raise DefectSupportIssueError("validator and validator_type are required")
    return {
        "schema": 1,
        "paper": folder.name,
        "prompt_version": "defect-support-v1-exact-source-defect-to-lean-semantic",
        "audit_kind": "source_defect_to_lean_agent",
        "source_grounded": True,
        "validator": validator,
        "validator_type": validator_type,
        "validated_at": datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
            "+00:00", "Z"
        ),
        "items": issued,
    }


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
        target = folder / "audit" / "defect_support_match_llm.json"
        target.write_text(rendered, encoding="utf-8")
        print(target.relative_to(ROOT))
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
