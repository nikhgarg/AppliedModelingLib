#!/usr/bin/env python3
"""Seed paper_coverage_llm.json from an explicit source-statement inventory.

This helper is intentionally conservative.  It only marks a source item
`covered` when its canonical key or alias exactly matches a current dashboard
row.  Everything else is left `uncertain` so a separate LLM/source-reading pass
can decide whether it is covered, partially covered, missing, or out of scope.
Do not use this exact-key scaffold to justify omitting source-labelled named
definitions, propositions, theorems/corollaries, lemmas, or numbered
formula/algorithm/assumption targets for compactness.  Figures, captions,
numerical examples, simulations, and ordinary prose belong only to explicit
deep-paper coverage mode.

This command deliberately never asks Lean to rebuild a dashboard cache.  The
default exact-key scaffold reads an already-present local row cache, checks the
current PaperInterface selection syntactically, and stops visibly if that cache
is absent or stale.  Use ``--all-uncertain-bootstrap`` when the cache has not
yet been refreshed: it records every source item as uncertain without looking
at Lean row names.  Both outputs are non-evidence scaffolds and fail closed in
the closeout checks.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.review_dashboard import (  # noqa: E402
    DEFAULT_LLM_PAPER_COVERAGE_FILE,
    PAPER_INTERFACE_CACHE_SCHEMA,
    REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
    ReviewItem,
    cached_rows_match_current_extraction_surface,
    paper_interface_cache_file,
    paper_coverage_inventory,
    paper_coverage_inventory_digest,
    paper_statement_map_payload,
    review_source_file,
    review_surface_digest,
    statement_digest,
)
from scripts.source_coverage_scope import (  # noqa: E402
    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    source_item_coverage_sha256,
    source_item_effective_route_policy,
)


class CacheOnlySeedError(RuntimeError):
    """Raised when a non-elaborating exact-key seed cannot use a row cache."""


def _cached_review_items_for_exact_key_seed(folder: Path) -> list[ReviewItem]:
    """Load a syntactically current row cache without starting Lean.

    The normal dashboard cache loader authenticates the full imported Lean
    dependency closure.  That is essential for an audit, but using it here
    would turn a seed command into an expensive manifest extraction on a cache
    miss.  This helper therefore verifies only the current PaperInterface
    source and review-surface selection.  The resulting scaffold remains
    explicitly non-evidence, so it cannot receive closeout credit before a
    later strict dashboard refresh and semantic source-to-row review.
    """

    cache_path = paper_interface_cache_file(folder)
    try:
        payload = json.loads(cache_path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise CacheOnlySeedError(
            f"no local dashboard row cache at {cache_path.relative_to(ROOT)}"
        ) from exc
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise CacheOnlySeedError(
            f"could not read local dashboard row cache at {cache_path.relative_to(ROOT)}"
        ) from exc

    if not isinstance(payload, dict):
        raise CacheOnlySeedError("local dashboard row cache is not a JSON object")
    if payload.get("schema") != PAPER_INTERFACE_CACHE_SCHEMA:
        raise CacheOnlySeedError(
            "local dashboard row cache schema is stale; refresh it before exact-key seeding"
        )
    if payload.get("paper") != folder.name:
        raise CacheOnlySeedError("local dashboard row cache belongs to another paper")

    hashes = payload.get("hashes")
    if not isinstance(hashes, dict):
        raise CacheOnlySeedError("local dashboard row cache lacks its source hashes")
    try:
        source_file = review_source_file(folder)
        current_interface = source_file.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        raise CacheOnlySeedError("could not read the current PaperInterface source") from exc
    if hashes.get("review_source_file") != source_file.name:
        raise CacheOnlySeedError(
            "local dashboard row cache names a different review source file"
        )
    if hashes.get("interface_sha256") != statement_digest(current_interface):
        raise CacheOnlySeedError(
            "the PaperInterface source changed after the local dashboard cache was written"
        )

    raw_rows = payload.get("rows")
    if not isinstance(raw_rows, list):
        raise CacheOnlySeedError("local dashboard row cache lacks its rows")

    rows: list[ReviewItem] = []
    names: set[str] = set()
    for raw in raw_rows:
        if not isinstance(raw, dict):
            raise CacheOnlySeedError("local dashboard row cache contains a malformed row")
        name = str(raw.get("name") or "").strip()
        kind = str(raw.get("kind") or "").strip()
        lean_statement = str(raw.get("lean_statement") or "").strip()
        interface_source = str(raw.get("interface_source") or "").strip()
        signature = str(raw.get("lean_signature_sha256") or "").strip().lower()
        if not name or not kind or not lean_statement or not interface_source:
            raise CacheOnlySeedError(
                "local dashboard row cache contains an incomplete review row"
            )
        if not signature:
            raise CacheOnlySeedError(
                f"local dashboard row cache lacks an elaborated signature for `{name}`"
            )
        if name in names:
            raise CacheOnlySeedError(
                f"local dashboard row cache has duplicate review row name `{name}`"
            )
        names.add(name)
        rows.append(
            ReviewItem(
                name=name,
                kind=kind,
                lean_statement=lean_statement,
                paper_statement=str(raw.get("paper_statement") or ""),
                agent_statement=str(raw.get("agent_statement") or ""),
                full_name=str(raw.get("full_name") or ""),
                interface_source=interface_source,
                lean_signature_sha256=signature,
                source_status=str(raw.get("source_status") or ""),
                source_note=str(raw.get("source_note") or ""),
                is_assumption=bool(raw.get("is_assumption") is True),
                is_proposition_spec=bool(raw.get("is_proposition_spec") is True),
                proposition_spec_role=str(raw.get("proposition_spec_role") or ""),
                proposition_spec_proof=str(raw.get("proposition_spec_proof") or ""),
            )
        )

    if not rows:
        raise CacheOnlySeedError("local dashboard row cache contains no review rows")
    if not cached_rows_match_current_extraction_surface(folder, rows):
        raise CacheOnlySeedError(
            "the current PaperInterface/status selection no longer matches the local dashboard row cache"
        )
    return rows


def seed_payload(
    folder: Path,
    validator: str,
    validator_type: str,
    *,
    cached_rows: list[ReviewItem] | None,
) -> dict[str, Any]:
    _full_inventory, inventory, source_coverage_mode, _mode_error = (
        paper_coverage_inventory(folder)
    )
    statement_map = paper_statement_map_payload(folder)
    rows_by_name = {item.name: item for item in cached_rows or []}
    row_names = set(rows_by_name)
    exact_key_mode = cached_rows is not None
    audit_kind = "exact_key_scaffold" if exact_key_mode else "all_uncertain_bootstrap"
    coverage: dict[str, dict[str, Any]] = {}
    for key, item in sorted(inventory.items()):
        aliases = [str(alias) for alias in item.get("aliases", []) or [] if str(alias).strip()]
        candidates = [key, *aliases]
        matched = [candidate for candidate in candidates if candidate in row_names]
        route_policy = source_item_effective_route_policy(item)
        if not exact_key_mode:
            judgment = "uncertain"
            reason = (
                "All-uncertain bootstrap: no dashboard row cache was consulted. "
                "A source-reading reviewer must independently determine the "
                "source-to-row route; this scaffold gives no coverage credit."
            )
            review_rows = []
        elif route_policy["is_quarantined_source_defect"]:
            judgment = "uncertain"
            reason = (
                "Quarantined source defects never receive direct seeded coverage. "
                "A source-reading reviewer must select support_only routes and a "
                "separate defect_support_match_llm.json audit must bind each exact "
                "defect record to the elaborated Lean counterexample/refutation."
            )
            review_rows = []
        elif route_policy["is_support_only"]:
            judgment = "uncertain"
            reason = (
                "Support-only source items never receive direct seeded coverage. "
                "A source-reading reviewer must select the appropriate support "
                "route with its exact source scope."
            )
            review_rows = []
        elif matched:
            judgment = "covered"
            reason = "Canonical source key or alias exactly matches current dashboard row name."
            review_rows = sorted(set(matched))
        else:
            judgment = "uncertain"
            reason = (
                "No exact source-key/alias match to a current dashboard row. "
                "Requires independent source-to-row review; compactness alone "
                "is not a reason to scope out source-visible named material."
            )
            review_rows = []
        review_row_signature_sha256 = {
            row_name: str(rows_by_name[row_name].lean_signature_sha256 or "")
            .strip()
            .lower()
            for row_name in review_rows
        }
        coverage[key] = {
            "coverage": judgment,
            "review_rows": review_rows,
            "review_row_signature_sha256": review_row_signature_sha256,
            "reason": reason,
            "source_evidence": "",
            "dashboard_evidence": "",
            "statement_sha256": str(item.get("statement_sha256") or ""),
            "source_item_coverage_digest_schema": SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
            "source_item_coverage_sha256": source_item_coverage_sha256(
                item, source_coverage_mode
            ),
            "audit_kind": audit_kind,
            "source_grounded": False,
            "seed_scaffold": True,
        }
    return {
        "schema": 1,
        "paper": folder.name,
        "prompt_version": REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
        "audit_kind": audit_kind,
        "source_grounded": False,
        "seed_scaffold": True,
        "validator": validator,
        "validator_type": validator_type,
        "validated_at": datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
            "+00:00",
            "Z",
        ),
        "comment": (
            "Seeded by exact source-key/alias matches from a local cache only; "
            "non-exact items remain uncertain until an independent "
            "LLM/source-reading pass resolves them."
            if exact_key_mode
            else "All source items are deliberately uncertain because no dashboard "
            "row cache was consulted. An independent source-to-row audit is required."
        ),
        "cache_only_seed": exact_key_mode,
        "review_surface_cache_verification": (
            "PaperInterface source and row-selection surface matched the local "
            "cache; imported Lean dependencies were not authenticated by this seed."
            if exact_key_mode
            else "No dashboard row cache was read."
        ),
        "source_coverage_mode": source_coverage_mode,
        "source_artifact_path": str(
            statement_map.get("source_artifact_path") or ""
        ).strip(),
        "source_artifact_sha256": str(
            statement_map.get("source_artifact_sha256") or ""
        ).strip().lower(),
        "paper_statement_inventory_sha256": paper_coverage_inventory_digest(
            inventory,
            mode=source_coverage_mode,
            statement_map_payload=statement_map,
        ),
        "review_surface_sha256": (
            review_surface_digest(cached_rows) if cached_rows is not None else ""
        ),
        "items": coverage,
    }


def iter_papers(paper: str | None) -> list[Path]:
    if paper:
        folder = PAPERS_DIR / paper
        if not folder.is_dir():
            raise SystemExit(f"unknown paper folder: {paper}")
        return [folder]
    return sorted(
        folder
        for folder in PAPERS_DIR.iterdir()
        if folder.is_dir() and folder.name != "TEMPLATE" and (folder / "PaperInterface.lean").exists()
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", default="", help="Optional paper folder to seed.")
    parser.add_argument(
        "--write",
        action="store_true",
        help="Write paper_coverage_llm.json. Without this flag, only print a summary.",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Overwrite an existing paper_coverage_llm.json.",
    )
    parser.add_argument(
        "--all-uncertain-bootstrap",
        action="store_true",
        help=(
            "Do not read dashboard rows; seed every source item as uncertain. "
            "Use this before the first cache refresh. The result is a fail-closed "
            "non-evidence scaffold."
        ),
    )
    parser.add_argument(
        "--validator",
        default="seed_paper_coverage.py",
        help="Validator label to store in the seeded sidecar.",
    )
    parser.add_argument(
        "--validator-type",
        default="script",
        choices=("script", "agent", "model", "human"),
        help="Validator type to store in the seeded sidecar.",
    )
    args = parser.parse_args()

    failures = 0
    for folder in iter_papers(args.paper or None):
        _full_inventory, inventory, _mode, _mode_error = paper_coverage_inventory(folder)
        if not inventory:
            print(f"{folder.name}: no explicit/resolvable source inventory")
            continue
        if args.all_uncertain_bootstrap:
            cached_rows = None
        else:
            try:
                cached_rows = _cached_review_items_for_exact_key_seed(folder)
            except CacheOnlySeedError as exc:
                failures += 1
                print(
                    f"{folder.name}: cache-only exact-key seed unavailable: {exc}.",
                    file=sys.stderr,
                )
                print(
                    "  Refresh one paper's strict row cache with "
                    f"`env LEAN_NUM_THREADS=1 python3 scripts/review_dashboard.py "
                    f"--paper {folder.name} --refresh-cache`, then retry; or use "
                    "`--all-uncertain-bootstrap` to write a no-row fail-closed scaffold.",
                    file=sys.stderr,
                )
                continue
        payload = seed_payload(
            folder,
            args.validator,
            args.validator_type,
            cached_rows=cached_rows,
        )
        values = [item.get("coverage") for item in payload["items"].values()]
        covered = sum(1 for value in values if value == "covered")
        uncertain = sum(1 for value in values if value == "uncertain")
        mode = "exact_key_cache_only" if cached_rows is not None else "all_uncertain_bootstrap"
        print(
            f"{folder.name}: mode={mode} inventory={len(inventory)} "
            f"covered_by_exact_key={covered} uncertain={uncertain}"
        )
        if not args.write:
            continue
        out = folder / DEFAULT_LLM_PAPER_COVERAGE_FILE
        if out.exists() and not args.force:
            raise SystemExit(f"{out} exists; use --force to overwrite")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
