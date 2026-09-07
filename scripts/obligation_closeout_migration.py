#!/usr/bin/env python3
"""Migrate an authenticated historical receipt into the obligation store.

This legacy-only command authenticates a schema-2/3/4 canonical receipt and
delegates deterministic bundle assembly to the protocol-neutral materializer.
It does not define a second projection or acceptance route.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_formalization_engine_revision import (
    EngineRevisionError,
    validate_runtime_engine_registration,
)
from scripts.final_closure_receipt import (
    FinalClosureReceiptError,
    validate_final_closure_receipt,
)
from scripts.obligation_closeout_materialization import (
    ObligationCloseoutMaterializationError,
    ObligationCloseoutMaterializationResult,
    ProgressCallback,
    materialize_authenticated_closeout_to_obligation_bundle,
)
from scripts.obligation_closeout_state import ObligationCloseoutStateError
from scripts.obligation_evidence_issuance import (
    LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256,
)
from scripts.obligation_evidence_projection import ObligationEvidenceProjectionError
from scripts.obligation_evidence_store import ObligationEvidenceStoreError
from scripts.obligation_paper_index import PaperObligationIndexError
from scripts.obligation_preflight import ObligationPreflightError


class ObligationCloseoutMigrationError(ValueError):
    """A historical accepted closeout cannot be migrated safely."""


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    try:
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError as exc:
        raise ObligationCloseoutMigrationError(
            f"could not hash historical receipt {path}: {exc}"
        ) from exc
    return digest.hexdigest()


def _progress(callback: ProgressCallback | None, stage: str, **details: Any) -> None:
    if callback is not None:
        callback({"stage": stage, **details})


def migrate_accepted_closeout_to_obligation_bundle(
    root: Path,
    paper: str,
    *,
    progress_callback: ProgressCallback | None = None,
) -> ObligationCloseoutMaterializationResult:
    """Migrate one historical schema-2/3/4 receipt through the shared core."""

    root = root.resolve()
    receipt_path = root / "papers" / paper / "FINAL_CLOSURE_RECEIPT.md"
    _progress(progress_callback, "authenticate_legacy_closeout")
    accepted = validate_final_closure_receipt(root, paper)
    schema = accepted.payload.get("schema")
    if schema not in {2, 3, 4}:
        raise ObligationCloseoutMigrationError(
            "legacy migration requires a schema-2, schema-3, or schema-4 receipt"
        )
    receipt_sha256 = _sha256_file(receipt_path)
    engine = validate_runtime_engine_registration(root)
    result = materialize_authenticated_closeout_to_obligation_bundle(
        root,
        paper,
        operation="authenticated_legacy_closeout_migration",
        issuance_authority_sha256=receipt_sha256,
        issuance_assurance_contract_sha256=(
            LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
        ),
        expected_engine_tree_sha256=engine.engine_tree_sha256,
        watched_authority_paths=(receipt_path,),
        progress_callback=progress_callback,
    )
    validate_final_closure_receipt(root, paper)
    if _sha256_file(receipt_path) != receipt_sha256:
        raise ObligationCloseoutMigrationError(
            "legacy canonical receipt changed during obligation migration"
        )
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    args = parser.parse_args(argv)

    def show_progress(event: Mapping[str, Any]) -> None:
        print(json.dumps(dict(event), sort_keys=True), flush=True)

    try:
        result = migrate_accepted_closeout_to_obligation_bundle(
            ROOT,
            args.paper,
            progress_callback=show_progress,
        )
    except (
        EngineRevisionError,
        FinalClosureReceiptError,
        ObligationCloseoutMaterializationError,
        ObligationCloseoutMigrationError,
        ObligationCloseoutStateError,
        ObligationEvidenceProjectionError,
        ObligationEvidenceStoreError,
        PaperObligationIndexError,
        ObligationPreflightError,
        OSError,
        RuntimeError,
        ValueError,
    ) as exc:
        print(f"obligation-closeout migration failed: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result.projection(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI wrapper.
    raise SystemExit(main())
