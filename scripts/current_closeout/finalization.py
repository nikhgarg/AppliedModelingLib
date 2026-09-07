"""Publish one current closeout inside its exact strict transaction.

The worker process and its serialized trace are operational infrastructure.
They cannot authorize publication.  This module consumes only the runtime-only
``CurrentCloseoutPass`` issued after the primary, evidence, conclusion,
holistic, focused-build, and final-mutation gates all passed in one process.
"""

from __future__ import annotations

from collections.abc import Mapping
from typing import Any

from scripts.closeout_plan_receipt import load_validated_closeout_plan_receipt
from scripts.closeout_status_projection import (
    CloseoutStatusProjectionError,
    refresh_derived_paper_status_metadata,
)
from scripts.current_closeout.input_mutation import current_evidence_input_mutations
from scripts.current_closeout.pass_capability import (
    CurrentCloseoutPassError,
    bind_current_closeout_pass_authority,
    current_closeout_pass_authority,
    validate_current_closeout_pass,
)
from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_EXECUTION_STAGES,
    current_closeout_execution_projection,
)
from scripts.final_closure_receipt import (
    FinalClosureReceiptError,
    record_focused_build_receipt,
)
from scripts.formalization_engine_identity import current_registered_engine_projection
from scripts.lean_import_closure import lean_import_closure_receipt_payload
from scripts.obligation_closeout_materialization import (
    materialize_passed_strict_closeout_to_obligation_bundle,
)
from scripts.obligation_closure_credential import (
    publish_current_obligation_bundle_as_accepted_graph,
)
from scripts.strict_closeout_authority import (
    StrictCloseoutAuthorityError,
    issue_current_strict_closeout_authority,
    validate_strict_closeout_authority,
)


class CloseoutFinalizationError(ValueError):
    """A current strict transaction cannot be published safely."""


def _same_engine(left: Mapping[str, object], right: Mapping[str, object]) -> bool:
    keys = (
        "engine_tree_sha256",
        "review_semantic_class_sha256",
        "revision_sequence",
        "registration_kind",
        "engine_file_count",
    )
    return all(left.get(key) == right.get(key) for key in keys)


def finalize_current_closeout(current_pass: object) -> dict[str, Any]:
    """Materialize and publish the exact pass before it leaves this process."""

    try:
        accepted = validate_current_closeout_pass(current_pass)
        root = accepted.repository_root
        paper = accepted.paper
        issued_plan = accepted.plan_receipt()
        deep_paper_prose = issued_plan.get("deep_paper_prose")
        if not isinstance(deep_paper_prose, bool):
            raise CloseoutFinalizationError(
                "the current closeout pass has no exact prose-audit mode"
            )
        plan_receipt, plan_error = load_validated_closeout_plan_receipt(
            root,
            paper=paper,
            deep_paper_prose=deep_paper_prose,
            expected_plan_identity=accepted.plan_identity,
        )
        if plan_receipt is None:
            raise CloseoutFinalizationError(
                "the strict closeout plan changed before publication: " + plan_error
            )
        if plan_receipt != issued_plan:
            raise CloseoutFinalizationError(
                "the strict closeout plan bytes changed before publication"
            )
        engine, engine_error = current_registered_engine_projection(root)
        if engine is None:
            raise CloseoutFinalizationError(
                engine_error or "registered engine projection is unavailable"
            )
        if not _same_engine(engine, accepted.engine_registration()):
            raise CloseoutFinalizationError(
                "registered engine changed before current closeout publication"
            )
        if current_evidence_input_mutations(accepted.evidence_context):
            raise CloseoutFinalizationError(
                "current closeout inputs changed after the terminal mutation gate"
            )
        build_input_provider = accepted.build_input_provider
        finalize_unchanged = getattr(build_input_provider, "finalize_unchanged", None)
        if not callable(finalize_unchanged) or not finalize_unchanged():
            raise CloseoutFinalizationError(
                "Lean build/import inputs changed before publication"
            )

        authority = validate_strict_closeout_authority(
            issue_current_strict_closeout_authority(accepted)
        )
        bind_current_closeout_pass_authority(accepted, authority)
        raw_closure = accepted.lean_closure_projection().get("lean_import_closure")
        if not isinstance(raw_closure, Mapping):
            raise CloseoutFinalizationError(
                "the current closeout pass has no Lean import-closure payload"
            )
        closure_receipt = lean_import_closure_receipt_payload(paper, raw_closure)
        build_receipt = record_focused_build_receipt(
            root,
            paper,
            run_build=False,
            persist_saved_closure=False,
            authenticated_lean_import_closure_receipt=closure_receipt,
        )
        obligation_migration = materialize_passed_strict_closeout_to_obligation_bundle(
            root,
            paper,
            authority=authority,
            build_input_provider=build_input_provider,
            finalize_build_input_provider=False,
            authenticated_lean_import_closure_receipt=closure_receipt,
            authenticated_v11_lean_review_graph=accepted.lean_review_graph(),
            authenticated_v11_lean_review_graph_sha256=(
                accepted.lean_review_graph_sha256
            ),
        )
        if not finalize_unchanged():
            raise CloseoutFinalizationError(
                "Lean build/import inputs changed during graph materialization"
            )
        if current_closeout_pass_authority(accepted) is not authority:
            raise CloseoutFinalizationError(
                "current closeout authority changed during graph materialization"
            )
        final_receipt = publish_current_obligation_bundle_as_accepted_graph(
            root,
            paper,
            current_closeout_pass=accepted,
        )
        derived_status_metadata_refreshed = refresh_derived_paper_status_metadata(
            root, paper
        )
    except (
        CloseoutFinalizationError,
        CurrentCloseoutPassError,
        FinalClosureReceiptError,
        CloseoutStatusProjectionError,
        StrictCloseoutAuthorityError,
        OSError,
        RuntimeError,
        TypeError,
        ValueError,
    ) as exc:
        if isinstance(exc, CloseoutFinalizationError):
            raise
        raise CloseoutFinalizationError(
            f"current closeout publication failed: {exc}"
        ) from exc

    return {
        "canonical_receipt": final_receipt.relative_to(root).as_posix(),
        "focused_build_receipt": build_receipt.relative_to(root).as_posix(),
        "evidence_lane": "obligation-graph",
        "derived_status_metadata_refreshed": derived_status_metadata_refreshed,
        "obligation_evidence": obligation_migration.projection(),
        "closeout_stage_dag": current_closeout_execution_projection(
            STRICT_CLOSEOUT_EXECUTION_STAGES
        ),
        "runtime_pass_bound_stage_count": len(STRICT_CLOSEOUT_EXECUTION_STAGES),
    }


__all__ = [
    "CloseoutFinalizationError",
    "finalize_current_closeout",
]
