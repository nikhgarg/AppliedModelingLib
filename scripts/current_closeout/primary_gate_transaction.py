"""Bind the closed current primary gate to one exact evidence transaction."""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path

from scripts import source_manifest_validation as source_validation
from scripts.current_closeout.lean_review_graph import graph_context_input_sha256
from scripts.current_closeout.realization import (
    graph_native_realization_receipts_from_inventory,
)
from scripts.current_closeout.review_surface import (
    builder_issued_v11_lean_review_surface,
)
from scripts.current_closeout.primary_gate import (
    CurrentV11PrimaryGateResult,
    ReviewRoutePartition,
    evaluate_current_v11_primary_gate,
)
from scripts.current_closeout.semantic_review import (
    current_v11_semantic_review_result,
)
from scripts.evidence_run_context import (
    EvidenceRunContextIssuerBinding,
    Finding,
    V11EvidenceRunContext,
    run_scoped_cached_value,
    run_scoped_validation_findings,
)
from scripts.lean_axiom_closure import APPROVED_LEAN_AXIOMS

_PRIMARY_ACCEPTANCE_ISSUER = object()


def current_source_spec_correspondence_inventory_findings(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
    require_source_bytes: bool = True,
) -> list[Finding]:
    """Bind the shared source inventory to this transaction's retained graph.

    Historical correspondence worksheets and transition selectors do not own
    a selected current graph. Source scope, aliases, atom quotes, and contract
    shape retain their shared checks; Lean supplies realization identities.
    """

    if (
        not isinstance(context, V11EvidenceRunContext)
        or not context.issued_by_builder
        or context.folder != folder.resolve()
        or folder.resolve().parent != repository_root.resolve() / "papers"
    ):
        return [Finding(
            "ERROR", folder.name, str(folder / "status.json"),
            "current source correspondence requires its exact builder-issued transaction",
        )]

    def evaluate() -> list[Finding]:
        findings, payload, selected, source_current = (
            source_validation.source_spec_correspondence_inventory_inputs(
                folder,
                context.status,
                require_source_bytes=require_source_bytes,
                context=context,
                graph_native_selected=True,
                automatic_requirement=(True, "selected current graph realization requirement"),
            )
        )
        if payload is None:
            return findings
        map_path = source_validation.transaction_sidecar(
            folder, "paper_statement_map.json", context
        )

        def add(message: str) -> None:
            findings.append(Finding(
                source_validation.finding_severity(context.status),
                folder.name,
                source_validation.rel(map_path),
                message,
            ))

        source_path, source_digest = source_validation.semantic_review_source_identity(payload)
        for key, item in selected:
            atoms = item.get(source_validation.SOURCE_CLAIM_ATOMS_KEY)
            for error in source_validation.source_claim_atoms_validation_errors(
                atoms, require_source_quote=True
            ):
                add(f"items.{key}: {error}")
            if source_current:
                for error in source_validation._source_claim_atoms_current_quote_binding_errors(
                    folder, atoms,
                    source_artifact_path=source_path,
                    source_artifact_sha256=source_digest,
                    alternate_source_artifact_path=payload.get("source_artifact_path"),
                    alternate_source_artifact_sha256=payload.get("source_artifact_sha256"),
                ):
                    add(f"items.{key}: {error}")

        semantic = current_v11_semantic_review_result(
            repository_root, folder, context=context
        )
        if not semantic.semantic_review_current:
            detail = semantic.selection_error
            if not detail and semantic.findings:
                detail = semantic.findings[0].message
            add("current v11 semantic review is incomplete: " + (
                detail or "v11 direct semantic-review evidence is incomplete"
            ))
            return findings
        try:
            surface = builder_issued_v11_lean_review_surface(folder, context)
        except ValueError as exc:
            add("current v11 realization graph is unavailable: " + str(exc))
            return findings
        if surface is None:
            add("current v11 realization graph is unavailable")
            return findings
        exact_items = context.statement_map.get("items")
        supplied_items = payload.get("items")
        if not isinstance(exact_items, Mapping) or not isinstance(supplied_items, Mapping):
            add("current v11 statement map has no item ledger")
            return findings
        for key, item in selected:
            if exact_items.get(key) != supplied_items.get(key) or exact_items.get(key) != item:
                add(f"{key}: source item is not bound to this evidence transaction")
                return findings
        receipts, errors = graph_native_realization_receipts_from_inventory(
            source_map=payload,
            inventory=surface.declaration_inventory,
            context_input_sha256=graph_context_input_sha256(
                context, repository_root=repository_root
            ),
            expected_paper_declarations=surface.paper_semantic_targets,
            expected_library_declarations=surface.library_semantic_targets,
        )
        for error in errors:
            add(error)
        if not errors:
            missing = sorted({key for key, _item in selected} - set(receipts))
            if missing:
                add("current v11 graph selected a different realization surface: "
                    + ", ".join(missing[:4]))
        return findings

    return run_scoped_validation_findings(
        context, folder=folder, status=context.status,
        require_source_bytes=require_source_bytes,
        validator="source_spec_correspondence_inventory_findings",
        compute=evaluate,
    )


def current_route_schema_preflight_findings(
    repository_root: Path,
    folder: Path,
    *,
    context: object,
) -> list[Finding]:
    """Check all frozen route/configuration inputs before build or final review.

    This is a non-accepting conjunction over the retained current graph and
    source-only validators. The later primary/evidence gates still own proof,
    axiom, source-byte, semantic, and terminal acceptance.
    """

    root, folder = repository_root.resolve(), folder.resolve()
    if (
        not isinstance(context, V11EvidenceRunContext)
        or not context.issued_by_builder
        or context.folder != folder
        or folder.parent != root / "papers"
    ):
        return [Finding(
            "ERROR", folder.name, str(folder / "status.json"),
            f"`{folder.name}` route-schema preflight requires its exact "
            "builder-issued current transaction",
        )]
    raw = current_source_spec_correspondence_inventory_findings(
        root, folder, context=context, require_source_bytes=False
    )
    raw.extend(source_validation.repaired_source_defect_route_preflight_findings(
        folder, context.status, context=context
    ))
    raw.extend(source_validation.source_proof_fidelity_findings(
        folder, context.status, context.status_payload,
        require_source_bytes=False, context=context,
    ))
    findings: list[Finding] = []
    for finding in raw:
        path = Path(finding.path)
        findings.append(Finding(
            finding.severity, folder.name,
            str(path if path.is_absolute() else root / path),
            f"`{folder.name}` route-schema preflight: {finding.message}",
        ))
    primary = current_v11_primary_gate_result(root, folder, context=context)
    findings.extend(Finding(
        "ERROR", folder.name, str(folder / "status.json"),
        f"`{folder.name}` frozen closeout configuration preflight: {message}",
    ) for message in primary.configuration_errors + primary.structure_errors)
    return list(dict.fromkeys(findings))


class AcceptedCurrentV11PrimaryGate:
    """Nominal proof of one exact accepted primary-gate verdict."""

    __slots__ = ("context", "result", "surface")

    def __init__(
        self,
        issuer: object,
        *,
        context: V11EvidenceRunContext,
        result: CurrentV11PrimaryGateResult,
        surface: object,
    ) -> None:
        if issuer is not _PRIMARY_ACCEPTANCE_ISSUER:
            raise TypeError(
                "current v11 primary acceptance is issued only by its gate"
            )
        self.context = context
        self.result = result
        self.surface = surface


def _unavailable_result(message: str) -> CurrentV11PrimaryGateResult:
    return CurrentV11PrimaryGateResult(
        declarations={},
        partition=ReviewRoutePartition((), (), ()),
        semantic_errors=(message,),
    )


def current_v11_primary_gate_result(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
) -> CurrentV11PrimaryGateResult:
    """Return one cached, parser-free gate for the issued v11 transaction."""

    root = repository_root.resolve()
    paper = folder.resolve()
    if (
        not isinstance(context, V11EvidenceRunContext)
        or not context.issued_by_builder
        or context.folder != paper
        or not context.v11_lean_claim_graph_selected
        or paper.parent != root / "papers"
    ):
        return _unavailable_result(
            "current v11 primary gate requires its exact builder-issued transaction"
        )

    def evaluate() -> CurrentV11PrimaryGateResult:
        semantic = current_v11_semantic_review_result(
            root,
            paper,
            context=context,
        )
        if semantic.surface is None:
            detail = semantic.selection_error
            if not detail and semantic.findings:
                detail = semantic.findings[0].message
            return _unavailable_result(
                f"`{paper.name}` current v11 semantic surface is unavailable: "
                + (detail or "semantic review did not produce a Lean graph")
            )
        context.retain_v11_review_surface(semantic.surface)
        status_payload = context.status_payload
        source_map = context.statement_map
        if not isinstance(status_payload, dict):
            return _unavailable_result(
                f"`{paper.name}` current v11 transaction has no status payload"
            )
        if not isinstance(source_map, dict):
            return _unavailable_result(
                f"`{paper.name}` current v11 transaction has no statement map"
            )
        semantic_error = semantic.selection_error
        if not semantic_error and semantic.findings:
            semantic_error = semantic.findings[0].message
        return evaluate_current_v11_primary_gate(
            repository_root=root,
            paper_id=paper.name,
            folder=paper,
            status_payload=status_payload,
            source_map=source_map,
            surface=semantic.surface,
            semantic_review_current=semantic.semantic_review_current,
            semantic_review_error=semantic_error,
            approved_axioms=APPROVED_LEAN_AXIOMS,
        )

    result = run_scoped_cached_value(
        context,
        folder=paper,
        key=("verdict", "current_v11_primary_gate", root.as_posix()),
        compute=evaluate,
    )
    if not isinstance(result, CurrentV11PrimaryGateResult):
        raise TypeError("current v11 primary-gate cache contains a foreign value")
    return result


def evaluate_and_accept_current_v11_primary_gate(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
) -> tuple[CurrentV11PrimaryGateResult, AcceptedCurrentV11PrimaryGate | None]:
    """Evaluate once and bind acceptance to the exact verdict and Lean surface."""

    result = current_v11_primary_gate_result(
        repository_root,
        folder,
        context=context,
    )
    if not result.accepted:
        return result, None
    surface = context.retained_v11_review_surface()
    binding = context._issuer_token
    if (
        surface is None
        or not isinstance(binding, EvidenceRunContextIssuerBinding)
        or binding.context is not context
    ):
        return _unavailable_result(
            "current v11 primary acceptance has no exact retained Lean surface"
        ), None
    existing = accepted_current_v11_primary_gate(context)
    if existing is not None and existing.result is result:
        return result, existing
    accepted = AcceptedCurrentV11PrimaryGate(
        _PRIMARY_ACCEPTANCE_ISSUER,
        context=context,
        result=result,
        surface=surface,
    )
    binding.current_v11_primary_gate_acceptance = accepted
    return result, accepted


def accepted_current_v11_primary_gate(
    context: object,
) -> AcceptedCurrentV11PrimaryGate | None:
    """Return only the factory-issued acceptance bound to this exact context."""

    if not isinstance(context, V11EvidenceRunContext) or not context.issued_by_builder:
        return None
    binding = context._issuer_token
    if not isinstance(binding, EvidenceRunContextIssuerBinding):
        return None
    accepted = binding.current_v11_primary_gate_acceptance
    if not isinstance(accepted, AcceptedCurrentV11PrimaryGate):
        return None
    if (
        accepted.context is not context
        or accepted.surface is not context.retained_v11_review_surface()
        or not accepted.result.accepted
    ):
        return None
    return accepted
