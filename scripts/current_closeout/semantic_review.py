"""One exact current-v11 semantic-review verdict over a frozen transaction.

This module joins three already explicit authorities without rediscovering any
of them: the typed source routes select asserted paper claims, Lean supplies
the complete semantic graph, and reviewer ledgers bind exact source bundles to
Lean semantic identities.  It does not parse Lean, infer claims from names, or
create judgments.  Historical source-record lanes remain outside this module.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType

from scripts.current_closeout.review_surface import (
    V11LeanReviewSurface,
    build_accepting_v11_review_surface,
    read_diagnostic_v11_review_surface,
)
from scripts.corrected_target_identity import (
    corrected_target_review_digest,
    source_requires_approved_corrected_target,
)
from scripts.direct_semantic_review_binding import (
    LEAN_TARGET_PROTOCOL,
    normalized_direct_screening_ledger,
    reusable_direct_source_spec_judgment,
)
from scripts.evidence_run_context import (
    Finding,
    V11EvidenceRunContext,
    run_scoped_cached_value,
)
from scripts.obligation_routes import (
    EvidenceRouteSet,
    ObligationRouteError,
    SemanticReviewTargetKind,
)
from scripts.portable_evidence_identity import portable_evidence_sha256
from scripts.semantic_prerequisite_projection import (
    LIBRARY_SEMANTIC_REVIEW_SCHEMA,
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_SCHEMA,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
    V11_DEFINITION_TARGET_PROTOCOL,
)
from scripts.semantic_review_binding import reusable_semantic_judgment
from scripts.source_review_input import (
    source_anchor_file_error,
    source_semantic_input_bundle,
    statement_digest,
)
from scripts.v11_screening_contract import validate_v11_screening_container

CLOSEOUT_STATUSES = frozenset(
    {
        "formalized",
        "formalized with caveat",
        "partially formalized",
        "conditional",
    }
)
ALL_SELECTED_SEMANTIC_REVIEW_MATERIAL_SCHEMA = 1
_SHA256_LENGTH = 64


@dataclass(frozen=True)
class CurrentV11SemanticReviewResult:
    """Complete verdict for the three semantic-review lanes only.

    This result grants no proof, axiom, mutation, holistic-review, build, or
    closeout authority.  Those remain mandatory inputs to the later closed
    current-v11 acceptance conjunction.
    """

    surface: V11LeanReviewSurface | None
    direct_findings: tuple[Finding, ...] = ()
    paper_prerequisite_findings: tuple[Finding, ...] = ()
    library_prerequisite_findings: tuple[Finding, ...] = ()
    selection_error: str = ""
    normalized_direct_items: Mapping[str, Mapping[str, object]] = (
        MappingProxyType({})
    )

    @property
    def findings(self) -> tuple[Finding, ...]:
        return (
            self.direct_findings
            + self.paper_prerequisite_findings
            + self.library_prerequisite_findings
        )

    @property
    def semantic_review_current(self) -> bool:
        return bool(
            self.surface is not None
            and not self.selection_error
            and not self.findings
        )


def _sha256(value: object, *, field: str, allow_empty: bool = False) -> str:
    digest = str(value or "").strip().lower()
    if allow_empty and not digest:
        return ""
    if len(digest) != _SHA256_LENGTH or any(
        character not in "0123456789abcdef" for character in digest
    ):
        raise ValueError(f"all-selected semantic review has invalid {field}")
    return digest


def _positive_review_basis(
    judgment: object,
    corrected_target_review_sha256: object,
    *,
    field: str,
) -> tuple[str, str]:
    normalized = str(judgment or "").strip().lower()
    correction = _sha256(
        corrected_target_review_sha256,
        field=f"{field} corrected-target review",
        allow_empty=True,
    )
    if normalized == "matches" and not correction:
        return "source_match", ""
    if normalized == "matches_approved_corrected_target" and correction:
        return "approved_corrected_target_match", correction
    raise ValueError(
        f"all-selected semantic review has invalid positive judgment basis for {field}"
    )


def _all_selected_semantic_review_material(
    *,
    semantic_targets: Mapping[str, Mapping[str, object]],
    direct_items: Mapping[str, Mapping[str, object]],
    paper_prerequisites: tuple[Mapping[str, object], ...],
    library_prerequisites: tuple[Mapping[str, object], ...],
) -> dict[str, object]:
    """Project the one canonical material shape from validated inputs."""

    if set(direct_items) != set(semantic_targets):
        raise ValueError(
            "all-selected semantic review direct-result inventory is incomplete"
        )

    direct_results: list[dict[str, str]] = []
    for declaration, target in sorted(semantic_targets.items()):
        row = direct_items.get(declaration)
        if not isinstance(row, Mapping) or not isinstance(target, Mapping):
            raise ValueError(
                "all-selected semantic review has a malformed direct result"
            )
        source_item = str(row.get("source_item") or "").strip()
        source_input_protocol = str(
            row.get("source_input_protocol") or ""
        ).strip()
        lean_target_protocol = str(row.get("lean_target_protocol") or "").strip()
        if not source_item or not source_input_protocol or not lean_target_protocol:
            raise ValueError(
                "all-selected semantic review direct result lacks its source or target route"
            )
        target_protocol = str(
            target.get("lean_target_protocol") or lean_target_protocol
        ).strip()
        target_identities = {
            "lean_expanded_statement_sha256": target.get("display_sha256"),
        }
        if target_protocol != lean_target_protocol or any(
            _sha256(target_value, field=f"direct result {source_item} {field}")
            != _sha256(row.get(field), field=f"direct result {source_item} {field}")
            for field, target_value in target_identities.items()
        ):
            raise ValueError(
                "all-selected semantic review direct result disagrees with its "
                "validated Lean target"
            )
        basis, correction = _positive_review_basis(
            row.get("judgment"),
            row.get("corrected_target_review_sha256"),
            field=f"direct result {source_item}",
        )
        direct_results.append(
            {
                "source_item": source_item,
                "source_input_protocol": source_input_protocol,
                "source_input_bundle_sha256": _sha256(
                    row.get("source_input_bundle_sha256"),
                    field=f"direct result {source_item} source bundle",
                ),
                "paper_statement_sha256": _sha256(
                    row.get("paper_statement_sha256"),
                    field=f"direct result {source_item} paper statement",
                ),
                "lean_target_protocol": lean_target_protocol,
                "lean_expanded_statement_sha256": _sha256(
                    row.get("lean_expanded_statement_sha256"),
                    field=f"direct result {source_item} Lean target",
                ),
                "review_basis": basis,
                "corrected_target_review_sha256": correction,
            }
        )

    def prerequisite_rows(
        rows: tuple[Mapping[str, object], ...],
        *,
        role: str,
        target_protocol: str,
        target_field: str,
    ) -> list[dict[str, str]]:
        projected: list[dict[str, str]] = []
        for row in rows:
            source_item = str(row.get("source_item") or "").strip()
            if row.get("semantic_current") is not True or not source_item:
                raise ValueError(
                    f"all-selected semantic review has a noncurrent {role} prerequisite"
                )
            basis, correction = _positive_review_basis(
                row.get("semantic_judgment"),
                row.get("corrected_target_review_sha256"),
                field=f"{role} prerequisite {source_item}",
            )
            projected.append(
                {
                    "source_item": source_item,
                    "source_input_bundle_sha256": _sha256(
                        row.get("source_input_bundle_sha256"),
                        field=f"{role} prerequisite {source_item} source bundle",
                    ),
                    "source_anchor_bundle_sha256": _sha256(
                        row.get("source_anchor_bundle_sha256"),
                        field=f"{role} prerequisite {source_item} source anchors",
                    ),
                    "semantic_target_protocol": target_protocol,
                    "semantic_target_sha256": _sha256(
                        row.get(target_field),
                        field=f"{role} prerequisite {source_item} target",
                    ),
                    "elaborated_signature_sha256": _sha256(
                        row.get("elaborated_signature_sha256"),
                        field=f"{role} prerequisite {source_item} Lean signature",
                    ),
                    "review_basis": basis,
                    "corrected_target_review_sha256": correction,
                }
            )
        return sorted(projected, key=portable_evidence_sha256)

    return {
        "schema": ALL_SELECTED_SEMANTIC_REVIEW_MATERIAL_SCHEMA,
        "direct_results": sorted(direct_results, key=portable_evidence_sha256),
        "paper_prerequisites": prerequisite_rows(
            paper_prerequisites,
            role="paper",
            target_protocol=PAPER_PREREQUISITE_TARGET_PROTOCOL,
            target_field="paper_semantic_target_sha256",
        ),
        "library_prerequisites": prerequisite_rows(
            library_prerequisites,
            role="library",
            target_protocol=LIBRARY_SEMANTIC_TARGET_PROTOCOL,
            target_field="library_semantic_target_sha256",
        ),
    }


def all_selected_semantic_review_material(
    result: CurrentV11SemanticReviewResult,
) -> dict[str, object]:
    """Project current semantic identities without reviewer or renderer prose.

    The current-v11 evaluator has already checked every direct result and every
    selected prerequisite against one frozen source/Lean transaction.  This
    function selects only the material identities used by those checks; it does
    not read a ledger, inspect Lean, or create a verdict.
    """

    if not result.semantic_review_current or result.surface is None:
        raise ValueError("all-selected semantic review is not current")
    return _all_selected_semantic_review_material(
        semantic_targets=result.surface.semantic_targets,
        direct_items=result.normalized_direct_items,
        paper_prerequisites=result.surface.paper_prerequisites,
        library_prerequisites=result.surface.library_prerequisites,
    )


def all_selected_semantic_review_material_sha256(
    result: CurrentV11SemanticReviewResult,
) -> str:
    """Hash the exact all-selected current semantic-review material."""

    return portable_evidence_sha256(all_selected_semantic_review_material(result))


def _current_source_review_identity(
    repository_root: Path,
    folder: Path,
    source_record: Mapping[str, object],
    *,
    context: V11EvidenceRunContext,
) -> dict[str, str]:
    source_error = source_anchor_file_error(
        folder,
        source_record,
        repository_root=repository_root,
        file_bytes_override=context.file_bytes_override(),
    )
    if source_error:
        raise ValueError("exact source bundle is unavailable: " + source_error)
    source_text, source_digest, source_error = source_semantic_input_bundle(
        source_record,
        require_context_roles=True,
    )
    if source_error or not source_text:
        raise ValueError("exact source bundle is incomplete: " + source_error)
    _anchor_text, anchor_digest, source_error = source_semantic_input_bundle(
        source_record,
        require_context_roles=True,
        include_approved_contexts=False,
    )
    if source_error:
        raise ValueError("exact source-anchor bundle is incomplete: " + source_error)
    corrected_target = source_record.get("corrected_target")
    correction = (
        corrected_target_review_digest(corrected_target)
        if isinstance(corrected_target, Mapping)
        else ""
    )
    return {
        "source_input_bundle_sha256": _sha256(
            source_digest, field="current source bundle"
        ),
        "source_anchor_bundle_sha256": _sha256(
            anchor_digest, field="current source anchors"
        ),
        "paper_statement_sha256": _sha256(
            statement_digest(source_text), field="current paper statement"
        ),
        "corrected_target_review_sha256": correction,
    }


def _accepted_prerequisite_ledger_items(
    ledger: Mapping[str, object],
    *,
    paper: str,
    role: str,
) -> Mapping[str, Mapping[str, object]]:
    if role == "paper":
        expected_schema = PAPER_PREREQUISITE_SCHEMA
        expected_prompt = PAPER_PREREQUISITE_PROMPT_VERSION
        expected_protocol = PAPER_PREREQUISITE_TARGET_PROTOCOL
    else:
        expected_schema = LIBRARY_SEMANTIC_REVIEW_SCHEMA
        expected_prompt = REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION
        expected_protocol = LIBRARY_SEMANTIC_TARGET_PROTOCOL
    items = ledger.get("items")
    if (
        ledger.get("schema") != expected_schema
        or ledger.get("paper") != paper
        or str(ledger.get("prompt_version") or "").strip() != expected_prompt
        or str(ledger.get("target_protocol") or "").strip() != expected_protocol
        or not isinstance(items, Mapping)
    ):
        raise ValueError(f"current {role} prerequisite ledger is stale")
    if any(
        not isinstance(name, str) or not isinstance(row, Mapping)
        for name, row in items.items()
    ):
        raise ValueError(f"current {role} prerequisite ledger has a malformed row")
    return items


def accepted_graph_all_selected_semantic_review_material(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
) -> dict[str, object]:
    """Project the current all-selected material from an exact accepted graph.

    This is a document-only fallback for a missing operational Lean graph
    checkpoint.  It does not run Lean or create semantic authority.  The
    accepted-graph reader first requires the exact current Lean import/build
    closure with semantic recovery disabled and authenticates each candidate
    ledger row through its strict issuance.
    """

    root = repository_root.resolve()
    paper = folder.resolve()
    if (
        not isinstance(context, V11EvidenceRunContext)
        or not context.issued_by_builder
        or context.folder != paper
        or not context.v11_lean_claim_graph_selected
    ):
        raise ValueError(
            "accepted semantic review requires its exact issued v11 transaction"
        )
    if paper.parent != root / "papers":
        raise ValueError(
            "accepted semantic review requires the canonical repository root"
        )
    if context.status not in CLOSEOUT_STATUSES:
        raise ValueError("paper status does not select a closeout review lane")

    from scripts.obligation_closure_credential import (
        ObligationClosureCredentialError,
        authenticated_current_accepted_graph_semantic_review_inputs,
    )

    try:
        accepted = authenticated_current_accepted_graph_semantic_review_inputs(
            root, paper.name
        )
    except ObligationClosureCredentialError as exc:
        raise ValueError(
            "current accepted graph cannot supply document semantics: " + str(exc)
        ) from exc

    source_map = context.statement_map
    if not isinstance(source_map, Mapping) or source_map != accepted.source_map:
        raise ValueError(
            "accepted graph source map differs from the exact document transaction"
        )
    ledger_pairs = (
        (
            "v11_raw_source_spec_screening.json",
            accepted.direct_review_ledger,
        ),
        (
            "paper_semantic_prerequisites.json",
            accepted.paper_prerequisite_ledger,
        ),
        (
            "library_semantic_review.json",
            accepted.library_prerequisite_ledger,
        ),
    )
    for basename, accepted_ledger in ledger_pairs:
        current_ledger = context.json_payload(
            context.canonical_sidecar_path(basename)
        )
        if not isinstance(current_ledger, Mapping) or current_ledger != accepted_ledger:
            raise ValueError(
                f"accepted graph {basename} differs from the exact document transaction"
            )

    direct_validation = validate_v11_screening_container(
        accepted.direct_review_ledger,
        paper=paper.name,
    )
    if not direct_validation.current:
        raise ValueError("; ".join(direct_validation.errors))
    direct_items = accepted.direct_review_ledger.get("items")
    if not isinstance(direct_items, Mapping):
        raise ValueError("accepted graph direct-review ledger has no item map")
    paper_items = _accepted_prerequisite_ledger_items(
        accepted.paper_prerequisite_ledger,
        paper=paper.name,
        role="paper",
    )
    library_items = _accepted_prerequisite_ledger_items(
        accepted.library_prerequisite_ledger,
        paper=paper.name,
        role="library",
    )
    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
    except ObligationRouteError as exc:
        raise ValueError("accepted graph has invalid typed source routes") from exc
    source_items = source_map.get("items")
    if not isinstance(source_items, Mapping):
        raise ValueError("paper statement map has no item map")

    expected_specs = set(route_set.result_specifications())
    direct_targets = accepted.direct_target_identities_by_specification
    if set(direct_items) != expected_specs or set(direct_targets) != expected_specs:
        raise ValueError(
            "accepted graph direct-result inventory is incomplete"
        )
    semantic_targets: dict[str, Mapping[str, object]] = {}
    normalized_direct_items: dict[str, Mapping[str, object]] = {}
    source_identities: dict[str, dict[str, str]] = {}

    def source_identity(source_item: str) -> dict[str, str]:
        cached = source_identities.get(source_item)
        if cached is not None:
            return cached
        record = source_items.get(source_item)
        if not isinstance(record, Mapping):
            raise ValueError(
                f"accepted semantic review names unknown source item {source_item}"
            )
        current = _current_source_review_identity(
            root,
            paper,
            record,
            context=context,
        )
        source_identities[source_item] = current
        return current

    for route in route_set.result_routes():
        specification = route.spec_declaration
        row = direct_items.get(specification)
        target = direct_targets.get(specification)
        if not isinstance(row, Mapping) or not isinstance(target, Mapping):
            raise ValueError(
                f"accepted graph direct semantic material is incomplete: {specification}"
            )
        source_item = str(row.get("source_item") or "").strip()
        identity = source_identity(source_item)
        expected_protocol = (
            LEAN_TARGET_PROTOCOL
            if route.semantic_review_target_kind
            is SemanticReviewTargetKind.SPEC_PROPOSITION
            else V11_DEFINITION_TARGET_PROTOCOL
        )
        correction = identity["corrected_target_review_sha256"]
        source_record = source_items[source_item]
        assert isinstance(source_record, Mapping)
        corrected_target = source_record.get("corrected_target")
        current_direct_identity = {
            "source_input_bundle_sha256": identity[
                "source_input_bundle_sha256"
            ],
            "paper_statement_sha256": identity["paper_statement_sha256"],
            "lean_target_protocol": expected_protocol,
            "lean_expanded_statement_sha256": target[
                "reviewed_semantic_target_sha256"
            ],
            "coverage_status": str(
                source_record.get("coverage_status") or ""
            ).strip(),
            "corrected_target_sha256": (
                str(corrected_target.get("corrected_target_sha256") or "")
                .strip()
                .lower()
                if isinstance(corrected_target, Mapping)
                else ""
            ),
            "corrected_target_review_sha256": correction,
        }
        recorded_review_declaration = str(
            row.get("semantic_review_declaration") or specification
        ).strip()
        if (
            source_item != route.source_item_id
            or str(row.get("semantic_target_declaration") or "").strip()
            != specification
            or recorded_review_declaration != route.semantic_review_declaration
            or str(target.get("semantic_target_kind") or "").strip()
            != route.semantic_review_target_kind.value
            or reusable_direct_source_spec_judgment(
                row,
                current_direct_identity,
            )
            is None
        ):
            raise ValueError(
                f"{specification}: accepted direct-review identity is stale"
            )
        semantic_targets[specification] = {
            "display_sha256": target["reviewed_semantic_target_sha256"],
            "lean_target_protocol": expected_protocol,
        }
        normalized_direct_items[specification] = row

    expected_prerequisites = set(
        accepted.prerequisite_target_identities_by_declaration
    )
    if set(paper_items) & set(library_items) or (
        set(paper_items) | set(library_items)
    ) != expected_prerequisites:
        raise ValueError("accepted graph prerequisite inventory is incomplete")

    def prerequisite_rows(
        items: Mapping[str, Mapping[str, object]],
        *,
        role: str,
        declaration_field: str,
        protocol_field: str,
        target_field: str,
        expected_protocol: str,
    ) -> tuple[Mapping[str, object], ...]:
        projected: list[Mapping[str, object]] = []
        for declaration, row in sorted(items.items()):
            target = accepted.prerequisite_target_identities_by_declaration.get(
                declaration
            )
            if not isinstance(target, Mapping):
                raise ValueError(
                    f"accepted graph omits {role} prerequisite {declaration}"
                )
            source_item = str(row.get("source_item") or "").strip()
            identity = source_identity(source_item)
            source_record = source_items[source_item]
            assert isinstance(source_record, Mapping)
            expected_judgment = (
                "matches_approved_corrected_target"
                if source_requires_approved_corrected_target(source_record)
                else "matches"
            )
            current_prerequisite_identity = {
                "source_input_bundle_sha256": identity[
                    "source_input_bundle_sha256"
                ],
                "source_anchor_bundle_sha256": identity[
                    "source_anchor_bundle_sha256"
                ],
                "corrected_target_review_sha256": identity[
                    "corrected_target_review_sha256"
                ],
                "elaborated_signature_sha256": target[
                    "elaborated_signature_sha256"
                ],
                target_field: target["reviewed_semantic_target_sha256"],
            }
            reusable = reusable_semantic_judgment(
                row,
                current_prerequisite_identity,
                target_protocol_field=protocol_field,
                target_protocol=expected_protocol,
                prior_code_sha256_field=(
                    "paper_declaration_sha256"
                    if role == "paper"
                    else "library_definition_sha256"
                ),
                current_code_sha256_field=(
                    "paper_declaration_sha256"
                    if role == "paper"
                    else "current_named_library_definition_sha256"
                ),
                prior_target_sha256_field=target_field,
                current_target_sha256_field=target_field,
            )
            if (
                str(row.get(declaration_field) or "").strip() != declaration
                or str(row.get("judgment") or "").strip().lower()
                != expected_judgment
                or str(target.get("semantic_target_kind") or "").strip()
                != "semantic_prerequisite"
                or reusable is None
            ):
                raise ValueError(
                    f"{declaration}: accepted {role} prerequisite identity is stale"
                )
            projected.append(
                {
                    "source_item": source_item,
                    "source_input_bundle_sha256": identity[
                        "source_input_bundle_sha256"
                    ],
                    "source_anchor_bundle_sha256": identity[
                        "source_anchor_bundle_sha256"
                    ],
                    "corrected_target_review_sha256": identity[
                        "corrected_target_review_sha256"
                    ],
                    target_field: target["reviewed_semantic_target_sha256"],
                    "elaborated_signature_sha256": target[
                        "elaborated_signature_sha256"
                    ],
                    "semantic_judgment": row["judgment"],
                    "semantic_current": True,
                }
            )
        return tuple(projected)

    return _all_selected_semantic_review_material(
        semantic_targets=semantic_targets,
        direct_items=normalized_direct_items,
        paper_prerequisites=prerequisite_rows(
            paper_items,
            role="paper",
            declaration_field="paper_declaration",
            protocol_field="paper_semantic_target_protocol",
            target_field="paper_semantic_target_sha256",
            expected_protocol=PAPER_PREREQUISITE_TARGET_PROTOCOL,
        ),
        library_prerequisites=prerequisite_rows(
            library_items,
            role="library",
            declaration_field="library_declaration",
            protocol_field="library_semantic_target_protocol",
            target_field="library_semantic_target_sha256",
            expected_protocol=LIBRARY_SEMANTIC_TARGET_PROTOCOL,
        ),
    )


def accepted_graph_all_selected_semantic_review_material_sha256(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
) -> str:
    """Hash all-selected material recovered from exact accepted controls."""

    return portable_evidence_sha256(
        accepted_graph_all_selected_semantic_review_material(
            repository_root,
            folder,
            context=context,
        )
    )


def _relative(root: Path, path: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return str(path)


def _finding(
    root: Path,
    folder: Path,
    path: Path,
    message: str,
) -> Finding:
    return Finding("ERROR", folder.name, _relative(root, path), message)


def _prerequisite_findings(
    root: Path,
    folder: Path,
    entries: tuple[Mapping[str, object], ...],
    *,
    ledger_name: str,
    label: str,
) -> tuple[Finding, ...]:
    path = folder / "audit" / ledger_name
    findings: list[Finding] = []
    for entry in entries:
        name = str(entry.get("lean_name") or label).strip()
        judgment = str(
            entry.get("semantic_judgment") or "not recorded"
        ).strip().lower()
        if entry.get("semantic_current") is True and judgment in {
            "matches",
            "matches_approved_corrected_target",
        }:
            continue
        detail = str(entry.get("semantic_status") or "incomplete").strip()
        if entry.get("semantic_current") is True and judgment in {
            "mismatch",
            "uncertain",
        }:
            detail = f"current source judgment is `{judgment}`"
        findings.append(
            _finding(
                root,
                folder,
                path,
                f"{name}: {label} is not a current `matches` verdict ({detail})",
            )
        )
    return tuple(findings)


def _evaluate_current_v11_semantic_review(
    repository_root: Path,
    folder: Path,
    context: V11EvidenceRunContext,
    *,
    require_graph_checkpoint: bool = False,
) -> CurrentV11SemanticReviewResult:
    root = repository_root.resolve()
    paper = folder.resolve()
    map_path = paper / "audit" / "paper_statement_map.json"
    interface_path = paper / "PaperInterface.lean"
    screening_path = paper / "audit" / "v11_raw_source_spec_screening.json"

    if (
        not isinstance(context, V11EvidenceRunContext)
        or not context.issued_by_builder
        or context.folder != paper
        or not context.v11_lean_claim_graph_selected
    ):
        return CurrentV11SemanticReviewResult(
            surface=None,
            selection_error=(
                "current v11 semantic review requires its exact issued transaction"
            ),
        )
    if paper.parent != root / "papers":
        return CurrentV11SemanticReviewResult(
            surface=None,
            selection_error=(
                "current v11 semantic review requires the transaction's canonical "
                "repository root"
            ),
        )
    if context.status not in CLOSEOUT_STATUSES:
        return CurrentV11SemanticReviewResult(
            surface=None,
            selection_error="paper status does not select a closeout review lane",
        )
    source_map = context.statement_map
    if not isinstance(source_map, Mapping):
        return CurrentV11SemanticReviewResult(
            surface=None,
            selection_error="issued v11 transaction has no frozen statement map",
        )

    try:
        route_set = EvidenceRouteSet.from_source_map(source_map)
        specifications = route_set.result_specifications()
    except ObligationRouteError as exc:
        return CurrentV11SemanticReviewResult(
            surface=None,
            direct_findings=(
                _finding(root, paper, map_path, f"invalid typed source routes: {exc}"),
            ),
        )
    if not specifications:
        return CurrentV11SemanticReviewResult(
            surface=None,
            direct_findings=(
                _finding(
                    root,
                    paper,
                    map_path,
                    "v11 closeout selected no asserted source-facing Spec declarations",
                ),
            ),
        )

    try:
        surface_builder = (
            read_diagnostic_v11_review_surface
            if require_graph_checkpoint
            else build_accepting_v11_review_surface
        )
        surface = surface_builder(
            root,
            paper,
            specifications,
            context=context,
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return CurrentV11SemanticReviewResult(
            surface=None,
            direct_findings=(
                _finding(
                    root,
                    paper,
                    interface_path,
                    "could not obtain the current Lean semantic graph: " + str(exc),
                ),
            ),
        )

    direct_findings: list[Finding] = []
    normalized_direct_items: Mapping[str, Mapping[str, object]] = MappingProxyType(
        {}
    )
    screening = context.json_payload(screening_path)
    container = validate_v11_screening_container(
        screening,
        paper=paper.name,
    )
    if container.usable_item_ledger and isinstance(screening, Mapping):
        try:
            normalized_screening = normalized_direct_screening_ledger(
                paper_dir=paper,
                source_map=source_map,
                screening=screening,
                route_set=route_set,
                semantic_targets=surface.semantic_targets,
                repository_root=root,
                file_bytes_override=context.file_bytes_override(),
            )
            normalized_items = normalized_screening.get("items")
            if not isinstance(normalized_items, Mapping):
                raise ValueError("normalized v11 screening has no item map")
            normalized_direct_items = MappingProxyType(
                {
                    str(name): MappingProxyType(dict(row))
                    for name, row in normalized_items.items()
                    if isinstance(name, str) and isinstance(row, Mapping)
                }
            )
            if len(normalized_direct_items) != len(normalized_items):
                raise ValueError("normalized v11 screening has a malformed item")
        except ValueError as exc:
            direct_findings.append(
                _finding(
                    root,
                    paper,
                    screening_path,
                    "v11 source-to-Spec review is not current: " + str(exc),
                )
            )
    else:
        for error in container.errors:
            direct_findings.append(_finding(root, paper, screening_path, error))

    paper_findings = _prerequisite_findings(
        root,
        paper,
        surface.paper_prerequisites,
        ledger_name="paper_semantic_prerequisites.json",
        label="paper-local semantic prerequisite",
    )
    library_findings = _prerequisite_findings(
        root,
        paper,
        surface.library_prerequisites,
        ledger_name="library_semantic_review.json",
        label="material library semantic review",
    )
    return CurrentV11SemanticReviewResult(
        surface=surface,
        direct_findings=tuple(direct_findings),
        paper_prerequisite_findings=paper_findings,
        library_prerequisite_findings=library_findings,
        normalized_direct_items=normalized_direct_items,
    )


def current_v11_semantic_review_result(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
    require_graph_checkpoint: bool = False,
) -> CurrentV11SemanticReviewResult:
    """Return the one cached semantic verdict for this exact transaction.

    ``require_graph_checkpoint`` keeps read-only document migrations on the
    diagnostic reader, which fails closed instead of acquiring a missing Lean
    graph.  The separate cache key prevents an accepting-path value from
    bypassing that requirement.
    """

    result = run_scoped_cached_value(
        context,
        folder=folder,
        key=(
            "verdict",
            "current_v11_direct_semantic_review",
            repository_root.resolve().as_posix(),
            require_graph_checkpoint,
        ),
        compute=lambda: _evaluate_current_v11_semantic_review(
            repository_root,
            folder,
            context,
            require_graph_checkpoint=require_graph_checkpoint,
        ),
    )
    if not isinstance(result, CurrentV11SemanticReviewResult):
        raise TypeError("current v11 semantic-review cache contains a foreign value")
    return result


def current_v11_raw_source_spec_screening_findings(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
) -> list[Finding]:
    """Return direct and paper-local findings from the exact verdict.

    Reusable-library findings are projected separately so the historical
    integrity aggregator does not report the same error twice.
    """

    result = current_v11_semantic_review_result(
        repository_root,
        folder,
        context=context,
    )
    if result.selection_error:
        return [
            _finding(
                repository_root.resolve(),
                folder.resolve(),
                folder.resolve() / "status.json",
                "current v11 source-to-Spec review is unavailable: "
                + result.selection_error,
            )
        ]
    return list(result.direct_findings + result.paper_prerequisite_findings)


def current_v11_material_library_semantic_review_findings(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
) -> list[Finding]:
    """Return the library component of the one exact semantic verdict."""

    result = current_v11_semantic_review_result(
        repository_root,
        folder,
        context=context,
    )
    if result.selection_error:
        return [
            _finding(
                repository_root.resolve(),
                folder.resolve(),
                folder.resolve() / "audit" / "library_semantic_review.json",
                "current material-library semantic review is unavailable: "
                + result.selection_error,
            )
        ]
    if result.surface is None:
        detail = (
            result.direct_findings[0].message
            if result.direct_findings
            else "the current Lean semantic surface is unavailable"
        )
        return [
            _finding(
                repository_root.resolve(),
                folder.resolve(),
                folder.resolve() / "audit" / "library_semantic_review.json",
                "current material-library semantic review could not be evaluated: "
                + detail,
            )
        ]
    return list(result.library_prerequisite_findings)


def current_v11_direct_semantic_review_state(
    repository_root: Path,
    folder: Path,
    *,
    context: V11EvidenceRunContext,
) -> tuple[bool, str]:
    """Return whether every current source/Lean semantic judgment passes."""

    result = current_v11_semantic_review_result(
        repository_root,
        folder,
        context=context,
    )
    if result.semantic_review_current:
        return True, ""
    if result.selection_error:
        return False, result.selection_error
    if result.findings:
        return False, result.findings[0].message
    return False, "v11 direct semantic-review evidence is incomplete"
