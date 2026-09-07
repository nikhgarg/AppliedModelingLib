#!/usr/bin/env python3
"""Graph-native canonical paper closure credentials.

Schema-5 ``FINAL_CLOSURE_RECEIPT.md`` is only a stable human-readable pointer.
The selected schema-2 obligation bundle is the sole acceptance credential.  A
current verifier authenticates that complete graph against the current source
inventory, exact source bytes, registered obligation contracts and issuing
engine, selected proof endpoints, and passed build leaf. Exact historical Lean
import-closure bytes are the fast path. Engine-projected aggregate labels are
provenance only once the current route structure, source bytes, and exact Lean
import closure all match. If that import closure drifts, the verifier reuses the same
current-material validators as closeout and asks Lean to reproduce every
reviewed transparent semantic target and typed Spec/proof route. It never
invokes an LLM or creates new semantic evidence.

Legacy receipt schemas remain independently valid under their recorded schema.
Promotion validates one such receipt once, reattests the unchanged leaves under
the current registered terminal verifier, and atomically selects an accepting
bundle.  No engine-version pair or compatibility bridge is involved.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import re
import shlex
import sys
from collections.abc import Iterable, Iterator, Mapping
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import date
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, Protocol

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_formalization_engine_revision import (
    EngineRevisionError,
    validate_runtime_engine_registration,
    validated_recorded_engine_revision_ledger,
)
from scripts.accepted_obligation_graph import (
    AcceptedObligationGraphError,
    build_accepted_obligation_graph,
)
from scripts.current_closeout.pass_capability import (
    current_closeout_pass_authority,
    validate_current_closeout_pass,
)
from scripts.lean_import_closure import (
    lean_import_closure_source_only_recovery_problem,
    lean_import_closure_payload_sha256,
    validated_lean_import_closure_payload,
    validated_lean_import_closure_receipt_payload,
)

if TYPE_CHECKING:
    from scripts.lean_signature_manifest import RepositoryBuildInputSnapshotProvider
from scripts.closeout_document_gates import final_holistic_audit_hard_errors
from scripts.final_adversarial_review_panel import (
    FinalAdversarialReviewPanelError,
    validated_final_adversarial_review_artifact_paths,
)
from scripts.final_holistic_audit_surface import (
    FinalHolisticAuditSurfaceError,
    build_current_final_holistic_source_assurance_projection,
    final_holistic_audit_surface_contract_is_supported,
    final_holistic_audit_surface_sha256,
    final_holistic_source_assurance_projection_sha256,
    final_holistic_source_assurance_v2_projection,
    final_holistic_source_assurance_v2_projection_sha256,
    final_holistic_source_assurance_v2_sha256,
    historical_final_holistic_source_assurance_sha256s,
)
from scripts.immutable_json import freeze_json
from scripts.obligation_closeout_state import (
    ObligationCloseoutStateError,
    verify_current_stored_paper_obligations,
)
from scripts.obligation_evidence_contracts import (
    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT,
)
from scripts.obligation_evidence_graph import ObligationKind
from scripts.obligation_evidence_issuance import (
    STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256,
)
from scripts.obligation_evidence_store import (
    PACKED_ACCEPTED_GRAPH_POINTER_SCHEMA,
    LoadedPaperObligationBundle,
    ObligationEvidenceStoreError,
    _atomic_write,
    current_accepted_graph_path,
    current_bundle_path,
    load_accepted_obligation_graph,
    load_lean_import_closure_preimage,
    load_obligation_evidence_store_snapshot,
    load_paper_obligation_bundle,
    load_recorded_current_accepted_obligation_graph,
    store_accepted_obligation_graph,
    store_lean_import_closure_preimage,
)
from scripts.obligation_paper_bundle import (
    ACCEPTING_PAPER_OBLIGATION_BUNDLE_SCHEMA,
)
from scripts.obligation_paper_index import (
    PaperObligationIndexError,
    current_reviewed_source_item_ids,
    prerequisite_source_judgments_by_source_item,
)
from scripts.obligation_preflight import (
    ObligationPreflightError,
    ObligationStructuralPreflight,
    structural_obligation_preflight,
)
from scripts.paper_build_command import is_exact_portable_paper_build_argv
from scripts.portable_evidence_identity import (
    canonical_json_bytes,
    portable_evidence_sha256,
)
from scripts.source_archive_surface import (
    resolve_paper_source_artifact_path,
    source_archive_surface_validation_issues,
)
from scripts.strict_closeout_authority import (
    StrictCloseoutAuthorityError,
    recorded_strict_closeout_authority,
    validate_strict_closeout_authority,
)

OBLIGATION_CLOSURE_RECEIPT_SCHEMA = 5
ACCEPTED_GRAPH_CLOSURE_RECEIPT_SCHEMA = 6
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
PAPER_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]*$")


class ObligationClosureCredentialError(ValueError):
    """The accepting graph or one of its current controls is invalid."""


class _InputMutationGuard(Protocol):
    def finalize_unchanged(self) -> bool: ...


@dataclass(frozen=True)
class _ExactFileInputMutationGuard:
    """Extend a build-input transaction across exact carrier bytes."""

    delegate: _InputMutationGuard
    exact_files: tuple[tuple[Path, bytes], ...]

    def _files_unchanged(self) -> bool:
        try:
            return all(path.read_bytes() == raw for path, raw in self.exact_files)
        except OSError:
            return False

    def finalize_unchanged(self) -> bool:
        if not self._files_unchanged():
            return False
        if not self.delegate.finalize_unchanged():
            return False
        return self._files_unchanged()


def revalidate_terminal_lean_semantics(*args: Any, **kwargs: Any) -> Any:
    """Load the expensive declaration-level recovery lane only after drift."""

    from scripts.terminal_lean_semantic_revalidation import (
        revalidate_terminal_lean_semantics as revalidate,
    )

    return revalidate(*args, **kwargs)


@dataclass(frozen=True)
class VerifiedObligationClosureCredential:
    paper: str
    receipt_path: Path
    payload: Mapping[str, Any]
    credential_sha256: str
    graph_sha256: str
    paper_index_sha256: str
    terminal_verification_sha256: str
    bundle_sha256: str | None = None
    terminal_validation_route: str = "exact_import_closure"
    terminal_validation_detail: str = ""


@dataclass(frozen=True)
class RecordedObligationGraphProjection:
    """Authenticated, nonaccepting facts safe for derived presentation."""

    graph_sha256: str
    review_declarations_by_source_item: Mapping[str, tuple[str, ...]]
    card_review_declarations_by_source_item: Mapping[str, tuple[str, ...]]
    source_lean_verdicts_by_source_item: Mapping[str, str]
    source_input_bundle_sha256s_by_source_item: Mapping[
        str, str | tuple[str, ...]
    ]
    claim_semantic_target_sha256s_by_specification: Mapping[str, str]
    prerequisite_semantic_target_sha256s_by_declaration: Mapping[str, str]
    reviewed_display_surface_complete: bool
    source_review_metadata_by_specification: Mapping[
        str, Mapping[str, str]
    ] = MappingProxyType({})
    prerequisite_review_metadata_by_declaration: Mapping[
        str, Mapping[str, str]
    ] = MappingProxyType({})


@dataclass(frozen=True)
class AuthenticatedAcceptedGraphSemanticReviewInputs:
    """Exact accepted-graph inputs for a nonaccepting document digest.

    The accepted graph remains the sole authority for the recorded semantic
    targets and judgments.  The current source map and review ledgers are
    included only after their exact rows have been authenticated by the
    graph's strict-closeout issuances and current Lean/import/build controls
    have passed without semantic recovery.
    """

    graph_sha256: str
    source_map: Mapping[str, Any]
    direct_review_ledger: Mapping[str, Any]
    paper_prerequisite_ledger: Mapping[str, Any]
    library_prerequisite_ledger: Mapping[str, Any]
    direct_target_identities_by_specification: Mapping[
        str, Mapping[str, str]
    ]
    prerequisite_target_identities_by_declaration: Mapping[
        str, Mapping[str, str]
    ]


@dataclass(frozen=True)
class _CurrentControls:
    loaded: Any
    preflight: ObligationStructuralPreflight
    authority_sha256s: tuple[str, ...]
    current_engine_sha256: str
    input_guard: _InputMutationGuard
    watched_input_sha256s: Mapping[str, str]
    terminal_validation_route: str
    terminal_validation_detail: str


def _sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _sha256_file(path: Path) -> str:
    try:
        return _sha256_bytes(path.read_bytes())
    except OSError as exc:
        raise ObligationClosureCredentialError(
            f"could not read `{path}`: {exc}"
        ) from exc


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise ObligationClosureCredentialError(f"{field} is not SHA-256")
    return text


def _json(path: Path, label: str) -> Mapping[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ObligationClosureCredentialError(f"{label} is unreadable: {exc}") from exc
    if not isinstance(value, Mapping):
        raise ObligationClosureCredentialError(f"{label} is not an object")
    return value


def _recorded_engine_authorities(root: Path) -> tuple[str, ...]:
    """Return immutable registered issuers without hashing the live engine."""

    try:
        ledger = validated_recorded_engine_revision_ledger(root)
    except EngineRevisionError as exc:
        raise ObligationClosureCredentialError(
            "registered formalization engine is unavailable: " + str(exc)
        ) from exc
    revisions = ledger.get("revisions") if isinstance(ledger, Mapping) else None
    if not isinstance(revisions, list):
        raise ObligationClosureCredentialError(
            "registered formalization engine history is unavailable"
        )
    return tuple(
        sorted(
            {
                _sha256(revision.get("engine_tree_sha256"), "registered engine")
                for revision in revisions
                if isinstance(revision, Mapping)
            }
        )
    )


def _registered_engine_authorities(root: Path) -> tuple[str, tuple[str, ...]]:
    try:
        current = validate_runtime_engine_registration(root)
        authorities = _recorded_engine_authorities(root)
    except EngineRevisionError as exc:
        raise ObligationClosureCredentialError(
            "registered formalization engine is unavailable: " + str(exc)
        ) from exc
    if current.engine_tree_sha256 not in authorities:
        raise ObligationClosureCredentialError(
            "current formalization engine is absent from registered history"
        )
    return current.engine_tree_sha256, authorities


def _current_preflight(
    root: Path, paper: str
) -> tuple[ObligationStructuralPreflight, tuple[Path, ...], Mapping[str, Any]]:
    paper_dir = root / "papers" / paper
    audit_dir = paper_dir / "audit"
    map_path = audit_dir / "paper_statement_map.json"
    source_map = _json(map_path, "paper statement map")
    preflight = structural_obligation_preflight(
        source_map,
        paper=paper,
        # An obligation graph already carries the checked source-to-proof
        # realization leaf.  Revalidating or publishing that graph must not
        # depend on retaining the predecessor worksheet used to construct the
        # leaf.  Existing partial worksheets remain fail-closed as malformed.
        require_source_spec_correspondence=False,
        # The accepted graph likewise owns every issued prerequisite judgment.
        # Current ledgers are human/release projections and cannot veto an
        # otherwise current graph merely because declaration navigation moved.
        require_prerequisite_ledger_bindings=False,
    )
    try:
        preflight.require_current()
    except ObligationPreflightError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    return (
        preflight,
        (map_path,),
        source_map,
    )


def _validate_current_source(
    root: Path,
    paper: str,
    source_map: Mapping[str, Any],
    *,
    allow_missing_source_bytes: bool,
) -> Path | None:
    paper_dir = root / "papers" / paper
    source_path, problem = resolve_paper_source_artifact_path(
        paper_dir,
        source_map.get("source_artifact_path"),
        repository_root=root,
    )
    if source_path is None:
        raise ObligationClosureCredentialError(
            "current source artifact path is invalid: " + problem
        )
    expected = _sha256(source_map.get("source_artifact_sha256"), "source artifact")
    if source_path.is_file():
        if _sha256_file(source_path) != expected:
            raise ObligationClosureCredentialError(
                "current source artifact bytes disagree with the obligation graph"
            )
    elif not allow_missing_source_bytes:
        raise ObligationClosureCredentialError("canonical source bytes are unavailable")
    archive_issues = source_archive_surface_validation_issues(
        paper_dir,
        source_map,
        repository_root=root,
        require_source_bytes=not allow_missing_source_bytes,
    )
    substantive_archive_issues = [
        issue
        for issue in archive_issues
        if not (allow_missing_source_bytes and issue.missing_bytes)
    ]
    if substantive_archive_issues:
        raise ObligationClosureCredentialError(
            "current archive-source provenance is invalid: "
            + "; ".join(issue.message for issue in substantive_archive_issues)
        )
    return source_path if source_path.is_file() else None


def _validate_current_build(
    root: Path,
    paper: str,
    loaded: LoadedPaperObligationBundle,
    preflight: ObligationStructuralPreflight,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    accepted_graph_external_artifact_authority: bool = False,
) -> tuple[
    _InputMutationGuard,
    tuple[Path, ...],
    bool,
    str,
]:
    from scripts.lean_signature_manifest import (
        RepositoryBuildInputSnapshotProvider,
        graph_authenticated_lean_import_closure_guard,
    )

    paper_dir = root / "papers" / paper
    audit_dir = paper_dir / "audit"
    status_path = paper_dir / "status.json"
    closure_path = audit_dir / "LEAN_IMPORT_CLOSURE_RECEIPT.json"
    status = _json(status_path, "paper status")
    try:
        actual_argv = shlex.split(str(status.get("build_target") or ""))
    except ValueError as exc:
        raise ObligationClosureCredentialError(
            "paper build target is malformed"
        ) from exc
    if not is_exact_portable_paper_build_argv(actual_argv, paper):
        raise ObligationClosureCredentialError(
            "paper build target is not the exact portable paper target"
        )
    canonical_argv = ["lake", "build", paper]

    build_ids = loaded.paper_index.leaf_sha256s_by_kind.get(ObligationKind.BUILD, ())
    if len(build_ids) != 1:
        raise ObligationClosureCredentialError(
            "accepting graph must contain exactly one build leaf"
        )
    build_leaf = loaded.graph.leaves[build_ids[0]]
    expected_targets = tuple(
        sorted(
            {
                digest
                for roles in loaded.paper_index.route_leaf_sha256s_by_source_item.values()
                for digest in roles.get("proof_endpoint", ())
            }
        )
    )
    if (
        tuple(build_leaf.semantic_payload["target_declaration_sha256s"])
        != expected_targets
    ):
        raise ObligationClosureCredentialError(
            "build leaf does not select every and only paper proof endpoint"
        )
    if build_leaf.semantic_payload["build_command_sha256"] != portable_evidence_sha256(
        {"schema": 1, "argv": canonical_argv}
    ):
        raise ObligationClosureCredentialError("build leaf command is stale")

    try:
        closure_raw = closure_path.read_bytes()
        closure_receipt = json.loads(closure_raw)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ObligationClosureCredentialError(
            "Lean import-closure receipt is unreadable: " + str(exc)
        ) from exc
    if not isinstance(closure_receipt, Mapping):
        raise ObligationClosureCredentialError(
            "Lean import-closure receipt is not an object"
        )
    try:
        closure_receipt = validated_lean_import_closure_receipt_payload(
            closure_receipt,
            paper=paper,
        )
    except ValueError as exc:
        raise ObligationClosureCredentialError(
            "Lean import-closure receipt fields are malformed: " + str(exc)
        ) from exc
    try:
        closure = validated_lean_import_closure_payload(
            closure_receipt.get("lean_import_closure")
        )
    except ValueError as exc:
        raise ObligationClosureCredentialError(
            "Lean import-closure payload is invalid: " + str(exc)
        ) from exc
    closure_sha256 = lean_import_closure_payload_sha256(closure)
    if _sha256(
        closure_receipt.get("lean_import_closure_sha256"),
        "Lean import closure",
    ) != closure_sha256:
        raise ObligationClosureCredentialError(
            "Lean import-closure receipt digest is stale"
        )
    accepted_closure_sha256 = _sha256(
        build_leaf.semantic_payload["lean_import_closure_sha256"],
        "build leaf Lean import closure",
    )
    controls = closure.get("build_controls")
    toolchains = (
        [
            item
            for item in controls
            if isinstance(item, Mapping) and item.get("path") == "lean-toolchain"
        ]
        if isinstance(controls, list)
        else []
    )
    if len(toolchains) != 1 or build_leaf.semantic_payload[
        "toolchain_sha256"
    ] != _sha256(
        toolchains[0].get("sha256") if toolchains else None,
        "Lean toolchain",
    ):
        raise ObligationClosureCredentialError("build leaf toolchain is stale")

    if closure_sha256 == accepted_closure_sha256:
        try:
            if build_input_provider is None:
                if accepted_graph_external_artifact_authority:
                    provider = graph_authenticated_lean_import_closure_guard(
                        root,
                        closure,
                    )
                else:
                    provider = RepositoryBuildInputSnapshotProvider(root)
                    provider.adopt_lean_import_closure_payload(closure)
            else:
                if accepted_graph_external_artifact_authority:
                    raise ValueError(
                        "accepted-graph validation cannot borrow a fresh-build provider"
                    )
                provider = build_input_provider
                if (
                    provider.root != root.resolve()
                    or not provider.owns_exact_lean_import_closure_payload(closure)
                ):
                    raise ValueError(
                        "shared Lean build-input provider does not own the current closure"
                    )
        except (OSError, RuntimeError, ValueError) as exc:
            raise ObligationClosureCredentialError(
                "current Lean import closure is invalid: " + str(exc)
            ) from exc
        return (
            _ExactFileInputMutationGuard(
                delegate=provider,
                exact_files=((closure_path, closure_raw),),
            ),
            (status_path, closure_path),
            False,
            "",
        )

    if not accepted_graph_external_artifact_authority:
        raise ObligationClosureCredentialError(
            "build leaf Lean import closure is stale"
        )
    if build_input_provider is not None:
        raise ObligationClosureCredentialError(
            "accepted-graph validation cannot borrow a fresh-build provider"
        )
    try:
        accepted_closure = load_lean_import_closure_preimage(
            root,
            paper,
            accepted_closure_sha256,
        )
        recovery_problem = lean_import_closure_source_only_recovery_problem(
            accepted_closure,
            closure,
        )
        if recovery_problem:
            raise ValueError(recovery_problem)
        provider = RepositoryBuildInputSnapshotProvider(root)
        provider.adopt_lean_import_closure_payload(closure)
    except (ObligationEvidenceStoreError, OSError, RuntimeError, ValueError) as exc:
        raise ObligationClosureCredentialError(
            "current Lean import closure cannot recover the accepted build: " + str(exc)
        ) from exc

    from scripts.terminal_lean_semantic_revalidation import (
        TerminalLeanSemanticRevalidationError,
    )

    ownership_paths = tuple(
        path
        for path in (
            audit_dir / "paper_semantic_prerequisites.json",
            audit_dir / "library_semantic_review.json",
        )
        if path.is_file()
    )
    ownership_input_sha256s = _snapshot(ownership_paths)
    _, _, authenticated_prerequisite_source_items = (
        _recorded_issued_review_metadata(root, paper, loaded, preflight)
    )
    try:
        provider, semantic_paths = revalidate_terminal_lean_semantics(
            root,
            paper,
            loaded,
            preflight=preflight,
            accepted_import_closure=accepted_closure,
            current_import_closure=closure,
            authenticated_prerequisite_source_items_by_declaration=(
                authenticated_prerequisite_source_items
            ),
            build_input_provider=provider,
        )
    except TerminalLeanSemanticRevalidationError as semantic_error:
        raise ObligationClosureCredentialError(
            "declaration-level revalidation failed: " + str(semantic_error)
        ) from semantic_error
    if authenticated_prerequisite_source_items and (
        _snapshot(ownership_paths) != ownership_input_sha256s
    ):
        raise ObligationClosureCredentialError(
            "authenticated prerequisite source ownership changed during "
            "terminal verification"
        )
    try:
        current_closure_raw = closure_path.read_bytes()
    except OSError as exc:
        raise ObligationClosureCredentialError(
            "Lean import-closure receipt disappeared during terminal verification: "
            + str(exc)
        ) from exc
    if current_closure_raw != closure_raw:
        raise ObligationClosureCredentialError(
            "Lean import-closure receipt changed during terminal verification"
        )
    authenticated_ownership_paths = (
        ownership_paths if authenticated_prerequisite_source_items else ()
    )
    return (
        _ExactFileInputMutationGuard(
            delegate=provider,
            exact_files=((closure_path, closure_raw),),
        ),
        tuple(
            dict.fromkeys(
                (
                    status_path,
                    closure_path,
                    *authenticated_ownership_paths,
                    *semantic_paths,
                )
            )
        ),
        True,
        "current closure differs from accepted closure only in repository source bytes",
    )


def _snapshot(paths: Iterable[Path]) -> Mapping[str, str]:
    result: dict[str, str] = {}
    for path in paths:
        result[path.resolve().as_posix()] = _sha256_file(path)
    return result


def _prepare_current_controls(
    root: Path,
    paper: str,
    loaded: LoadedPaperObligationBundle,
    *,
    authenticated_leaf_authority_sha256s: Iterable[str] = (),
    allow_missing_source_bytes: bool = False,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> _CurrentControls:
    preflight, preflight_paths, source_map = _current_preflight(root, paper)
    source_path = _validate_current_source(
        root,
        paper,
        source_map,
        allow_missing_source_bytes=allow_missing_source_bytes,
    )
    provider, build_paths, semantic_revalidated, validation_detail = (
        _validate_current_build(
            root,
            paper,
            loaded,
            preflight,
            build_input_provider=build_input_provider,
        )
    )
    current_engine, engine_authorities = _registered_engine_authorities(root)
    authorities = tuple(
        sorted(
            set(engine_authorities)
            | {
                _sha256(value, "authenticated leaf authority")
                for value in authenticated_leaf_authority_sha256s
            }
        )
    )
    try:
        verify_current_stored_paper_obligations(
            root,
            paper,
            loaded.paper_index,
            loaded.graph,
            preflight=preflight,
            authenticated_authority_sha256s=authorities,
        )
    except ObligationCloseoutStateError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    watched = (*preflight_paths, *build_paths)
    if source_path is not None:
        watched = (*watched, source_path)
    return _CurrentControls(
        loaded=loaded,
        preflight=preflight,
        authority_sha256s=authorities,
        current_engine_sha256=current_engine,
        input_guard=provider,
        watched_input_sha256s=_snapshot(watched),
        terminal_validation_route=(
            "lean_semantic_recovery"
            if semantic_revalidated
            else "exact_import_closure"
        ),
        terminal_validation_detail=validation_detail,
    )


def _prepare_accepted_graph_controls(
    root: Path,
    paper: str,
    *,
    graph_sha256: str | None = None,
    allow_missing_source_bytes: bool = False,
    allow_lean_semantic_recovery: bool = True,
) -> _CurrentControls:
    """Validate the selected graph credential without a bundle or producer."""

    preflight, preflight_paths, source_map = _current_preflight(root, paper)
    source_path = _validate_current_source(
        root,
        paper,
        source_map,
        allow_missing_source_bytes=allow_missing_source_bytes,
    )
    current_engine, authorities = _registered_engine_authorities(root)
    try:
        loaded = load_accepted_obligation_graph(
            root,
            paper,
            preflight=preflight,
            authenticated_authority_sha256s=authorities,
            require_current_aggregate_identity=False,
        )
    except ObligationEvidenceStoreError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    if graph_sha256 is not None and loaded.graph_sha256 != graph_sha256:
        raise ObligationClosureCredentialError(
            "schema-6 receipt does not select the current accepted graph"
        )
    terminal_paths: tuple[Path, ...] = ()
    if (
        loaded.closure_leaf.contract_sha256
        == STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
    ):
        closure_payload = loaded.closure_leaf.semantic_payload
        try:
            # Both direct results and paper/library prerequisites are already
            # bound to exact source atoms in the authenticated graph index.
            # Closed papers need not retain mutable issuance worksheets.
            reviewed_source_item_ids = current_reviewed_source_item_ids(
                loaded.paper_index, loaded.graph, preflight,
                source_map=source_map,
            )
            current_source_assurance = (
                build_current_final_holistic_source_assurance_projection(
                    root, paper=paper,
                    reviewed_source_item_ids=reviewed_source_item_ids,
                )
            )
            current_source_assurance_sha256 = (
                final_holistic_source_assurance_projection_sha256(
                    current_source_assurance
                )
            )
            current_source_assurance_v2 = (
                final_holistic_source_assurance_v2_projection(
                    current_source_assurance
                )
            )
            current_source_assurance_v2_sha256 = (
                final_holistic_source_assurance_v2_projection_sha256(
                    current_source_assurance_v2
                )
            )
        except (FinalHolisticAuditSurfaceError, PaperObligationIndexError) as exc:
            raise ObligationClosureCredentialError(str(exc)) from exc
        recorded_source_assurance_sha256 = closure_payload.get(
            "source_assurance_sha256"
        )
        historical_assurance = False
        authenticated_source_assurance = current_source_assurance_v2
        if recorded_source_assurance_sha256 == current_source_assurance_v2_sha256:
            pass
        elif recorded_source_assurance_sha256 == current_source_assurance_sha256:
            authenticated_source_assurance = current_source_assurance
        else:
            try:
                historical = historical_final_holistic_source_assurance_sha256s(
                    current_source_assurance, source_map=source_map
                )
            except FinalHolisticAuditSurfaceError as exc:
                raise ObligationClosureCredentialError(str(exc)) from exc
            if recorded_source_assurance_sha256 not in historical:
                raise ObligationClosureCredentialError(
                    "accepted graph source inventory, correction, defect, fidelity, or "
                    "status assurance is stale"
                )
            # Historical readers emit only their frozen pre-policy preimages.
            # A current policy-aware assurance can never select the old
            # single-review document contract merely because a panel or later
            # completeness marker is absent.
            historical_assurance = True
            authenticated_source_assurance = current_source_assurance
        frozen_review_policy_assurance = None
        source_assurance_is_policy_aware = (
            authenticated_source_assurance.get("schema") == 3
            or authenticated_source_assurance.get("v1_source_assurance_schema")
            == 3
        )
        if not historical_assurance and source_assurance_is_policy_aware:
            raw_review_policy_assurance = authenticated_source_assurance.get(
                "review_policy_assurance"
            )
            if not isinstance(raw_review_policy_assurance, Mapping):
                raise ObligationClosureCredentialError(
                    "accepted graph has malformed frozen review-policy assurance"
                )
            # This projection was reconstructed from disk, but its complete
            # digest has just matched the accepted closure leaf.  It is now an
            # authenticated frozen authority for reviewer cardinality.
            frozen_review_policy_assurance = dict(raw_review_policy_assurance)
        holistic_sha256 = str(
            closure_payload.get("final_holistic_audit_surface_sha256") or ""
        )
        holistic_errors = final_holistic_audit_hard_errors(
            root / "papers" / paper,
            target_surface_identity=holistic_sha256,
            require_surface_binding=True,
            allow_historical_missing_scope=historical_assurance,
            review_policy_assurance=frozen_review_policy_assurance,
        )
        if holistic_errors:
            raise ObligationClosureCredentialError(
                "accepted graph final holistic audit is stale: "
                + "; ".join(error.message for error in holistic_errors)
            )
        audit_dir = root / "papers" / paper / "audit"
        if frozen_review_policy_assurance is None:
            final_review_paths = (
                root / "papers" / paper / "docs" / "AGENT_SOURCE_AUDIT.md",
            )
        else:
            try:
                final_review_paths = (
                    validated_final_adversarial_review_artifact_paths(
                        root / "papers" / paper,
                        target_surface_identity=holistic_sha256,
                        review_policy_assurance=frozen_review_policy_assurance,
                    )
                )
            except FinalAdversarialReviewPanelError as exc:
                raise ObligationClosureCredentialError(str(exc)) from exc
        terminal_paths = (
            root / "papers" / paper / "status.json",
            *final_review_paths,
            *((audit_dir / "source_proof_fidelity.json",)
              if (audit_dir / "source_proof_fidelity.json").is_file()
              else ()),
        )
    provider, build_paths, semantic_revalidated, validation_detail = (
        _validate_current_build(
            root,
            paper,
            loaded,
            preflight,
            accepted_graph_external_artifact_authority=(
                allow_lean_semantic_recovery
            ),
        )
    )
    watched = (*preflight_paths, *build_paths, *terminal_paths)
    if source_path is not None:
        watched = (*watched, source_path)
    return _CurrentControls(
        loaded=loaded,
        preflight=preflight,
        authority_sha256s=authorities,
        current_engine_sha256=current_engine,
        input_guard=provider,
        watched_input_sha256s=_snapshot(watched),
        terminal_validation_route=(
            "lean_semantic_recovery"
            if semantic_revalidated
            else "exact_import_closure"
        ),
        terminal_validation_detail=validation_detail,
    )


def _finalize_controls(controls: _CurrentControls) -> None:
    if not controls.input_guard.finalize_unchanged():
        raise ObligationClosureCredentialError(
            "Lean import-closure inputs changed during terminal verification"
        )
    paths = tuple(Path(path) for path in controls.watched_input_sha256s)
    if _snapshot(paths) != controls.watched_input_sha256s:
        raise ObligationClosureCredentialError(
            "paper closure inputs changed during terminal verification"
        )


def _optional_file_bytes(path: Path) -> bytes | None:
    try:
        return path.read_bytes()
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ObligationClosureCredentialError(
            f"could not snapshot terminal selection `{path}`: {exc}"
        ) from exc


@contextmanager
def _terminal_selection_lock(root: Path, paper: str) -> Iterator[None]:
    """Serialize one paper's accepted pointer and rendered receipt update."""

    lock_path = current_accepted_graph_path(root, paper).with_name(
        ".terminal-selection.lock"
    )
    try:
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        stream = lock_path.open("a+b")
    except OSError as exc:
        raise ObligationClosureCredentialError(
            f"could not lock terminal selection for {paper}: {exc}"
        ) from exc
    try:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
    except OSError as exc:
        stream.close()
        raise ObligationClosureCredentialError(
            f"could not lock terminal selection for {paper}: {exc}"
        ) from exc
    try:
        yield
    finally:
        try:
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)
        finally:
            stream.close()


def _restore_terminal_migration_file(
    path: Path,
    *,
    old_bytes: bytes | None,
    migration_bytes: bytes,
) -> None:
    """Restore one migration output only while it still contains our bytes."""

    current = _optional_file_bytes(path)
    if current != migration_bytes or current == old_bytes:
        return
    try:
        if old_bytes is None:
            path.unlink()
        else:
            _atomic_write(path, old_bytes)
    except OSError as exc:
        raise ObligationClosureCredentialError(
            f"could not restore terminal selection `{path}`: {exc}"
        ) from exc


def _restore_terminal_migration_selection(
    *,
    pointer_path: Path,
    receipt_path: Path,
    old_pointer_bytes: bytes,
    old_receipt_bytes: bytes | None,
    new_pointer_bytes: bytes,
    new_receipt_bytes: bytes,
) -> None:
    """Undo only this migration's selected pointer and rendered receipt."""

    _restore_terminal_migration_file(
        pointer_path,
        old_bytes=old_pointer_bytes,
        migration_bytes=new_pointer_bytes,
    )
    _restore_terminal_migration_file(
        receipt_path,
        old_bytes=old_receipt_bytes,
        migration_bytes=new_receipt_bytes,
    )


def _receipt_payload(
    root: Path,
    paper: str,
    loaded: LoadedPaperObligationBundle,
) -> dict[str, Any]:
    return {
        "schema": OBLIGATION_CLOSURE_RECEIPT_SCHEMA,
        "paper": paper,
        "closure_status": "current",
        "acceptance_credential": False,
        "closed_at": date.today().isoformat(),
        "obligation_bundle": {
            "pointer": current_bundle_path(root, paper).relative_to(root).as_posix(),
            "bundle_sha256": loaded.bundle.bundle_sha256,
            "graph_sha256": loaded.graph.graph_sha256,
            "paper_index_sha256": loaded.paper_index.index_sha256,
            "terminal_verification_sha256": (
                loaded.bundle.terminal_verification_sha256
            ),
        },
    }


def _accepted_graph_receipt_payload(
    root: Path,
    paper: str,
    graph_sha256: str,
) -> dict[str, Any]:
    return {
        "schema": ACCEPTED_GRAPH_CLOSURE_RECEIPT_SCHEMA,
        "paper": paper,
        "closure_status": "current",
        "acceptance_credential": False,
        "closed_at": date.today().isoformat(),
        "accepted_graph": {
            "pointer": current_accepted_graph_path(root, paper)
            .relative_to(root)
            .as_posix(),
            "graph_sha256": graph_sha256,
        },
    }


def _toml_string(value: object) -> str:
    return json.dumps(str(value), ensure_ascii=True)


def render_obligation_closure_receipt(payload: Mapping[str, Any]) -> str:
    if payload.get("schema") == ACCEPTED_GRAPH_CLOSURE_RECEIPT_SCHEMA:
        graph = payload["accepted_graph"]
        assert isinstance(graph, Mapping)
        return "\n".join(
            [
                "+++",
                f"schema = {payload['schema']}",
                f"paper = {_toml_string(payload['paper'])}",
                f"closure_status = {_toml_string(payload['closure_status'])}",
                "acceptance_credential = false",
                f"closed_at = {_toml_string(payload['closed_at'])}",
                "",
                "[accepted_graph]",
                f"pointer = {_toml_string(graph['pointer'])}",
                f"graph_sha256 = {_toml_string(graph['graph_sha256'])}",
                "",
                "+++",
                "",
                "# Final closure receipt",
                "",
                "This file points to the selected accepted obligation graph. The graph's",
                "terminal closure root is the sole machine acceptance credential.",
                "",
            ]
        )
    bundle = payload["obligation_bundle"]
    assert isinstance(bundle, Mapping)
    lines = [
        "+++",
        f"schema = {payload['schema']}",
        f"paper = {_toml_string(payload['paper'])}",
        f"closure_status = {_toml_string(payload['closure_status'])}",
        "acceptance_credential = false",
        f"closed_at = {_toml_string(payload['closed_at'])}",
        "",
        "[obligation_bundle]",
    ]
    for field in (
        "pointer",
        "bundle_sha256",
        "graph_sha256",
        "paper_index_sha256",
        "terminal_verification_sha256",
    ):
        lines.append(f"{field} = {_toml_string(bundle[field])}")
    lines.extend(
        [
            "",
            "+++",
            "",
            "# Final closure receipt",
            "",
            "This file points to the complete accepting obligation graph. The graph,",
            "its authenticated leaf issuances, and current source/Lean/build controls",
            "are the sole machine acceptance credential.",
            "",
        ]
    )
    return "\n".join(lines)


def validate_obligation_closure_receipt(
    root: Path,
    paper: str,
    *,
    receipt_path: Path,
    payload: Mapping[str, Any],
    allow_missing_source_bytes: bool = False,
) -> VerifiedObligationClosureCredential:
    """Validate the graph-native receipt without running any producer."""

    if payload.get("schema") == ACCEPTED_GRAPH_CLOSURE_RECEIPT_SCHEMA:
        return _validate_accepted_graph_closure_receipt(
            root,
            paper,
            receipt_path=receipt_path,
            payload=payload,
            allow_missing_source_bytes=allow_missing_source_bytes,
        )

    if not PAPER_RE.fullmatch(paper):
        raise ObligationClosureCredentialError("paper identifier is malformed")
    required = {
        "schema",
        "paper",
        "closure_status",
        "acceptance_credential",
        "closed_at",
        "obligation_bundle",
    }
    if (
        set(payload) != required
        or payload.get("schema") != OBLIGATION_CLOSURE_RECEIPT_SCHEMA
        or payload.get("paper") != paper
        or payload.get("closure_status") != "current"
        or payload.get("acceptance_credential") is not False
    ):
        raise ObligationClosureCredentialError(
            "schema-5 closure receipt fields are malformed"
        )
    try:
        date.fromisoformat(str(payload.get("closed_at") or ""))
    except ValueError as exc:
        raise ObligationClosureCredentialError(
            "schema-5 closed_at must be YYYY-MM-DD"
        ) from exc
    raw_bundle = payload.get("obligation_bundle")
    bundle_fields = {
        "pointer",
        "bundle_sha256",
        "graph_sha256",
        "paper_index_sha256",
        "terminal_verification_sha256",
    }
    if not isinstance(raw_bundle, Mapping) or set(raw_bundle) != bundle_fields:
        raise ObligationClosureCredentialError(
            "schema-5 obligation bundle pointer is malformed"
        )
    expected_pointer = current_bundle_path(root, paper).relative_to(root).as_posix()
    if raw_bundle.get("pointer") != expected_pointer:
        raise ObligationClosureCredentialError(
            "schema-5 receipt names a noncanonical obligation bundle pointer"
        )
    bundle_sha256 = _sha256(raw_bundle.get("bundle_sha256"), "obligation bundle")
    try:
        loaded = load_paper_obligation_bundle(
            root,
            paper,
            bundle_sha256=bundle_sha256,
        )
        current = load_paper_obligation_bundle(root, paper)
    except ObligationEvidenceStoreError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    if current.bundle.bundle_sha256 != bundle_sha256:
        raise ObligationClosureCredentialError(
            "schema-5 receipt does not select the current obligation bundle"
        )
    if (
        loaded.bundle.schema != ACCEPTING_PAPER_OBLIGATION_BUNDLE_SCHEMA
        or not loaded.bundle.acceptance_credential
        or loaded.graph.graph_sha256
        != _sha256(raw_bundle.get("graph_sha256"), "obligation graph")
        or loaded.paper_index.index_sha256
        != _sha256(raw_bundle.get("paper_index_sha256"), "paper index")
        or loaded.bundle.terminal_verification_sha256
        != _sha256(
            raw_bundle.get("terminal_verification_sha256"),
            "terminal verification",
        )
    ):
        raise ObligationClosureCredentialError(
            "schema-5 receipt disagrees with its accepting obligation bundle"
        )
    controls = _prepare_current_controls(
        root,
        paper,
        loaded,
        allow_missing_source_bytes=allow_missing_source_bytes,
    )
    _finalize_controls(controls)
    return VerifiedObligationClosureCredential(
        paper=paper,
        receipt_path=receipt_path,
        payload=payload,
        credential_sha256=bundle_sha256,
        bundle_sha256=bundle_sha256,
        graph_sha256=loaded.graph.graph_sha256,
        paper_index_sha256=loaded.paper_index.index_sha256,
        terminal_verification_sha256=str(loaded.bundle.terminal_verification_sha256),
        terminal_validation_route=getattr(
            controls, "terminal_validation_route", "exact_import_closure"
        ),
        terminal_validation_detail=getattr(
            controls, "terminal_validation_detail", ""
        ),
    )


def _validate_accepted_graph_closure_receipt(
    root: Path,
    paper: str,
    *,
    receipt_path: Path,
    payload: Mapping[str, Any],
    allow_missing_source_bytes: bool,
) -> VerifiedObligationClosureCredential:
    graph_sha256 = _schema6_graph_sha256(root, paper, payload)
    controls = _prepare_accepted_graph_controls(
        root,
        paper,
        graph_sha256=graph_sha256,
        allow_missing_source_bytes=allow_missing_source_bytes,
    )
    current = controls.loaded
    _finalize_controls(controls)
    closure = current.closure_leaf.semantic_payload
    return VerifiedObligationClosureCredential(
        paper=paper,
        receipt_path=receipt_path,
        payload=payload,
        credential_sha256=graph_sha256,
        graph_sha256=current.semantic_graph.graph_sha256,
        paper_index_sha256=current.paper_index.index_sha256,
        terminal_verification_sha256=str(closure["terminal_verification_sha256"]),
        terminal_validation_route=getattr(
            controls, "terminal_validation_route", "exact_import_closure"
        ),
        terminal_validation_detail=getattr(
            controls, "terminal_validation_detail", ""
        ),
    )


def _schema6_graph_sha256(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
) -> str:
    """Validate only the stable schema-6 pointer fields and return its graph."""

    if not PAPER_RE.fullmatch(paper):
        raise ObligationClosureCredentialError("paper identifier is malformed")
    required = {
        "schema",
        "paper",
        "closure_status",
        "acceptance_credential",
        "closed_at",
        "accepted_graph",
    }
    if (
        set(payload) != required
        or payload.get("schema") != ACCEPTED_GRAPH_CLOSURE_RECEIPT_SCHEMA
        or payload.get("paper") != paper
        or payload.get("closure_status") != "current"
        or payload.get("acceptance_credential") is not False
    ):
        raise ObligationClosureCredentialError(
            "schema-6 closure receipt fields are malformed"
        )
    try:
        date.fromisoformat(str(payload.get("closed_at") or ""))
    except ValueError as exc:
        raise ObligationClosureCredentialError(
            "schema-6 closed_at must be YYYY-MM-DD"
        ) from exc
    raw_graph = payload.get("accepted_graph")
    if not isinstance(raw_graph, Mapping) or set(raw_graph) != {
        "pointer",
        "graph_sha256",
    }:
        raise ObligationClosureCredentialError(
            "schema-6 accepted-graph pointer is malformed"
        )
    expected_pointer = (
        current_accepted_graph_path(root, paper).relative_to(root).as_posix()
    )
    if raw_graph.get("pointer") != expected_pointer:
        raise ObligationClosureCredentialError(
            "schema-6 receipt names a noncanonical accepted-graph pointer"
        )
    return _sha256(raw_graph.get("graph_sha256"), "accepted obligation graph")


def recorded_accepted_graph_lean_import_closure_sha256(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
) -> str:
    """Return the build-input identity recorded by one schema-6 graph.

    This authenticates only stable receipt fields, the canonical selected
    pointer, the content-addressed graph, and its unique build leaf.  It does
    not establish current closure.  A planner may use the result to prove that
    a matching saved input carrier is stale, but never to accept a paper or to
    skip full validation when currentness remains possible.
    """

    graph_sha256 = _schema6_graph_sha256(root, paper, payload)
    try:
        graph = load_recorded_current_accepted_obligation_graph(
            root,
            paper,
            graph_sha256,
        )
    except ObligationEvidenceStoreError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    build_leaves = tuple(
        leaf for leaf in graph.leaves.values() if leaf.kind is ObligationKind.BUILD
    )
    if len(build_leaves) != 1:
        raise ObligationClosureCredentialError(
            "recorded accepted graph does not contain exactly one build leaf"
        )
    return _sha256(
        build_leaves[0].semantic_payload.get("lean_import_closure_sha256"),
        "recorded accepted-graph Lean import closure",
    )


def _selected_accepted_graph_from_receipt(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
    *,
    preflight: ObligationStructuralPreflight,
    authority_sha256s: Iterable[str],
):
    """Bind the pointer to the selected graph using already checked controls."""

    graph_sha256 = _schema6_graph_sha256(root, paper, payload)
    try:
        current = load_accepted_obligation_graph(
            root,
            paper,
            preflight=preflight,
            authenticated_authority_sha256s=authority_sha256s,
            require_current_aggregate_identity=False,
        )
    except ObligationEvidenceStoreError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    if current.graph_sha256 != graph_sha256:
        raise ObligationClosureCredentialError(
            "schema-6 receipt does not select the current accepted graph"
        )
    return current


def _recorded_source_lean_verdicts_by_source_item(
    current: Any,
    preflight: ObligationStructuralPreflight,
) -> Mapping[str, str]:
    """Project one conservative verdict for every graph-indexed source item.

    Result routes bind their source judgment directly. Source definitions and
    source conditions bind the same source atoms through one or more reviewed
    semantic-prerequisite declarations. An item matches only when every
    attached declaration matches; a mismatch dominates uncertainty.
    """

    graph = current.semantic_graph
    index = current.paper_index
    try:
        prerequisite_judgments = prerequisite_source_judgments_by_source_item(
            index, preflight
        )
    except (PaperObligationIndexError, ValueError) as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc

    projected: dict[str, str] = {}
    for source_item_id, roles in sorted(
        index.route_leaf_sha256s_by_source_item.items()
    ):
        direct_judgments = tuple(roles.get("source_lean_judgment", ()))
        if direct_judgments:
            judgment_digests = direct_judgments
        else:
            judgment_digests = prerequisite_judgments.get(source_item_id, ())
        verdicts = [
            str(graph.leaves[digest].semantic_payload.get("verdict") or "")
            for digest in judgment_digests
        ]
        if not verdicts:
            continue
        if "does_not_match" in verdicts:
            projected[source_item_id] = "does_not_match"
        elif "uncertain" in verdicts:
            projected[source_item_id] = "uncertain"
        elif all(verdict == "matches" for verdict in verdicts):
            projected[source_item_id] = "matches"

    return MappingProxyType(projected)


def _recorded_source_input_bundles_by_source_item(
    current: Any,
    preflight: ObligationStructuralPreflight,
    *,
    authenticated_prerequisite_source_items_by_declaration: Mapping[str, str] = (
        MappingProxyType({})
    ),
) -> Mapping[str, str | tuple[str, ...]]:
    """Project the reviewed verbatim-source bundles for each source item.

    Result items own a direct source-to-Lean judgment.  Definition and
    condition items may instead reach several prerequisite judgments through
    the same source atoms.  In a portable graph-only checkout, distinct source
    items can intentionally share those exact atoms.  Without their private
    issuance rows, every bundle reviewed against the atoms remains an
    authenticated candidate for the source card.  Preserve that finite set
    instead of choosing one by declaration order.  A source-aware presentation
    still has to match one of the recorded bundles.
    """

    graph = current.semantic_graph
    index = current.paper_index
    authenticated_source_items = (
        _validated_authenticated_prerequisite_source_items_by_declaration(
            current,
            authenticated_prerequisite_source_items_by_declaration,
        )
    )
    try:
        prerequisite_judgments = prerequisite_source_judgments_by_source_item(
            index,
            preflight,
            authenticated_source_items_by_declaration=authenticated_source_items,
        )
    except (PaperObligationIndexError, ValueError) as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc

    projected: dict[str, str | tuple[str, ...]] = {}
    for source_item_id, roles in sorted(
        index.route_leaf_sha256s_by_source_item.items()
    ):
        direct_judgment_digests = tuple(
            roles.get("source_lean_judgment", ())
        )
        judgment_digests = direct_judgment_digests
        if not judgment_digests:
            judgment_digests = prerequisite_judgments.get(source_item_id, ())
        bundles = {
            _sha256(
                graph.leaves[digest].semantic_payload.get(
                    "verbatim_source_bundle_sha256"
                ),
                f"recorded source item {source_item_id} verbatim source bundle",
            )
            for digest in judgment_digests
        }
        if not bundles:
            continue
        ordered_bundles = tuple(sorted(bundles))
        if len(ordered_bundles) > 1 and (
            direct_judgment_digests or authenticated_source_items
        ):
            raise ObligationClosureCredentialError(
                "recorded graph binds multiple verbatim-source bundles to "
                f"authenticated source item {source_item_id}"
            )
        projected[source_item_id] = (
            ordered_bundles[0]
            if len(ordered_bundles) == 1
            else ordered_bundles
        )
    return MappingProxyType(projected)


def _recorded_review_declarations_by_source_item(
    preflight: ObligationStructuralPreflight,
) -> Mapping[str, tuple[str, ...]]:
    """Return the typed semantic-review declaration for each source item."""

    route_set = preflight.route_set
    if route_set is None:  # ``_current_preflight`` has already failed closed.
        raise ObligationClosureCredentialError(
            "recorded graph projection has no typed source routes"
        )
    projected: dict[str, tuple[str, ...]] = {}
    for route in route_set.routes:
        declarations = (
            (route.semantic_review_declaration,)
            if route.semantic_review_declaration
            else route.semantic_declarations
        )
        if declarations:
            projected[route.source_item_id] = tuple(declarations)
    return MappingProxyType(projected)


def _source_items_by_exact_atoms(current: Any) -> Mapping[tuple[str, ...], tuple[str, ...]]:
    """Return only graph-indexed source owners for each exact atom tuple."""

    grouped: dict[tuple[str, ...], list[str]] = {}
    for source_item_id, roles in current.paper_index.route_leaf_sha256s_by_source_item.items():
        atoms = tuple(roles.get("source_atom", ()))
        if atoms:
            grouped.setdefault(atoms, []).append(str(source_item_id))
    return MappingProxyType(
        {
            atoms: tuple(sorted(source_item_ids))
            for atoms, source_item_ids in grouped.items()
        }
    )


def _validated_authenticated_prerequisite_source_items_by_declaration(
    current: Any,
    authenticated_source_items: Mapping[str, str],
) -> Mapping[str, str]:
    """Accept issued source ownership only when it still binds exact atoms."""

    source_items_by_atoms = _source_items_by_exact_atoms(current)
    prerequisites = current.paper_index.prerequisite_leaf_sha256s_by_declaration
    validated: dict[str, str] = {}
    for declaration, source_item_id in sorted(authenticated_source_items.items()):
        roles = prerequisites.get(declaration)
        if not isinstance(roles, Mapping):
            raise ObligationClosureCredentialError(
                "recorded prerequisite source owner names a declaration absent from "
                f"the accepted graph: {declaration}"
            )
        owner = str(source_item_id or "").strip()
        atoms = tuple(roles.get("source_atom", ()))
        if not owner or owner not in source_items_by_atoms.get(atoms, ()):
            raise ObligationClosureCredentialError(
                "recorded prerequisite source owner does not bind exact source "
                f"atoms for {declaration}"
            )
        validated[str(declaration)] = owner
    return MappingProxyType(validated)


def _recorded_card_review_declarations_by_source_item(
    current: Any,
    preflight: ObligationStructuralPreflight,
    *,
    authenticated_prerequisite_source_items_by_declaration: Mapping[str, str] = (
        MappingProxyType({})
    ),
) -> Mapping[str, tuple[str, ...]]:
    """Return the complete claim/prerequisite card surface by source item.

    Status selection needs only each route's primary semantic declaration.
    Human packets additionally show every semantic prerequisite reviewed
    against that route's exact source atoms.  Keep these projections distinct
    so prerequisite cards cannot disappear while status-name resolution stays
    based on the paper's explicitly selected result/condition declarations.
    """

    primary = _recorded_review_declarations_by_source_item(preflight)
    declarations = {source_item: set(names) for source_item, names in primary.items()}
    typed_source_items_by_declaration: dict[str, set[str]] = {}
    for source_item_id, names in primary.items():
        for declaration in names:
            typed_source_items_by_declaration.setdefault(declaration, set()).add(
                source_item_id
            )
    source_items_by_atoms = _source_items_by_exact_atoms(current)
    authenticated_source_items = (
        _validated_authenticated_prerequisite_source_items_by_declaration(
            current,
            authenticated_prerequisite_source_items_by_declaration,
        )
    )

    for (
        declaration,
        roles,
    ) in current.paper_index.prerequisite_leaf_sha256s_by_declaration.items():
        # A complete prerequisite-ledger row carries the source item selected
        # for the judgment.  It is usable here only after
        # ``_recorded_issued_review_metadata`` has authenticated that whole
        # row to this accepted judgment leaf.  This resolves shared source
        # atom sets without using names or mutable presentation metadata.
        authenticated_source_item = authenticated_source_items.get(str(declaration))
        typed_source_items = typed_source_items_by_declaration.get(
            str(declaration)
        )
        if (
            authenticated_source_item is not None
            and typed_source_items is not None
            and authenticated_source_item not in typed_source_items
        ):
            raise ObligationClosureCredentialError(
                "recorded prerequisite source owner conflicts with typed route "
                f"for {declaration}"
            )
        atoms = tuple(roles.get("source_atom", ()))
        if authenticated_source_item is not None:
            declarations.setdefault(authenticated_source_item, set()).add(
                str(declaration)
            )
            continue
        # An explicit typed route is the authoritative source-item ownership
        # relation.  Do not try to rediscover that relation from source bytes:
        # one source excerpt may intentionally define several separately
        # reviewed declarations, so identical source-atom sets need not name a
        # unique route.  Atom-based inference remains only for recursive
        # prerequisites that do not have their own typed source route.
        if typed_source_items is not None or not atoms:
            continue
        source_items = source_items_by_atoms.get(atoms, [])
        if len(source_items) != 1:
            raise ObligationClosureCredentialError(
                "recorded prerequisite source atoms do not resolve to one "
                f"source item for {declaration}"
            )
        declarations.setdefault(source_items[0], set()).add(str(declaration))

    return MappingProxyType(
        {
            source_item: tuple(sorted(names))
            for source_item, names in sorted(declarations.items())
        }
    )


def _recorded_reviewed_target_identity(
    current: Any,
    leaf_sha256: str,
    *,
    expected_kind: str,
    field: str,
) -> Mapping[str, str] | None:
    """Return graph-authenticated target identities when the leaf records them.

    Earlier accepted graphs instead retain Lean's canonical signature and
    proposition-graph identities. Those facts remain valid recorded closure,
    but they cannot authenticate pretty-printed packet bytes without Lean, so
    this nonaccepting presentation projection simply omits them.
    """

    try:
        leaf = current.semantic_graph.leaves[leaf_sha256]
    except KeyError as exc:
        raise ObligationClosureCredentialError(
            f"{field} names a Lean leaf outside the recorded graph"
        ) from exc
    if (
        leaf.kind is not ObligationKind.LEAN_DECLARATION
        or leaf.semantic_payload.get("semantic_target_kind") != expected_kind
    ):
        raise ObligationClosureCredentialError(
            f"{field} names the wrong recorded Lean semantic-target kind"
        )
    target_sha256 = leaf.semantic_payload.get("reviewed_semantic_target_sha256")
    if target_sha256 is None:
        return None
    signature_sha256 = leaf.semantic_payload.get("elaborated_signature_sha256")
    if signature_sha256 is None:
        return None
    return MappingProxyType(
        {
            "semantic_target_kind": expected_kind,
            "reviewed_semantic_target_sha256": _sha256(
                target_sha256, f"{field} reviewed semantic target"
            ),
            "elaborated_signature_sha256": _sha256(
                signature_sha256, f"{field} elaborated signature"
            ),
        }
    )


def _recorded_reviewed_target_sha256(
    current: Any,
    leaf_sha256: str,
    *,
    expected_kind: str,
    field: str,
) -> str | None:
    try:
        leaf = current.semantic_graph.leaves[leaf_sha256]
    except KeyError as exc:
        raise ObligationClosureCredentialError(
            f"{field} names a Lean leaf outside the recorded graph"
        ) from exc
    if (
        leaf.kind is not ObligationKind.LEAN_DECLARATION
        or leaf.semantic_payload.get("semantic_target_kind") != expected_kind
    ):
        raise ObligationClosureCredentialError(
            f"{field} names the wrong recorded Lean semantic-target kind"
        )
    target_sha256 = leaf.semantic_payload.get("reviewed_semantic_target_sha256")
    if target_sha256 is None:
        return None
    return _sha256(target_sha256, f"{field} reviewed semantic target")


def _recorded_claim_semantic_targets_by_specification(
    current: Any,
    preflight: ObligationStructuralPreflight,
) -> Mapping[str, str]:
    """Project the exact reviewed display digest for every selected result Spec."""

    route_set = preflight.route_set
    if route_set is None:  # ``_current_preflight`` has already failed closed.
        raise ObligationClosureCredentialError(
            "recorded graph projection has no typed result routes"
        )
    try:
        routes_by_specification = route_set.result_route_by_specification()
    except ValueError as exc:
        raise ObligationClosureCredentialError(
            "recorded graph has a nonunique result-Spec surface"
        ) from exc
    projected: dict[str, str] = {}
    for spec_declaration, route in sorted(routes_by_specification.items()):
        try:
            roles = current.paper_index.route_leaf_sha256s_by_source_item[
                route.source_item_id
            ]
        except KeyError as exc:
            raise ObligationClosureCredentialError(
                f"recorded graph omits result route {route.source_item_id}"
            ) from exc
        judgments = tuple(roles.get("source_lean_judgment", ()))
        semantic_reviews = tuple(roles.get("semantic_review", ()))
        specs = tuple(roles.get("spec", ()))
        if len(judgments) != 1 or len(semantic_reviews) != 1 or len(specs) != 1:
            raise ObligationClosureCredentialError(
                f"recorded graph has an ambiguous semantic target for result "
                f"{route.source_item_id}"
            )
        judgment = current.semantic_graph.leaves[judgments[0]]
        lean_leaf_sha256 = _sha256(
            judgment.semantic_payload.get("lean_declaration_sha256"),
            f"result {route.source_item_id} source judgment Lean leaf",
        )
        if (
            judgment.kind is not ObligationKind.SOURCE_LEAN_JUDGMENT
            or judgment.semantic_payload.get("verdict") != "matches"
            or lean_leaf_sha256 != semantic_reviews[0]
        ):
            raise ObligationClosureCredentialError(
                f"recorded graph does not bind a positive source judgment to "
                f"result {route.source_item_id}"
            )
        target_sha256 = _recorded_reviewed_target_sha256(
            current,
            lean_leaf_sha256,
            expected_kind=route.semantic_review_target_kind.value,
            field=f"result {route.source_item_id}",
        )
        if target_sha256 is not None:
            projected[spec_declaration] = target_sha256
    return MappingProxyType(projected)


def _recorded_prerequisite_semantic_targets_by_declaration(
    current: Any,
) -> Mapping[str, str]:
    """Project one location-neutral reviewed display digest per prerequisite."""

    projected: dict[str, str] = {}
    for declaration, roles in sorted(
        current.paper_index.prerequisite_leaf_sha256s_by_declaration.items()
    ):
        lean_leaves = tuple(roles.get("lean_declaration", ()))
        judgments = tuple(roles.get("source_lean_judgment", ()))
        if len(lean_leaves) != 1 or len(judgments) != 1:
            raise ObligationClosureCredentialError(
                f"recorded graph has an ambiguous prerequisite target for {declaration}"
            )
        judgment = current.semantic_graph.leaves[judgments[0]]
        judgment_lean_leaf = _sha256(
            judgment.semantic_payload.get("lean_declaration_sha256"),
            f"prerequisite {declaration} source judgment Lean leaf",
        )
        if (
            judgment.kind is not ObligationKind.SOURCE_LEAN_JUDGMENT
            or judgment.semantic_payload.get("verdict") != "matches"
            or judgment_lean_leaf != lean_leaves[0]
        ):
            raise ObligationClosureCredentialError(
                f"recorded graph does not bind a positive source judgment to "
                f"prerequisite {declaration}"
            )
        target_sha256 = _recorded_reviewed_target_sha256(
            current,
            lean_leaves[0],
            expected_kind="semantic_prerequisite",
            field=f"prerequisite {declaration}",
        )
        if target_sha256 is not None:
            projected[declaration] = target_sha256
    return MappingProxyType(projected)


def _recorded_issued_review_metadata(
    root: Path,
    paper: str,
    current: Any,
    preflight: ObligationStructuralPreflight,
) -> tuple[
    Mapping[str, Mapping[str, str]],
    Mapping[str, Mapping[str, str]],
    Mapping[str, str],
]:
    """Recover reviewer prose only from exact accepted-leaf issuances.

    The semantic graph owns verdicts and target identities.  Reasons and
    reviewer labels deliberately live outside semantic leaf identity, in the
    immutable issuance record for that leaf.  A tracked ledger row is
    therefore presentation evidence only when its complete canonical hash is
    recorded by a strict-closeout issuance attached to the corresponding
    judgment leaf in this accepted graph.  Missing, changed, or unattested
    rows are omitted rather than treated as accepted metadata.
    """

    try:
        snapshot = load_obligation_evidence_store_snapshot(
            root, paper, current.semantic_graph
        )
    except ObligationEvidenceStoreError:
        return MappingProxyType({}), MappingProxyType({}), MappingProxyType({})

    terminal_authority = _sha256(
        current.closure_leaf.semantic_payload.get("terminal_authority_sha256"),
        "recorded terminal authority",
    )
    authenticated_records = {
        (
            str(issuance.get("leaf_sha256") or "").strip().lower(),
            str(issuance.get("evidence_record_sha256") or "").strip().lower(),
        )
        for issuance in snapshot.issuances
        if (
            issuance.get("authority_sha256") == terminal_authority
            and issuance.get("assurance_contract_sha256")
            == STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
        )
    }

    def authenticated_row_for(
        row: object,
        judgment_leaf_sha256: str,
        *,
        target_sha256_field: str,
    ) -> Mapping[str, Any] | None:
        if not isinstance(row, Mapping):
            return None
        record_sha256 = hashlib.sha256(canonical_json_bytes(row)).hexdigest()
        if (judgment_leaf_sha256, record_sha256) not in authenticated_records:
            return None
        try:
            judgment_leaf = current.semantic_graph.leaves[judgment_leaf_sha256]
            lean_leaf_sha256 = _sha256(
                judgment_leaf.semantic_payload.get("lean_declaration_sha256"),
                "recorded review judgment Lean leaf",
            )
            lean_leaf = current.semantic_graph.leaves[lean_leaf_sha256]
        except KeyError:
            return None
        row_judgment = str(row.get("judgment") or "").strip().lower()
        expected_verdict = (
            "matches"
            if row_judgment in {"matches", "matches_approved_corrected_target"}
            else "does_not_match"
            if row_judgment == "mismatch"
            else row_judgment
        )
        if (
            judgment_leaf.kind is not ObligationKind.SOURCE_LEAN_JUDGMENT
            or judgment_leaf.semantic_payload.get("verdict") != expected_verdict
            or row.get("source_input_bundle_sha256")
            != judgment_leaf.semantic_payload.get("verbatim_source_bundle_sha256")
            or row.get(target_sha256_field)
            != lean_leaf.semantic_payload.get("reviewed_semantic_target_sha256")
        ):
            return None
        return row

    def metadata_for(row: Mapping[str, Any]) -> Mapping[str, str] | None:
        metadata = {
            field: str(row.get(field) or "").strip()
            for field in ("reason", "validator", "validator_type", "validated_at")
            if str(row.get(field) or "").strip()
        }
        metadata["_evidence_record_sha256"] = hashlib.sha256(
            canonical_json_bytes(row)
        ).hexdigest()
        return MappingProxyType(metadata) if metadata.get("reason") else None

    def ledger_items(name: str, *, schema: int = 1) -> Mapping[str, Any]:
        try:
            payload = _json(
                root / "papers" / paper / "audit" / name,
                f"recorded {name}",
            )
        except ObligationClosureCredentialError:
            return {}
        items = payload.get("items")
        if (
            payload.get("schema") != schema
            or payload.get("paper") != paper
            or not isinstance(items, Mapping)
        ):
            return {}
        return items

    direct_items = ledger_items("v11_raw_source_spec_screening.json", schema=3)
    source_metadata: dict[str, Mapping[str, str]] = {}
    route_set = preflight.route_set
    if route_set is not None:
        for route in route_set.result_routes():
            specification = str(route.spec_declaration)
            roles = current.paper_index.route_leaf_sha256s_by_source_item.get(
                route.source_item_id, {}
            )
            judgments = tuple(roles.get("source_lean_judgment", ()))
            row = direct_items.get(specification)
            if (
                len(judgments) != 1
                or not isinstance(row, Mapping)
                or row.get("source_item") != route.source_item_id
                or row.get("semantic_target_declaration") != specification
            ):
                continue
            authenticated_row = authenticated_row_for(
                row,
                judgments[0],
                target_sha256_field="lean_expanded_statement_sha256",
            )
            metadata = (
                metadata_for(authenticated_row)
                if authenticated_row is not None
                else None
            )
            if metadata is not None:
                source_metadata[specification] = metadata

    paper_items = ledger_items("paper_semantic_prerequisites.json")
    library_items = ledger_items("library_semantic_review.json")
    prerequisite_metadata: dict[str, Mapping[str, str]] = {}
    prerequisite_source_items: dict[str, str] = {}
    for declaration, roles in sorted(
        current.paper_index.prerequisite_leaf_sha256s_by_declaration.items()
    ):
        judgments = tuple(roles.get("source_lean_judgment", ()))
        candidates = [
            (
                paper_items.get(declaration),
                "paper_declaration",
                "paper_semantic_target_sha256",
            ),
            (
                library_items.get(declaration),
                "library_declaration",
                "library_semantic_target_sha256",
            ),
        ]
        candidates = [candidate for candidate in candidates if candidate[0] is not None]
        if len(judgments) != 1 or len(candidates) != 1:
            continue
        row, declaration_field, target_field = candidates[0]
        if not isinstance(row, Mapping) or row.get(declaration_field) != declaration:
            continue
        authenticated_row = authenticated_row_for(
            row,
            judgments[0],
            target_sha256_field=target_field,
        )
        if authenticated_row is None:
            continue
        source_item = str(authenticated_row.get("source_item") or "").strip()
        if source_item:
            prerequisite_source_items[str(declaration)] = source_item
        metadata = metadata_for(authenticated_row)
        if metadata is not None:
            prerequisite_metadata[str(declaration)] = metadata

    return (
        MappingProxyType(source_metadata),
        MappingProxyType(prerequisite_metadata),
        MappingProxyType(prerequisite_source_items),
    )


def validate_nonaccepting_recorded_graph_projection(
    root: Path,
    paper: str,
    payload: Mapping[str, Any],
) -> RecordedObligationGraphProjection:
    """Authenticate a saved graph for display without proving current closure.

    Derived status, reports, and website rendering may show the exact recorded
    closeout but are not acceptance gates. They authenticate the canonical
    schema-6 pointer, current structural review surface, complete stored graph,
    paper index, terminal hash, and historical registered issuer. They must not
    inspect source bytes, current Lean/build inputs, or launch semantic
    revalidation. The full ``validate_obligation_closure_receipt`` remains the
    only current-closure check.
    """

    preflight, _paths, _source_map = _current_preflight(root, paper)
    current = _selected_accepted_graph_from_receipt(
        root,
        paper,
        payload,
        preflight=preflight,
        authority_sha256s=_recorded_engine_authorities(root),
    )
    claim_targets = _recorded_claim_semantic_targets_by_specification(
        current, preflight
    )
    prerequisite_targets = _recorded_prerequisite_semantic_targets_by_declaration(
        current
    )
    (
        source_review_metadata,
        prerequisite_review_metadata,
        prerequisite_source_items,
    ) = (
        _recorded_issued_review_metadata(root, paper, current, preflight)
    )
    route_set = preflight.route_set
    if route_set is None:  # ``_current_preflight`` has already failed closed.
        raise ObligationClosureCredentialError(
            "recorded graph projection has no typed review surface"
        )
    return RecordedObligationGraphProjection(
        graph_sha256=current.graph_sha256,
        review_declarations_by_source_item=(
            _recorded_review_declarations_by_source_item(preflight)
        ),
        card_review_declarations_by_source_item=(
            _recorded_card_review_declarations_by_source_item(
                current,
                preflight,
                authenticated_prerequisite_source_items_by_declaration=(
                    prerequisite_source_items
                ),
            )
        ),
        source_lean_verdicts_by_source_item=(
            _recorded_source_lean_verdicts_by_source_item(current, preflight)
        ),
        source_input_bundle_sha256s_by_source_item=(
            _recorded_source_input_bundles_by_source_item(
                current,
                preflight,
                authenticated_prerequisite_source_items_by_declaration=(
                    prerequisite_source_items
                ),
            )
        ),
        claim_semantic_target_sha256s_by_specification=claim_targets,
        prerequisite_semantic_target_sha256s_by_declaration=prerequisite_targets,
        reviewed_display_surface_complete=(
            set(claim_targets) == set(route_set.result_specifications())
            and set(prerequisite_targets)
            == set(current.paper_index.prerequisite_leaf_sha256s_by_declaration)
        ),
        source_review_metadata_by_specification=source_review_metadata,
        prerequisite_review_metadata_by_declaration=prerequisite_review_metadata,
    )


def _accepted_graph_direct_target_identities(
    current: Any,
    preflight: ObligationStructuralPreflight,
) -> Mapping[str, Mapping[str, str]]:
    route_set = preflight.route_set
    if route_set is None:
        raise ObligationClosureCredentialError(
            "accepted semantic-review inputs have no typed result routes"
        )
    recorded_targets = _recorded_claim_semantic_targets_by_specification(
        current, preflight
    )
    identities: dict[str, Mapping[str, str]] = {}
    for route in route_set.result_routes():
        roles = current.paper_index.route_leaf_sha256s_by_source_item.get(
            route.source_item_id, {}
        )
        semantic_reviews = tuple(roles.get("semantic_review", ()))
        if len(semantic_reviews) != 1:
            raise ObligationClosureCredentialError(
                "accepted graph has an ambiguous reviewed target for result "
                + route.source_item_id
            )
        identity = _recorded_reviewed_target_identity(
            current,
            semantic_reviews[0],
            expected_kind=route.semantic_review_target_kind.value,
            field=f"result {route.source_item_id}",
        )
        if identity is None:
            raise ObligationClosureCredentialError(
                "accepted graph lacks modern reviewed target identities for result "
                + route.source_item_id
            )
        if identity["reviewed_semantic_target_sha256"] != recorded_targets.get(
            route.spec_declaration
        ):
            raise ObligationClosureCredentialError(
                "accepted graph reviewed target disagrees for result "
                + route.source_item_id
            )
        identities[route.spec_declaration] = identity
    if set(identities) != set(route_set.result_specifications()):
        raise ObligationClosureCredentialError(
            "accepted graph does not contain every selected result target"
        )
    return MappingProxyType(identities)


def _accepted_graph_prerequisite_target_identities(
    current: Any,
) -> Mapping[str, Mapping[str, str]]:
    recorded_targets = _recorded_prerequisite_semantic_targets_by_declaration(
        current
    )
    identities: dict[str, Mapping[str, str]] = {}
    for declaration, roles in sorted(
        current.paper_index.prerequisite_leaf_sha256s_by_declaration.items()
    ):
        lean_leaves = tuple(roles.get("lean_declaration", ()))
        if len(lean_leaves) != 1:
            raise ObligationClosureCredentialError(
                "accepted graph has an ambiguous reviewed target for prerequisite "
                + declaration
            )
        identity = _recorded_reviewed_target_identity(
            current,
            lean_leaves[0],
            expected_kind="semantic_prerequisite",
            field=f"prerequisite {declaration}",
        )
        if identity is None:
            raise ObligationClosureCredentialError(
                "accepted graph lacks modern reviewed target identities for "
                f"prerequisite {declaration}"
            )
        if identity["reviewed_semantic_target_sha256"] != recorded_targets.get(
            declaration
        ):
            raise ObligationClosureCredentialError(
                "accepted graph reviewed target disagrees for prerequisite "
                + declaration
            )
        identities[declaration] = identity
    if set(identities) != set(
        current.paper_index.prerequisite_leaf_sha256s_by_declaration
    ):
        raise ObligationClosureCredentialError(
            "accepted graph does not contain every selected prerequisite target"
        )
    return MappingProxyType(identities)


def _exact_json_input(path: Path, label: str) -> tuple[Mapping[str, Any], bytes]:
    try:
        raw = path.read_bytes()
        value = json.loads(raw)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        raise ObligationClosureCredentialError(f"{label} is unreadable: {exc}") from exc
    if not isinstance(value, Mapping):
        raise ObligationClosureCredentialError(f"{label} is not an object")
    return value, raw


def authenticated_current_accepted_graph_semantic_review_inputs(
    root: Path,
    paper: str,
) -> AuthenticatedAcceptedGraphSemanticReviewInputs:
    """Return all-selected semantic inputs from one exact accepted graph.

    This document-only reader does not run Lean and cannot recover a stale
    import closure.  It accepts only the current source, route, Lean/import,
    build-content, target, judgment, and strict-issuance identities already
    authenticated by the selected graph.
    """

    root = root.resolve()
    controls = _prepare_accepted_graph_controls(
        root,
        paper,
        allow_lean_semantic_recovery=False,
    )
    current = controls.loaded
    preflight, _preflight_paths, source_map = _current_preflight(root, paper)
    if preflight != controls.preflight:
        raise ObligationClosureCredentialError(
            "paper structural preflight changed during accepted semantic review"
        )

    paper_dir = root / "papers" / paper
    ledger_paths = {
        "direct": paper_dir / "audit" / "v11_raw_source_spec_screening.json",
        "paper": paper_dir / "audit" / "paper_semantic_prerequisites.json",
        "library": paper_dir / "audit" / "library_semantic_review.json",
    }
    ledgers: dict[str, Mapping[str, Any]] = {}
    exact_bytes: dict[Path, bytes] = {}
    for role, path in ledger_paths.items():
        ledger, raw = _exact_json_input(path, f"current {role} semantic-review ledger")
        ledgers[role] = ledger
        exact_bytes[path] = raw
    pointer_path = current_accepted_graph_path(root, paper)
    pointer, pointer_raw = _exact_json_input(
        pointer_path, "current accepted obligation graph pointer"
    )
    if pointer.get("graph_sha256") != current.graph_sha256:
        raise ObligationClosureCredentialError(
            "selected accepted graph changed during semantic-review projection"
        )
    exact_bytes[pointer_path] = pointer_raw

    direct_items = ledgers["direct"].get("items")
    paper_items = ledgers["paper"].get("items")
    library_items = ledgers["library"].get("items")
    if not all(isinstance(items, Mapping) for items in (
        direct_items,
        paper_items,
        library_items,
    )):
        raise ObligationClosureCredentialError(
            "current semantic-review ledger has no item map"
        )
    assert isinstance(direct_items, Mapping)
    assert isinstance(paper_items, Mapping)
    assert isinstance(library_items, Mapping)

    route_set = preflight.route_set
    if route_set is None:
        raise ObligationClosureCredentialError(
            "accepted semantic-review inputs have no typed review surface"
        )
    expected_direct = set(route_set.result_specifications())
    expected_prerequisites = set(
        current.paper_index.prerequisite_leaf_sha256s_by_declaration
    )
    if set(direct_items) != expected_direct:
        raise ObligationClosureCredentialError(
            "current direct-review rows differ from the accepted result surface"
        )
    if set(paper_items) & set(library_items):
        raise ObligationClosureCredentialError(
            "paper and library semantic-review ledgers overlap"
        )
    if set(paper_items) | set(library_items) != expected_prerequisites:
        raise ObligationClosureCredentialError(
            "current prerequisite rows differ from the accepted prerequisite surface"
        )

    source_metadata, prerequisite_metadata, _source_items = (
        _recorded_issued_review_metadata(root, paper, current, preflight)
    )
    if set(source_metadata) != expected_direct:
        raise ObligationClosureCredentialError(
            "accepted graph does not authenticate every current direct-review row"
        )
    if set(prerequisite_metadata) != expected_prerequisites:
        raise ObligationClosureCredentialError(
            "accepted graph does not authenticate every current prerequisite row"
        )
    for name, row in direct_items.items():
        if not isinstance(row, Mapping) or hashlib.sha256(
            canonical_json_bytes(row)
        ).hexdigest() != source_metadata[name].get("_evidence_record_sha256"):
            raise ObligationClosureCredentialError(
                f"accepted graph does not authenticate direct-review row {name}"
            )
    for name, row in {**dict(paper_items), **dict(library_items)}.items():
        if not isinstance(row, Mapping) or hashlib.sha256(
            canonical_json_bytes(row)
        ).hexdigest() != prerequisite_metadata[name].get(
            "_evidence_record_sha256"
        ):
            raise ObligationClosureCredentialError(
                f"accepted graph does not authenticate prerequisite row {name}"
            )

    direct_targets = _accepted_graph_direct_target_identities(current, preflight)
    prerequisite_targets = _accepted_graph_prerequisite_target_identities(current)
    result = AuthenticatedAcceptedGraphSemanticReviewInputs(
        graph_sha256=current.graph_sha256,
        source_map=freeze_json(dict(source_map)),
        direct_review_ledger=freeze_json(dict(ledgers["direct"])),
        paper_prerequisite_ledger=freeze_json(dict(ledgers["paper"])),
        library_prerequisite_ledger=freeze_json(dict(ledgers["library"])),
        direct_target_identities_by_specification=freeze_json(
            {name: dict(identity) for name, identity in direct_targets.items()}
        ),
        prerequisite_target_identities_by_declaration=freeze_json(
            {
                name: dict(identity)
                for name, identity in prerequisite_targets.items()
            }
        ),
    )
    _finalize_controls(controls)
    try:
        inputs_unchanged = all(
            path.read_bytes() == raw for path, raw in exact_bytes.items()
        )
    except OSError as exc:
        raise ObligationClosureCredentialError(
            "accepted semantic-review inputs became unreadable"
        ) from exc
    if not inputs_unchanged:
        raise ObligationClosureCredentialError(
            "accepted semantic-review inputs changed during validation"
        )
    return result


def _retain_current_pass_lean_import_closure(
    root: Path,
    paper: str,
    loaded: LoadedPaperObligationBundle,
    current_closeout_pass: object,
) -> Path:
    """Persist the frozen transaction closure before selecting its graph."""

    projection = current_closeout_pass.lean_closure_projection()
    raw_closure = (
        projection.get("lean_import_closure")
        if isinstance(projection, Mapping)
        else None
    )
    try:
        closure = validated_lean_import_closure_payload(raw_closure)
    except ValueError as exc:
        raise ObligationClosureCredentialError(
            "current closeout pass has no valid Lean import closure: " + str(exc)
        ) from exc
    build_ids = loaded.paper_index.leaf_sha256s_by_kind.get(
        ObligationKind.BUILD, ()
    )
    if len(build_ids) != 1 or build_ids[0] not in loaded.graph.leaves:
        raise ObligationClosureCredentialError(
            "current obligation bundle has no unique build leaf"
        )
    selected_digest = _sha256(
        loaded.graph.leaves[build_ids[0]].semantic_payload.get(
            "lean_import_closure_sha256"
        ),
        "build leaf Lean import closure",
    )
    if lean_import_closure_payload_sha256(closure) != selected_digest:
        raise ObligationClosureCredentialError(
            "current closeout pass Lean import closure disagrees with the build leaf"
        )
    provider = current_closeout_pass.build_input_provider
    owns_exact = getattr(provider, "owns_exact_lean_import_closure_payload", None)
    if not callable(owns_exact) or not owns_exact(closure):
        raise ObligationClosureCredentialError(
            "current closeout provider does not own the selected Lean import closure"
        )
    try:
        return store_lean_import_closure_preimage(
            root,
            paper,
            selected_digest,
            closure,
        )
    except ObligationEvidenceStoreError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc


def publish_current_obligation_bundle_as_accepted_graph(
    root: Path,
    paper: str,
    *,
    current_closeout_pass: object,
) -> Path:
    """Publish only from the exact in-process current-closeout capability.

    A portable strict authority remains embedded in the accepted graph so a
    later checkout can validate its historical issuance.  That projection is
    no longer an input credential: traces, stage receipts, and hand-built
    authority values cannot invoke this publication boundary.
    """

    root = root.resolve()
    try:
        accepted_pass = validate_current_closeout_pass(current_closeout_pass)
        authority = validate_strict_closeout_authority(
            current_closeout_pass_authority(accepted_pass)
        )
    except (StrictCloseoutAuthorityError, ValueError) as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    if (
        accepted_pass.repository_root != root
        or accepted_pass.paper != paper
        or authority.paper != paper
    ):
        raise ObligationClosureCredentialError(
            "current closeout pass belongs to another repository or paper"
        )
    final_holistic_audit_surface = accepted_pass.final_holistic_surface()
    build_input_provider = accepted_pass.build_input_provider
    if (
        not final_holistic_audit_surface_contract_is_supported(
            final_holistic_audit_surface
        )
        or final_holistic_audit_surface.get("paper") != paper
    ):
        raise ObligationClosureCredentialError(
            "final holistic audit surface is malformed or belongs to another paper"
        )
    final_surface_sha256 = final_holistic_audit_surface_sha256(
        final_holistic_audit_surface
    )
    source_assurance_sha256 = final_holistic_source_assurance_v2_sha256(
        final_holistic_audit_surface
    )
    with _terminal_selection_lock(root, paper):
        try:
            loaded = load_paper_obligation_bundle(root, paper)
        except ObligationEvidenceStoreError as exc:
            raise ObligationClosureCredentialError(str(exc)) from exc
        controls = _prepare_current_controls(
            root,
            paper,
            loaded,
            authenticated_leaf_authority_sha256s=(authority.authority_sha256,),
            build_input_provider=build_input_provider,
        )
        _retain_current_pass_lean_import_closure(
            root,
            paper,
            loaded,
            accepted_pass,
        )
        store_accepted_obligation_graph(
            root,
            paper,
            loaded.paper_index,
            loaded.graph,
            preflight=controls.preflight,
            strict_closeout_authority=authority,
            final_holistic_audit_surface_sha256=final_surface_sha256,
            source_assurance_sha256=source_assurance_sha256,
        )
        accepted = load_accepted_obligation_graph(
            root,
            paper,
            preflight=controls.preflight,
            authenticated_authority_sha256s=controls.authority_sha256s,
        )
        payload = _accepted_graph_receipt_payload(root, paper, accepted.graph_sha256)
        receipt_path = root / "papers" / paper / "FINAL_CLOSURE_RECEIPT.md"
        _atomic_write(
            receipt_path,
            render_obligation_closure_receipt(payload).encode("utf-8"),
        )
        if receipt_path.read_text(encoding="utf-8") != (
            render_obligation_closure_receipt(payload)
        ):
            raise ObligationClosureCredentialError(
                "schema-6 receipt did not round-trip after publication"
            )
        _selected_accepted_graph_from_receipt(
            root,
            paper,
            payload,
            preflight=controls.preflight,
            authority_sha256s=controls.authority_sha256s,
        )
        _finalize_controls(controls)
        return receipt_path


def migrate_accepted_terminal_source_assurance_v1_to_v2(
    root: Path,
    paper: str,
) -> Path:
    """Replace only a validated v1 terminal root with v2 assurance.

    This migration cannot issue or alter semantic evidence.  It requires the
    selected accepted graph's v1 assurance to match the exact current v1
    builder, requires the accepted Lean import closure to remain exact so no
    semantic recovery can run, and reuses the same semantic graph, paper index,
    strict authority, and frozen final-audit identity.
    """

    root = root.resolve()
    with _terminal_selection_lock(root, paper):
        return _migrate_accepted_terminal_source_assurance_v1_to_v2_under_lock(
            root,
            paper,
        )


def _migrate_accepted_terminal_source_assurance_v1_to_v2_under_lock(
    root: Path,
    paper: str,
) -> Path:
    """Run the v1-to-v2 replacement while terminal selection is locked."""

    controls = _prepare_accepted_graph_controls(
        root,
        paper,
        allow_lean_semantic_recovery=False,
    )
    preflight, _preflight_paths, source_map = _current_preflight(root, paper)
    if controls.preflight != preflight:
        raise ObligationClosureCredentialError(
            "paper structural preflight changed during terminal migration"
        )
    loaded = controls.loaded
    if (
        loaded.closure_leaf.contract_sha256
        != STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
    ):
        raise ObligationClosureCredentialError(
            "terminal source-assurance migration requires a strict accepted graph"
        )
    closure_payload = loaded.closure_leaf.semantic_payload
    try:
        reviewed_source_item_ids = current_reviewed_source_item_ids(
            loaded.paper_index,
            loaded.graph,
            preflight,
            source_map=source_map,
        )
        current_v1 = build_current_final_holistic_source_assurance_projection(
            root,
            paper=paper,
            reviewed_source_item_ids=reviewed_source_item_ids,
        )
        current_v1_sha256 = final_holistic_source_assurance_projection_sha256(
            current_v1
        )
    except (FinalHolisticAuditSurfaceError, PaperObligationIndexError) as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    if closure_payload.get("source_assurance_sha256") != current_v1_sha256:
        raise ObligationClosureCredentialError(
            "terminal source-assurance migration requires an exact current v1 digest"
        )

    if controls.terminal_validation_route != "exact_import_closure":
        raise ObligationClosureCredentialError(
            "terminal source-assurance migration cannot use Lean semantic recovery"
        )
    try:
        authority = recorded_strict_closeout_authority(
            closure_payload.get("strict_closeout_authority")
        )
        current_v2 = final_holistic_source_assurance_v2_projection(current_v1)
        current_v2_sha256 = (
            final_holistic_source_assurance_v2_projection_sha256(current_v2)
        )
    except (StrictCloseoutAuthorityError, FinalHolisticAuditSurfaceError) as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc
    frozen_final_audit_sha256 = _sha256(
        closure_payload.get("final_holistic_audit_surface_sha256"),
        "frozen final holistic audit surface",
    )
    old_semantic_leaf_sha256s = frozenset(loaded.graph.leaves)
    try:
        candidate = build_accepted_obligation_graph(
            loaded.graph,
            loaded.paper_index,
            preflight=controls.preflight,
            strict_closeout_authority=authority,
            final_holistic_audit_surface_sha256=frozen_final_audit_sha256,
            source_assurance_sha256=current_v2_sha256,
        )
    except AcceptedObligationGraphError as exc:
        raise ObligationClosureCredentialError(str(exc)) from exc

    pointer_path = current_accepted_graph_path(root, paper)
    receipt_path = root / "papers" / paper / "FINAL_CLOSURE_RECEIPT.md"
    old_pointer_bytes = _optional_file_bytes(pointer_path)
    old_receipt_bytes = _optional_file_bytes(receipt_path)
    if old_pointer_bytes is None:
        raise ObligationClosureCredentialError(
            "terminal source-assurance migration has no selected v1 pointer"
        )
    try:
        old_pointer = json.loads(old_pointer_bytes)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ObligationClosureCredentialError(
            "terminal source-assurance migration v1 pointer is unreadable"
        ) from exc
    if (
        not isinstance(old_pointer, Mapping)
        or old_pointer.get("graph_sha256") != loaded.graph_sha256
    ):
        raise ObligationClosureCredentialError(
            "selected accepted graph changed during terminal migration"
        )

    new_pointer_bytes = canonical_json_bytes(
        {
            "schema": PACKED_ACCEPTED_GRAPH_POINTER_SCHEMA,
            "graph_sha256": candidate.graph_sha256,
        }
    ) + b"\n"
    payload = _accepted_graph_receipt_payload(
        root,
        paper,
        candidate.graph_sha256,
    )
    new_receipt_bytes = render_obligation_closure_receipt(payload).encode("utf-8")

    # Check the full watched surface immediately before the first selection
    # write.  A second check below is protected by compare-and-restore.
    _finalize_controls(controls)
    if (
        _optional_file_bytes(pointer_path) != old_pointer_bytes
        or _optional_file_bytes(receipt_path) != old_receipt_bytes
    ):
        raise ObligationClosureCredentialError(
            "terminal selection changed before source-assurance migration"
        )
    try:
        stored_pointer_path = store_accepted_obligation_graph(
            root,
            paper,
            loaded.paper_index,
            loaded.graph,
            preflight=controls.preflight,
            strict_closeout_authority=authority,
            final_holistic_audit_surface_sha256=frozen_final_audit_sha256,
            source_assurance_sha256=current_v2_sha256,
        )
        if stored_pointer_path != pointer_path:
            raise ObligationClosureCredentialError(
                "terminal source-assurance migration selected a noncanonical pointer"
            )
        migrated = load_accepted_obligation_graph(
            root,
            paper,
            preflight=controls.preflight,
            authenticated_authority_sha256s=controls.authority_sha256s,
            require_current_aggregate_identity=False,
        )
        if (
            migrated.graph_sha256 != candidate.graph_sha256
            or frozenset(migrated.graph.leaves) != old_semantic_leaf_sha256s
            or migrated.graph.graph_sha256 != loaded.graph.graph_sha256
            or migrated.paper_index.index_sha256
            != loaded.paper_index.index_sha256
            or migrated.closure_leaf.semantic_payload.get(
                "final_holistic_audit_surface_sha256"
            )
            != frozen_final_audit_sha256
            or migrated.closure_leaf.semantic_payload.get(
                "source_assurance_sha256"
            )
            != current_v2_sha256
            or migrated.closure_leaf.semantic_payload.get(
                "strict_closeout_authority"
            )
            != authority.projection()
        ):
            raise ObligationClosureCredentialError(
                "terminal source-assurance migration changed frozen semantic inputs"
            )
        _atomic_write(receipt_path, new_receipt_bytes)
        if receipt_path.read_bytes() != new_receipt_bytes:
            raise ObligationClosureCredentialError(
                "schema-6 receipt did not round-trip after terminal migration"
            )
        _selected_accepted_graph_from_receipt(
            root,
            paper,
            payload,
            preflight=controls.preflight,
            authority_sha256s=controls.authority_sha256s,
        )
        _finalize_controls(controls)
    except Exception as exc:
        try:
            _restore_terminal_migration_selection(
                pointer_path=pointer_path,
                receipt_path=receipt_path,
                old_pointer_bytes=old_pointer_bytes,
                old_receipt_bytes=old_receipt_bytes,
                new_pointer_bytes=new_pointer_bytes,
                new_receipt_bytes=new_receipt_bytes,
            )
        except ObligationClosureCredentialError as rollback_exc:
            raise ObligationClosureCredentialError(
                "terminal source-assurance migration failed and could not "
                "safely restore the prior selection: " + str(rollback_exc)
            ) from exc
        raise
    return receipt_path


def promote_current_obligation_bundle_to_acceptance(
    root: Path,
    paper: str,
    *,
    authenticated_predecessor_sha256: str,
) -> Path:
    """Reject legacy promotion into the stronger current acceptance contract.

    Historical receipts remain valid under their recorded schema.  A new
    strict-semantic accepted graph is issued only by a current strict closeout,
    never by manufacturing a version-pair bridge from an older receipt.
    """

    del root, paper
    _sha256(authenticated_predecessor_sha256, "authenticated predecessor acceptance")
    raise ObligationClosureCredentialError(
        "historical closure remains valid under its recorded schema; run the current "
        "strict closeout to issue a strict-semantic accepted graph"
    )
