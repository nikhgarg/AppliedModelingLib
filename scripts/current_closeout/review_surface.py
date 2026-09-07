"""Immutable review surfaces projected from one current Lean graph.

Lean graph acquisition and validation live in :mod:`lean_review_graph`.  This
module performs the remaining non-judgmental projection: it freezes the graph
targets, joins the two already selected prerequisite ledgers for the accepting
transaction, and exposes a narrower writer projection for standalone review
commands.  It does not issue verdicts or grant closeout acceptance.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass, field as dataclass_field
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, Protocol

if TYPE_CHECKING:
    from scripts.obligation_closure_credential import RecordedObligationGraphProjection

import hashlib
import json
import re
from typing import Callable

from scripts import semantic_review_decision_queue as review_queue
from scripts.corrected_target_identity import (
    corrected_target_review_digest,
    corrected_target_screening_binding_is_current,
    source_requires_approved_corrected_target,
)
from scripts.current_closeout import lean_review_graph
from scripts.dashboard_audit_inputs import _dashboard_is_file, _dashboard_json_payload
from scripts.evidence_run_context import run_scoped_cached_value
from scripts.final_closure_receipt import (
    ACCEPTED_GRAPH_RECEIPT_SCHEMA,
    LEGACY_RECEIPT_SCHEMAS,
    OBLIGATION_RECEIPT_SCHEMA,
    FinalClosureReceiptError,
    load_final_closure_receipt,
)
from scripts.immutable_json import freeze_json
from scripts.obligation_routes import (
    EvidenceRouteSet,
    ObligationRouteError,
    SemanticReviewTargetKind,
)
from scripts.portable_evidence_identity import canonical_json_bytes
from scripts.source_review_input import validated_approved_review_contexts
from scripts.report_context_presentation import (
    report_context_presentation,
    row_context_presentation,
)
from scripts.semantic_prerequisite_projection import (
    LIBRARY_SEMANTIC_REVIEW_SCHEMA,
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
    V11_DEFINITION_TARGET_PROTOCOL,
    V11_LEAN_TARGET_PROTOCOL,
    lean_graph_library_declaration_sources,
    project_library_semantic_prerequisites,
    project_paper_semantic_prerequisites,
    selected_library_semantic_prerequisite_targets,
    selected_paper_semantic_prerequisite_targets,
    source_map_items_by_key,
)
from scripts.semantic_reuse_authority import CurrentSemanticReuseAuthority
from scripts.source_coverage_scope import (
    explicit_raw_source_spec_screening_requested,
    source_item_effective_route_policy,
)
from scripts.source_display_projection import (
    _project_public_library_source_excerpts,
    source_anchor_display_state,
)
from scripts.source_review_input import (
    normalize_statement,
    source_semantic_input_bundle,
    statement_digest,
)


def _paper_prerequisite_support(
    review_targets: Mapping[str, Any],
    roots: Iterable[str],
) -> tuple[
    dict[str, dict[str, Any]],
    dict[str, tuple[str, ...]],
    dict[str, str],
]:
    """Project per-row transitive support from Lean-owned dependency edges."""

    support, names_by_root = review_queue.review_support_from_targets(
        review_targets,
        root_declarations=roots,
    )
    digests = (
        {
            root: (
                review_queue.selected_supporting_declarations_sha256(
                    support,
                    names,
                )
                or ""
            )
            for root, names in names_by_root.items()
        }
        if support
        else {root: "" for root in names_by_root}
    )
    return support, names_by_root, digests


class V11ReviewSurfaceContextView(
    lean_review_graph.V11GraphAcquisitionContextView,
    Protocol,
):
    """Frozen transaction interface required by graph-derived review rows."""

    folder: Path
    statement_map: Mapping[str, Any] | None

    def record_v11_graph_carrier_reuse(self, *, carrier_reused: bool) -> None: ...

    def retain_v11_review_surface(self, surface: object) -> None: ...


@dataclass(frozen=True)
class V11LeanReviewSurface:
    """One exact Lean-owned input shared by all current semantic gates."""

    semantic_targets: Mapping[str, Mapping[str, Any]]
    paper_prerequisites: tuple[Mapping[str, Any], ...]
    library_prerequisites: tuple[Mapping[str, Any], ...]
    source_declarations: Mapping[str, Mapping[str, Any]]
    library_source_declarations: Mapping[str, Mapping[str, Any]]
    semantic_contracts: Mapping[tuple[str, str, str], Mapping[str, Any]]
    declaration_inventory: Mapping[str, Any]
    module_sources: Mapping[str, tuple[Path, bytes]]
    build_input_provider: object
    graph_request: Mapping[str, Any] = dataclass_field(default_factory=dict)
    review_claim_manifests: Mapping[str, Mapping[str, Any]] = dataclass_field(
        default_factory=dict
    )
    paper_semantic_targets: Mapping[str, Mapping[str, Any]] = dataclass_field(
        default_factory=dict
    )
    library_semantic_targets: Mapping[str, Mapping[str, Any]] = dataclass_field(
        default_factory=dict
    )
    paper_declaration_sources: Mapping[str, Mapping[str, Any]] = dataclass_field(
        default_factory=dict
    )
    library_declaration_sources: Mapping[str, Mapping[str, Any]] = dataclass_field(
        default_factory=dict
    )
    carrier_reused: bool = False


@dataclass(frozen=True)
class CurrentV11ReviewGraphProjection:
    """Exact non-evidentiary reviewer targets from one saved Lean graph."""

    context: V11ReviewSurfaceContextView
    specifications: tuple[str, ...]
    semantic_targets: Mapping[str, Mapping[str, Any]]
    paper_prerequisite_targets: Mapping[str, Mapping[str, Any]]
    library_semantic_targets: Mapping[str, Mapping[str, Any]]
    library_semantic_target_errors: Mapping[str, str]
    paper_declaration_sources: Mapping[str, Mapping[str, Any]] = dataclass_field(
        default_factory=dict
    )
    library_declaration_sources: Mapping[str, Mapping[str, Any]] = dataclass_field(
        default_factory=dict
    )
    repository_root: Path | None = None
    carrier_reused: bool = False

    def _validated_paper_dir(self, paper_dir: Path) -> Path:
        resolved = paper_dir.resolve()
        if resolved != self.context.folder:
            raise ValueError(
                "current v11 review transaction belongs to a different paper"
            )
        return resolved

    def _repository_root(self, paper_dir: Path) -> Path:
        if self.repository_root is not None:
            return self.repository_root.resolve()
        resolved = paper_dir.resolve()
        if len(resolved.parents) < 2 or resolved.parent.name != "papers":
            raise ValueError("current v11 review paper is outside a papers root")
        return resolved.parents[1]

    def project_paper_prerequisites(
        self,
        paper_dir: Path,
        *,
        ledger: Mapping[str, Any],
    ) -> tuple[Mapping[str, Any], ...]:
        """Project paper-local review rows from this exact graph transaction."""

        resolved = self._validated_paper_dir(paper_dir)
        selected_targets = selected_paper_semantic_prerequisite_targets(
            self.context.statement_map,
            self.paper_prerequisite_targets,
        )
        _support, _names_by_root, support_digests = _paper_prerequisite_support(
            self.target_material(),
            selected_targets,
        )
        return tuple(
            project_paper_semantic_prerequisites(
                resolved,
                claim_semantic_targets=self.semantic_targets,
                prerequisite_semantic_targets=selected_targets,
                semantic_target_errors={},
                declaration_sources=self.paper_declaration_sources,
                source_map=self.context.statement_map,
                ledger=ledger,
                repository_root=self._repository_root(resolved),
                file_bytes_override=self.context.file_bytes_override(),
                supporting_declarations_sha256_by_name=support_digests,
            )
        )

    def paper_prerequisite_review_support(
        self,
        roots: Iterable[str],
    ) -> tuple[
        dict[str, dict[str, Any]],
        dict[str, tuple[str, ...]],
        dict[str, str],
    ]:
        """Return exact queue support and row identities for selected roots."""

        return _paper_prerequisite_support(self.target_material(), roots)

    def project_library_prerequisites(
        self,
        paper_dir: Path,
        *,
        ledger: Mapping[str, Any],
    ) -> tuple[Mapping[str, Any], ...]:
        """Project reusable review rows from this exact graph transaction."""

        resolved = self._validated_paper_dir(paper_dir)
        return tuple(
            project_library_semantic_prerequisites(
                resolved,
                semantic_targets=self.library_semantic_targets,
                semantic_target_errors=self.library_semantic_target_errors,
                declaration_sources=self.library_declaration_sources,
                source_map=self.context.statement_map,
                ledger=ledger,
                repository_root=self._repository_root(resolved),
                file_bytes_override=self.context.file_bytes_override(),
            )
        )

    def target_material(self) -> Mapping[str, object]:
        """Return the common graph-native input expected by review writers."""

        return MappingProxyType(
            {
                "specifications": list(self.specifications),
                "semantic_targets": self.semantic_targets,
                "paper_prerequisite_targets": self.paper_prerequisite_targets,
                "library_semantic_targets": self.library_semantic_targets,
                "library_semantic_target_errors": (
                    self.library_semantic_target_errors
                ),
                "paper_declaration_sources": self.paper_declaration_sources,
                "library_declaration_sources": self.library_declaration_sources,
            }
        )


def build_v11_review_surface_material(
    repository_root: Path,
    folder: Path,
    expected_specifications: Iterable[str],
    *,
    context: V11ReviewSurfaceContextView,
    checkpoint_projection_only: bool = False,
    require_graph_checkpoint: bool = False,
) -> V11LeanReviewSurface | CurrentV11ReviewGraphProjection:
    """Project one immutable review surface from the validated current graph."""

    root = repository_root.resolve()
    paper_folder = folder.resolve()
    try:
        material = lean_review_graph.build_v11_lean_review_graph_material(
            root,
            paper_folder,
            expected_specifications,
            context=context,
            checkpoint_projection_only=(
                checkpoint_projection_only or require_graph_checkpoint
            ),
        )
        projection = material.acquisition.projection
        semantic_targets = projection.semantic_targets
        paper_targets = projection.paper_semantic_targets
        library_targets = projection.library_semantic_targets
        paper_sources = projection.paper_declaration_sources
        library_sources = projection.library_declaration_sources

        if checkpoint_projection_only:
            return CurrentV11ReviewGraphProjection(
                context=context,
                specifications=material.request_plan.specifications,
                semantic_targets=freeze_json(dict(semantic_targets)),
                paper_prerequisite_targets=freeze_json(dict(paper_targets)),
                library_semantic_targets=freeze_json(dict(library_targets)),
                library_semantic_target_errors=MappingProxyType({}),
                paper_declaration_sources=freeze_json(dict(paper_sources)),
                library_declaration_sources=freeze_json(dict(library_sources)),
                repository_root=root,
                carrier_reused=material.carrier_reused,
            )

        source_map = context.statement_map
        if not isinstance(source_map, Mapping):
            raise TypeError("v11 Lean review graph lacks its exact source map")
        frozen_input_bytes = context.file_bytes_override()
        paper_ledger = context.json_payload(
            context.canonical_sidecar_path("paper_semantic_prerequisites.json")
        ) or {}
        library_ledger = context.json_payload(
            context.canonical_sidecar_path("library_semantic_review.json")
        ) or {}
        _support, _names_by_root, paper_support_digests = (
            _paper_prerequisite_support(
                {
                    "semantic_targets": semantic_targets,
                    "paper_prerequisite_targets": paper_targets,
                    "library_semantic_targets": library_targets,
                    "library_semantic_target_errors": {},
                    "paper_declaration_sources": paper_sources,
                    "library_declaration_sources": library_sources,
                },
                paper_targets,
            )
        )
        paper_prerequisites = project_paper_semantic_prerequisites(
            paper_folder,
            claim_semantic_targets=semantic_targets,
            prerequisite_semantic_targets=paper_targets,
            semantic_target_errors={},
            declaration_sources=paper_sources,
            source_map=source_map,
            ledger=paper_ledger,
            repository_root=root,
            file_bytes_override=frozen_input_bytes,
            supporting_declarations_sha256_by_name=paper_support_digests,
        )
        library_prerequisites = project_library_semantic_prerequisites(
            paper_folder,
            semantic_targets=library_targets,
            semantic_target_errors={},
            declaration_sources=library_sources,
            source_map=source_map,
            ledger=library_ledger,
            repository_root=root,
            file_bytes_override=frozen_input_bytes,
        )
    except (OSError, RuntimeError, TypeError) as exc:
        raise ValueError(str(exc)) from exc

    frozen_contracts = MappingProxyType(
        {
            key: freeze_json(dict(value))
            for key, value in sorted(projection.semantic_contracts.items())
        }
    )
    frozen_prerequisites = freeze_json(list(paper_prerequisites))
    frozen_library_prerequisites = freeze_json(list(library_prerequisites))
    if not isinstance(frozen_prerequisites, list) or not isinstance(
        frozen_library_prerequisites, list
    ):
        raise TypeError("v11 prerequisite projection is not a JSON list")
    provider = material.build_input_provider
    if provider is None and not require_graph_checkpoint:
        raise ValueError("accepting v11 Lean review graph has no build provider")
    return V11LeanReviewSurface(
        semantic_targets=freeze_json(dict(semantic_targets)),
        paper_prerequisites=tuple(frozen_prerequisites),
        library_prerequisites=tuple(frozen_library_prerequisites),
        source_declarations=freeze_json(dict(projection.source_declarations)),
        library_source_declarations=freeze_json(
            dict(projection.library_source_declarations)
        ),
        semantic_contracts=frozen_contracts,
        declaration_inventory=freeze_json(dict(material.acquisition.inventory)),
        module_sources=MappingProxyType(dict(material.module_sources)),
        build_input_provider=provider,
        graph_request=freeze_json(dict(material.graph_request)),
        review_claim_manifests=freeze_json(
            dict(projection.review_claim_manifests)
        ),
        paper_semantic_targets=freeze_json(dict(paper_targets)),
        library_semantic_targets=freeze_json(dict(library_targets)),
        paper_declaration_sources=freeze_json(dict(paper_sources)),
        library_declaration_sources=freeze_json(dict(library_sources)),
        carrier_reused=material.carrier_reused,
    )


def read_diagnostic_v11_review_surface(
    repository_root: Path,
    folder: Path,
    expected_specifications: Iterable[str],
    *,
    context: V11ReviewSurfaceContextView,
) -> V11LeanReviewSurface:
    """Read retained inputs only; never prepare a missing graph or grant reuse.

    A checkpoint projection has no build provider and is deliberately neither
    retained as an accepting surface nor cached under the accepting build key.
    Explicit preparation and strict workers keep their existing build owner.
    """

    expected = tuple(sorted({
        str(specification).strip()
        for specification in expected_specifications
        if str(specification).strip()
    }))
    retained = builder_issued_v11_lean_review_surface(folder, context)
    if retained is not None and set(retained.semantic_targets) == set(expected):
        return retained

    def read() -> V11LeanReviewSurface:
        if context.v11_lean_review_graph_payload is None:
            raise ValueError(
                "explicit Lean graph preparation required: no current retained checkpoint"
            )
        try:
            result = build_v11_review_surface_material(
                repository_root, folder, expected, context=context,
                require_graph_checkpoint=True,
            )
        except (OSError, RuntimeError, TypeError, ValueError) as exc:
            raise ValueError(
                "explicit Lean graph preparation required: " + str(exc)
            ) from exc
        if not isinstance(result, V11LeanReviewSurface):
            raise TypeError("diagnostic v11 graph reader returned a foreign surface")
        return result

    result = run_scoped_cached_value(
        context, folder=folder,
        key=("surface", "diagnostic_v11_lean_review_surface",
             repository_root.resolve().as_posix(), expected),
        compute=read,
    )
    if not isinstance(result, V11LeanReviewSurface):
        raise TypeError("diagnostic v11 graph cache contains a foreign surface")
    return result


def build_accepting_v11_review_surface(
    repository_root: Path,
    folder: Path,
    expected_specifications: Iterable[str],
    *,
    context: V11ReviewSurfaceContextView,
) -> V11LeanReviewSurface:
    """Build the accepting-path graph surface, including both current ledgers."""

    expected = tuple(
        sorted(
            {
                str(specification).strip()
                for specification in expected_specifications
                if str(specification).strip()
            }
        )
    )

    def build() -> V11LeanReviewSurface:
        result = build_v11_review_surface_material(
            repository_root,
            folder,
            expected,
            context=context,
        )
        if not isinstance(result, V11LeanReviewSurface):
            raise TypeError("accepting v11 graph builder returned a writer projection")
        context.record_v11_graph_carrier_reuse(
            carrier_reused=result.carrier_reused,
        )
        return result

    result = run_scoped_cached_value(
        context,
        folder=folder,
        key=(
            "surface",
            "v11_lean_review_surface",
            repository_root.resolve().as_posix(),
            expected,
        ),
        compute=build,
    )
    if not isinstance(result, V11LeanReviewSurface):
        raise TypeError("v11 Lean review surface cache contains a foreign value")
    context.retain_v11_review_surface(result)
    return result


def build_current_v11_review_graph_projection(
    repository_root: Path,
    folder: Path,
    expected_specifications: Iterable[str],
    *,
    context: V11ReviewSurfaceContextView,
) -> CurrentV11ReviewGraphProjection:
    """Reconstruct writer material from an exact saved graph carrier."""

    result = build_v11_review_surface_material(
        repository_root,
        folder,
        expected_specifications,
        context=context,
        checkpoint_projection_only=True,
    )
    if not isinstance(result, CurrentV11ReviewGraphProjection):
        raise TypeError("saved v11 graph reader returned an accepting surface")
    return result


def load_current_v11_review_graph_projection(
    repository_root: Path,
    folder: Path,
) -> CurrentV11ReviewGraphProjection | None:
    """Load writer targets from one exact transaction and saved graph.

    A missing operational graph is a cache miss, not authority to run Lean or
    consult presentation artifacts.  The complete target and prerequisite
    checks remain mandatory when a checkpoint is present.
    """

    from scripts.current_closeout.evidence_transaction import (
        build_current_v11_context_with_graph_checkpoint,
    )

    root = repository_root.resolve()
    paper_folder = folder.resolve()
    context = build_current_v11_context_with_graph_checkpoint(
        paper_folder,
        repository_root=root,
    )
    if context.v11_lean_review_graph_payload is None:
        return None
    try:
        specifications = tuple(
            sorted(
                EvidenceRouteSet.from_source_map(
                    context.statement_map
                ).result_specifications()
            )
        )
    except ObligationRouteError as exc:
        raise ValueError(
            "current v11 review graph has invalid typed result routes"
        ) from exc
    if not specifications:
        raise ValueError("current v11 review graph has no selected specifications")
    projection = build_current_v11_review_graph_projection(
        root,
        paper_folder,
        specifications,
        context=context,
    )
    context.record_v11_graph_carrier_reuse(
        carrier_reused=projection.carrier_reused
    )
    if set(projection.semantic_targets) != set(specifications):
        raise ValueError(
            "current v11 review graph does not contain every selected specification"
        )
    if set(projection.paper_prerequisite_targets) & set(
        projection.library_semantic_targets
    ):
        raise ValueError(
            "current v11 review graph assigns one prerequisite to two locations"
        )
    return projection


def builder_issued_v11_lean_review_surface(
    folder: Path,
    context: V11ReviewSurfaceContextView,
) -> V11LeanReviewSurface | None:
    """Return the typed graph surface retained by this exact transaction."""

    surface = lean_review_graph.builder_issued_v11_lean_review_surface(
        folder,
        context,
    )
    if surface is None:
        return None
    if not isinstance(surface, V11LeanReviewSurface):
        raise TypeError("retained v11 Lean graph has a foreign surface type")
    return surface



ROOT = Path(__file__).resolve().parents[2]
SOURCE_MAP_NAME = "audit/paper_statement_map.json"
INTAKE_FREEZE_NAME = "audit/intake_freeze.json"
V11_SCREENING_NAME = "audit/v11_raw_source_spec_screening.json"
V11_SCREENING_SCHEMA = 3
V11_SCREENING_PROMPT_VERSION = "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4"
V11_RAW_SOURCE_SPEC_SCREENING_FILE = V11_SCREENING_NAME
V11_RAW_SOURCE_SPEC_SCREENING_SCHEMA = V11_SCREENING_SCHEMA
V11_RAW_SOURCE_SPEC_SCREENING_PROMPT_VERSION = V11_SCREENING_PROMPT_VERSION
V11_RAW_SOURCE_SPEC_LEAN_TARGET_PROTOCOL = V11_LEAN_TARGET_PROTOCOL
PAPER_PREREQUISITE_LEDGER_NAME = "audit/paper_semantic_prerequisites.json"
LIBRARY_SEMANTIC_REVIEW_NAME = "audit/library_semantic_review.json"
PACKET_LEAN_CACHE_NAME = "audit/human_review_packet_lean_cache.json"
PACKET_LEAN_CACHE_SCHEMA = 5
_PACKET_LEAN_CACHE_SCHEMA_3_PROTOCOLS = {
    "spec_proposition": "lean_transparent_paper_expansion_with_claim_atoms_v2",
    "definition_declaration": "lean_paper_definition_declaration_display_v1",
    "paper_prerequisite": "lean_paper_declaration_display_v1",
    "library_prerequisite": "lean-library-display-plus-exact-code-v1",
}
_AUTO_SEMANTIC_REUSE_AUTHORITY = object()
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"
CORRECTED_SOURCE_STATEMENT_STATUS = "corrected_source_statement"
CORRECTED_TARGET_SCHEMA = 1
CORRECTED_TARGET_ROUTE_KIND = "approved_corrected_target"
CORRECTED_TARGET_MATCH_RESOLUTION = "approved_corrected_target"
POSITIVE_SEMANTIC_MATCH_JUDGMENTS = frozenset({"matches", APPROVED_CORRECTED_TARGET_MATCH})
SOURCE_ARTIFACT_SHA256_RE = re.compile(r"[0-9a-f]{64}")
PreparedClaimRow = tuple[dict[str, Any], tuple[Mapping[str, Any], ...], str]
PreparedClaimSection = tuple[str, tuple[PreparedClaimRow, ...]]


@dataclass(frozen=True)
class PreparedReviewSurface:
    """One typed, authenticated human-review surface shared by PDF and web.

    The object contains presentation rows only.  It does not grant closeout
    acceptance: exact cached Lean displays are admitted by the packet-cache
    authority, while source and judgment ledgers remain independently bound.
    Keeping this typed projection separate from parser-shaped ``ReviewItem``
    caches prevents the PDF and dashboard from rediscovering different claim
    or prerequisite surfaces.
    """

    paper_dir: Path
    source_map: Mapping[str, Any]
    status: Mapping[str, Any]
    surface_error: str
    presentation_authority: str
    report_context_presentation_sha256: str
    recorded_graph_projection: RecordedObligationGraphProjection | None
    claim_rows: tuple[PreparedClaimRow, ...]
    claim_sections: tuple[PreparedClaimSection, ...]
    paper_prerequisites: tuple[dict[str, Any], ...]
    library_prerequisites: tuple[dict[str, Any], ...]
    governing_declarations: tuple[dict[str, Any], ...] = ()


@dataclass(frozen=True)
class _PacketLeanCacheSelection:
    """One authenticated packet-cache selection and its owning authority."""

    payload: Mapping[str, Any]
    authority: str
    recorded_graph_projection: RecordedObligationGraphProjection | None = None
    current_graph_projection: CurrentV11ReviewGraphProjection | None = None


def _read_json(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError(f"could not read {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return payload


def _paper_lean_tree_sha256(paper_dir: Path) -> str:
    """Hash the exact paper-local Lean sources behind a cached display pass."""

    digest = hashlib.sha256()
    for path in sorted(paper_dir.rglob("*.lean")):
        relative = path.relative_to(paper_dir).as_posix().encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        contents = path.read_bytes()
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def _library_semantic_source_modules_sha256(
    targets: Mapping[str, Any],
) -> str | None:
    """Fingerprint the reusable source modules on the cached Lean target surface.

    The packet cache already materializes every direct reusable prerequisite
    reached from its selected Specs.  Hashing those target modules therefore
    invalidates a cache when its reviewed library surface changes, without
    tying an unrelated paper to every file in the shared reusable library.
    The whole-library hash remains provenance in the cache; this focused
    fingerprint is the exact-current reuse guard.
    """

    modules: set[str] = set()
    for declaration, raw_target in targets.items():
        name = str(declaration).strip()
        if not name.startswith("AppliedModelingLib."):
            continue
        if not isinstance(raw_target, Mapping):
            return None
        module = str(raw_target.get("source_module") or "").strip()
        if not module.startswith("AppliedModelingLib."):
            return None
        source_path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if not source_path.is_file():
            return None
        modules.add(module)
    digest = hashlib.sha256()
    for module in sorted(modules):
        source_path = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        relative = source_path.relative_to(ROOT).as_posix().encode("utf-8")
        contents = source_path.read_bytes()
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def _packet_lean_display_engine_paths() -> tuple[Path, ...]:
    """Return only implementation files that determine Lean display bytes."""

    return (
        (ROOT / "scripts").joinpath("lean_signature_manifest.py"),
        (ROOT / "scripts").joinpath("lean_signature_manifest_helper.lean"),
    )


def _packet_lean_display_engine_sha256() -> str:
    """Return a fingerprint of the Lean code producing cached displays.

    The packet cache stores Lean-elaborated declarations, not Python-selected
    presentation rows.  Its paper/library tree digests and exact Spec-name set
    already invalidate changes to the semantic surface, while every consumer
    rechecks exact decision coverage under the current orchestration code.
    Binding this cache to the dashboard or packet renderer therefore caused
    unrelated Python edits to discard valid Lean work.  Fingerprint only the
    Python/Lean elaboration engine that determines the cached displays.
    """

    digest = hashlib.sha256()
    for path in _packet_lean_display_engine_paths():
        relative = path.name.encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        contents = path.read_bytes()
        # CACHE_RENDERER_NEUTRAL_START
        # A packet cache contains Lean declarations and dependency displays,
        # never its generated TeX.  Strip explicitly marked renderer-only
        # changes before hashing so they do not cause an unnecessary Lean walk
        # or invalidate an otherwise exact display cache.
        contents = re.sub(
            rb"\n[ \t]*# CACHE_RENDERER_NEUTRAL_START\n.*?\n[ \t]*# CACHE_RENDERER_NEUTRAL_END",
            b"",
            contents,
            flags=re.S,
        )
        # CACHE_RENDERER_NEUTRAL_END
        digest.update(len(contents).to_bytes(8, "big"))
        digest.update(contents)
    return digest.hexdigest()


def _packet_lean_cache_path(paper_dir: Path) -> Path:
    return paper_dir / PACKET_LEAN_CACHE_NAME


def paper_semantic_review_targets_from_cache(
    payload: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Return the source-boundary cards, with a read-only legacy fallback.

    The complete ``paper_prerequisite_targets`` graph remains in the cache so
    Lean dependency closure can be verified and rendered as supporting context.
    New caches additionally carry this explicit source-review subset. Older
    caches remain displayable while migration is in progress, but cannot turn
    an internal helper into a new reviewed boundary in a newly written cache.
    """

    selected = payload.get("paper_semantic_review_targets")
    if isinstance(selected, Mapping):
        return selected
    full = payload.get("paper_prerequisite_targets")
    return full if isinstance(full, Mapping) else {}


def paper_semantic_review_support_from_cache(
    payload: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Return matching source-boundary support identities from one cache."""

    selected = payload.get("paper_semantic_review_supporting_declarations_sha256")
    if isinstance(selected, Mapping):
        return selected
    full = payload.get("paper_prerequisite_supporting_declarations_sha256")
    return full if isinstance(full, Mapping) else {}


def _semantic_authority_packet_cache_current(
    paper_dir: Path,
    payload: Mapping[str, Any],
    names: list[str],
    authority: CurrentSemanticReuseAuthority,
) -> bool:
    """Rebind reviewed display bytes to current declaration semantics.

    The cache's historical tree/engine hashes remain provenance, not semantic
    identities.  Reuse is allowed only when the current verifier has issued a
    declaration-level authority for every selected Spec and the three human
    semantic ledgers bind the exact cached displays with positive judgments.
    """

    if (
        authority.paper != paper_dir.name
        or authority.result.get("current") is not True
        or not set(names).issubset(authority.reviewed_declarations)
    ):
        return False
    return _review_bound_packet_cache_current(paper_dir, payload, names)


def _packet_cache_display_integrity(payload: Mapping[str, Any]) -> bool:
    """Validate exact persisted display bytes before any cache can be reused."""

    for field in (
        "semantic_targets",
        "paper_prerequisite_targets",
        "library_semantic_targets",
    ):
        targets = payload.get(field)
        if not isinstance(targets, Mapping):
            return False
        for name, raw_target in targets.items():
            if not isinstance(name, str) or not name.strip() or not isinstance(
                raw_target, Mapping
            ):
                return False
            display = raw_target.get("display")
            expected = str(raw_target.get("display_sha256") or "").strip().lower()
            if (
                not isinstance(display, str)
                or not display.strip()
                or not re.fullmatch(r"[0-9a-f]{64}", expected)
                or hashlib.sha256(display.encode("utf-8")).hexdigest() != expected
            ):
                return False
            if field == "semantic_targets":
                atom_fields_present = any(
                    raw_target.get(key) is not None
                    for key in (
                        "review_claim_manifest_sha256",
                        "review_claim_atoms_sha256",
                        "review_claim_atoms",
                    )
                )
                if atom_fields_present:
                    # Packet-cache validation is a presentation-time reader.
                    # Keep the Lean manifest producer out of planner startup;
                    # the current graph path imports it only when validating
                    # persisted claim-atom display material.
                    from scripts.lean_signature_manifest import (
                        validated_review_claim_atom_material,
                    )

                    manifest_sha256 = str(
                        raw_target.get("review_claim_manifest_sha256") or ""
                    ).strip().lower()
                    if not re.fullmatch(r"[0-9a-f]{64}", manifest_sha256):
                        return False
                    try:
                        atoms, _digest = validated_review_claim_atom_material(
                            raw_target
                        )
                    except ValueError:
                        return False
                    if any(
                        not str(atom.get("display") or "").strip()
                        for atom in atoms
                    ):
                        return False
    raw_paper_support = payload.get(
        "paper_prerequisite_supporting_declarations_sha256"
    )
    paper_targets = payload.get("paper_prerequisite_targets")
    if (
        not isinstance(raw_paper_support, Mapping)
        or not isinstance(paper_targets, Mapping)
        or set(raw_paper_support) != set(paper_targets)
        or any(
            not isinstance(name, str)
            or not name.strip()
            or not isinstance(digest, str)
            or (
                digest
                and not re.fullmatch(r"[0-9a-f]{64}", digest.strip().lower())
            )
            for name, digest in raw_paper_support.items()
        )
    ):
        return False
    raw_selected_targets = payload.get("paper_semantic_review_targets")
    raw_selected_support = payload.get(
        "paper_semantic_review_supporting_declarations_sha256"
    )
    if (raw_selected_targets is None) != (raw_selected_support is None):
        return False
    if raw_selected_targets is not None and (
        not isinstance(raw_selected_targets, Mapping)
        or not isinstance(raw_selected_support, Mapping)
        or not set(raw_selected_targets).issubset(paper_targets)
        or set(raw_selected_support) != set(raw_selected_targets)
        or any(
            raw_selected_targets[name] != paper_targets[name]
            or raw_selected_support[name] != raw_paper_support[name]
            for name in raw_selected_targets
        )
    ):
        return False
    raw_library_sources = payload.get("library_declaration_sources")
    if raw_library_sources is not None:
        library_targets = payload.get("library_semantic_targets")
        if (
            not isinstance(raw_library_sources, Mapping)
            or not isinstance(library_targets, Mapping)
            or set(raw_library_sources) != set(library_targets)
        ):
            return False
        for name, raw_source in raw_library_sources.items():
            if not isinstance(name, str) or not name.strip() or not isinstance(
                raw_source, Mapping
            ):
                return False
            definition = raw_source.get("library_definition")
            expected = str(
                raw_source.get("library_definition_sha256") or ""
            ).strip().lower()
            source_path = str(raw_source.get("library_source_path") or "").strip()
            if (
                not isinstance(definition, str)
                or not definition.strip()
                or not re.fullmatch(r"[0-9a-f]{64}", expected)
                or hashlib.sha256(definition.encode("utf-8")).hexdigest() != expected
                or not source_path
                or Path(source_path).is_absolute()
            ):
                return False
    return True


def _current_packet_display_protocols() -> dict[str, str]:
    return {
        "spec_proposition": V11_LEAN_TARGET_PROTOCOL,
        "definition_declaration": V11_DEFINITION_TARGET_PROTOCOL,
        "paper_prerequisite": PAPER_PREREQUISITE_TARGET_PROTOCOL,
        "library_prerequisite": LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    }


def _packet_cache_display_protocols_current(payload: Mapping[str, Any]) -> bool:
    """Bind staged display reuse to semantic contracts, not source-file churn.

    Schema 3 originally implied the four protocol versions recorded below.
    New writers include them explicitly.  Either representation becomes stale
    when a display contract changes, while implementation-only edits that do
    not advance a contract leave the non-authoritative transport reusable.
    """

    raw = payload.get("display_protocols")
    if raw is None:
        recorded = _PACKET_LEAN_CACHE_SCHEMA_3_PROTOCOLS
    elif isinstance(raw, Mapping) and all(
        isinstance(key, str) and isinstance(value, str)
        for key, value in raw.items()
    ):
        recorded = dict(raw)
    else:
        return False
    if recorded != _current_packet_display_protocols():
        return False
    targets = payload.get("semantic_targets")
    if not isinstance(targets, Mapping):
        return False
    for raw_target in targets.values():
        if not isinstance(raw_target, Mapping):
            return False
        target_kind = str(raw_target.get("semantic_target_kind") or "").strip()
        actual = raw_target.get("lean_target_protocol")
        if not target_kind and actual is None:
            # Early schema-3 partial transports did not repeat the implied
            # protocol on an incomplete row.  They remain non-authoritative.
            continue
        expected = recorded.get(target_kind)
        if expected is None or actual != expected:
            return False
    return True


def _exact_current_packet_lean_cache_transport(
    paper_dir: Path,
    specification_names: Iterable[str],
) -> dict[str, Any] | None:
    """Return exact current staged Lean displays without granting authority.

    Packet preparation is deliberately resumable: a successful bounded Lean
    batch is persisted before the complete claim/prerequisite surface exists.
    Such a partial cache may transport already-produced display bytes into the
    next preparation or reviewer-issuance step, but it is not an accepted
    presentation and supplies no semantic judgment or closeout credit.

    Reuse therefore requires the exact current paper Lean tree, reusable-
    library Lean tree, display-producing Lean engine, selected Spec list, and
    integrity of every display already present.  It intentionally does not
    consult a historical receipt or semantic ledger.  Consumers must still
    require the particular complete stage they need, and accepting audit gates
    independently bind those bytes to the current Lean graph and review.
    """

    path = _packet_lean_cache_path(paper_dir)
    if not path.is_file():
        return None
    try:
        payload = _read_json(path)
    except ValueError:
        return None
    names = sorted(
        {
            str(name).strip()
            for name in specification_names
            if str(name).strip()
        }
    )
    if (
        payload.get("schema") != PACKET_LEAN_CACHE_SCHEMA
        or payload.get("paper") != paper_dir.name
        or payload.get("specifications") != names
    ):
        return None
    for field in (
        "semantic_targets",
        "paper_prerequisite_targets",
        "paper_prerequisite_supporting_declarations_sha256",
        "library_semantic_targets",
        "library_semantic_target_errors",
    ):
        if not isinstance(payload.get(field), Mapping):
            return None
    semantic_targets = payload["semantic_targets"]
    paper_targets = payload["paper_prerequisite_targets"]
    paper_support = payload["paper_prerequisite_supporting_declarations_sha256"]
    library_targets = payload["library_semantic_targets"]
    library_errors = payload["library_semantic_target_errors"]
    assert isinstance(semantic_targets, Mapping)
    assert isinstance(paper_targets, Mapping)
    assert isinstance(paper_support, Mapping)
    assert isinstance(library_targets, Mapping)
    assert isinstance(library_errors, Mapping)
    library_semantic_source_modules_sha256 = str(
        payload.get("library_semantic_source_modules_sha256") or ""
    ).strip().lower()
    if (
        set(semantic_targets) - set(names)
        or set(paper_targets) & set(library_targets)
        or set(paper_support) != set(paper_targets)
        or set(library_targets) & set(library_errors)
        or any(
            not isinstance(name, str) or not name.strip()
            for targets in (
                semantic_targets,
                paper_targets,
                library_targets,
                library_errors,
            )
            for name in targets
        )
        or not _packet_cache_display_integrity(payload)
        or not re.fullmatch(r"[0-9a-f]{64}", library_semantic_source_modules_sha256)
        or library_semantic_source_modules_sha256
        != _library_semantic_source_modules_sha256(library_targets)
    ):
        return None
    exact_semantic_container = (
        payload.get("paper_lean_tree_sha256") == _paper_lean_tree_sha256(paper_dir)
        and library_semantic_source_modules_sha256
        == _library_semantic_source_modules_sha256(library_targets)
        and payload.get("lean_display_engine_sha256")
        == _packet_lean_display_engine_sha256()
        and _packet_cache_display_protocols_current(payload)
    )
    if not exact_semantic_container:
        graph_selected, graph_projection = _recorded_graph_packet_projection(paper_dir)
        if (
            not graph_selected
            or graph_projection is None
            or not graph_projection.reviewed_display_surface_complete
            or not _recorded_graph_packet_cache_current(
                payload, names, graph_projection
            )
            # Prospective preparation consumes the complete dependency
            # transport. A recorded review authenticates only its selected
            # roots, not extra cached helpers from a changed container.
            or set(paper_targets) | set(library_targets)
            != set(graph_projection.prerequisite_semantic_target_sha256s_by_declaration)
        ):
            return None
    return dict(payload)


def _recorded_graph_packet_cache_current(
    payload: Mapping[str, Any],
    names: list[str],
    projection: RecordedObligationGraphProjection,
) -> bool:
    """Bind one packet presentation to the selected accepted graph."""

    if (
        not _packet_cache_display_integrity(payload)
        or not _packet_cache_display_protocols_current(payload)
    ):
        return False
    targets = payload.get("semantic_targets")
    paper_targets = payload.get("paper_prerequisite_targets")
    library_targets = payload.get("library_semantic_targets")
    library_errors = payload.get("library_semantic_target_errors")
    if not all(
        isinstance(value, Mapping)
        for value in (targets, paper_targets, library_targets, library_errors)
    ):
        return False
    assert isinstance(targets, Mapping)
    assert isinstance(paper_targets, Mapping)
    assert isinstance(library_targets, Mapping)
    assert isinstance(library_errors, Mapping)

    cached_claims = {
        str(name): str(target.get("display_sha256") or "").strip().lower()
        for name, target in targets.items()
        if isinstance(target, Mapping)
    }
    recorded_claims = dict(
        projection.claim_semantic_target_sha256s_by_specification
    )
    if (
        set(targets) != set(names)
        or cached_claims != recorded_claims
        or set(recorded_claims) != set(names)
    ):
        return False

    if set(paper_targets) & set(library_targets):
        return False
    cached_prerequisites = {
        str(name): str(target.get("display_sha256") or "").strip().lower()
        for targets_by_location in (paper_targets, library_targets)
        for name, target in targets_by_location.items()
        if isinstance(target, Mapping)
    }
    recorded_prerequisites = dict(
        projection.prerequisite_semantic_target_sha256s_by_declaration
    )
    if any(
        cached_prerequisites.get(name) != digest
        for name, digest in recorded_prerequisites.items()
    ):
        return False
    return not any(str(value).strip() for value in library_errors.values())


def _recorded_graph_packet_cache_projection(
    payload: Mapping[str, Any], projection: RecordedObligationGraphProjection
) -> dict[str, Any]:
    """Expose only authenticated reviewed roots, never cached closure helpers."""

    selected = set(projection.prerequisite_semantic_target_sha256s_by_declaration)
    result = dict(payload)
    for field in (
        "paper_prerequisite_targets",
        "paper_prerequisite_supporting_declarations_sha256",
        "library_semantic_targets",
    ):
        if isinstance(payload.get(field), Mapping):
            result[field] = {
                name: value for name, value in payload[field].items() if name in selected
            }
    for selected_field, full_field in (
        ("paper_semantic_review_targets", "paper_prerequisite_targets"),
        ("paper_semantic_review_supporting_declarations_sha256",
         "paper_prerequisite_supporting_declarations_sha256"),
    ):
        if selected_field in payload:
            result[selected_field] = dict(result[full_field])
    # A packet cache is transport for Lean-emitted semantic displays.  Its
    # optional self-hashed source snippets are not accepted-graph authority;
    # recorded-card preparation reconstructs exact declaration text from the
    # separately authenticated prerequisite row and current source bytes.
    result.pop("library_declaration_sources", None)
    return result


def _current_v11_graph_packet_cache_current(
    payload: Mapping[str, Any],
    names: list[str],
    projection: object,
) -> bool:
    """Bind a non-evidentiary packet cache to one exact current graph.

    During a protocol migration a paper may still have an accepted historical
    graph while the current closeout transaction has already prepared a newer
    graph.  The historical graph remains the closure authority until strict
    finalization; it must not, however, make it impossible to render the
    current graph's review packet before that finalization.  This predicate
    compares only Lean-emitted display identities from the validated current
    graph.  It issues no semantic judgment and grants no closure status.
    """

    if not _packet_cache_display_integrity(payload):
        return False
    targets = payload.get("semantic_targets")
    paper_targets = payload.get("paper_prerequisite_targets")
    library_targets = payload.get("library_semantic_targets")
    library_errors = payload.get("library_semantic_target_errors")
    if not all(
        isinstance(value, Mapping)
        for value in (targets, paper_targets, library_targets, library_errors)
    ):
        return False
    current_targets = getattr(projection, "semantic_targets", None)
    current_paper = getattr(projection, "paper_prerequisite_targets", None)
    current_library = getattr(projection, "library_semantic_targets", None)
    current_errors = getattr(projection, "library_semantic_target_errors", None)
    current_library_sources = getattr(
        projection, "library_declaration_sources", None
    )
    if not all(
        isinstance(value, Mapping)
        for value in (
            current_targets,
            current_paper,
            current_library,
            current_errors,
            current_library_sources,
        )
    ):
        return False

    def display_identities(values: Mapping[str, Any]) -> dict[str, str]:
        return {
            str(name): str(target.get("display_sha256") or "").strip().lower()
            for name, target in values.items()
            if isinstance(target, Mapping)
        }

    assert isinstance(targets, Mapping)
    assert isinstance(paper_targets, Mapping)
    assert isinstance(library_targets, Mapping)
    assert isinstance(library_errors, Mapping)
    assert isinstance(current_targets, Mapping)
    assert isinstance(current_paper, Mapping)
    assert isinstance(current_library, Mapping)
    assert isinstance(current_errors, Mapping)
    assert isinstance(current_library_sources, Mapping)

    raw_selected_paper = payload.get("paper_semantic_review_targets")
    if raw_selected_paper is not None:
        if not isinstance(raw_selected_paper, Mapping):
            return False
        try:
            expected_selected_paper = selected_paper_semantic_prerequisite_targets(
                projection.context.statement_map,
                current_paper,
            )
        except (AttributeError, ValueError):
            return False
        if display_identities(raw_selected_paper) != display_identities(
            expected_selected_paper
        ):
            return False
    if current_library:
        try:
            expected_selected_library = selected_library_semantic_prerequisite_targets(
                projection.context.statement_map,
                current_library,
            )
        except (AttributeError, ValueError):
            return False
    else:
        expected_selected_library = {}
    expected_selected_library_errors = {
        name: error
        for name, error in current_errors.items()
        if name in expected_selected_library
    }
    cached_library_sources = payload.get("library_declaration_sources")
    if not isinstance(cached_library_sources, Mapping):
        return False

    def declaration_source_identity(value: object) -> tuple[object, ...] | None:
        if not isinstance(value, Mapping):
            return None
        return (
            value.get("library_definition"),
            str(value.get("library_definition_sha256") or "").strip().lower(),
            str(value.get("library_source_path") or "").strip(),
            value.get("library_line_start"),
            value.get("library_line_end"),
            str(value.get("library_definition_error") or "").strip(),
        )

    expected_library_sources = {
        name: current_library_sources.get(name)
        for name in expected_selected_library
    }
    return (
        set(targets) == set(names)
        and display_identities(targets) == display_identities(current_targets)
        and display_identities(paper_targets) == display_identities(current_paper)
        and display_identities(library_targets)
        == display_identities(expected_selected_library)
        and set(cached_library_sources) == set(expected_selected_library)
        and all(
            declaration_source_identity(cached_library_sources.get(name))
            == declaration_source_identity(expected_library_sources.get(name))
            and declaration_source_identity(expected_library_sources.get(name))
            is not None
            for name in expected_selected_library
        )
        and not any(str(value).strip() for value in library_errors.values())
        and not any(
            str(value).strip()
            for value in expected_selected_library_errors.values()
        )
    )


def _recorded_graph_packet_projection(
    paper_dir: Path,
) -> tuple[bool, RecordedObligationGraphProjection | None]:
    """Return whether schema 6 owns this cache and its authenticated projection."""

    from scripts.obligation_closure_credential import (
        ObligationClosureCredentialError,
        validate_nonaccepting_recorded_graph_projection,
    )

    receipt_path = paper_dir / "FINAL_CLOSURE_RECEIPT.md"
    if not receipt_path.is_file():
        return False, None
    try:
        receipt = load_final_closure_receipt(ROOT, paper_dir.name)
    except FinalClosureReceiptError:
        # A present but unreadable canonical receipt cannot authorize fallback
        # to an unrelated historical cache path.
        return True, None
    schema = receipt.payload.get("schema")
    if schema == ACCEPTED_GRAPH_RECEIPT_SCHEMA:
        try:
            return True, validate_nonaccepting_recorded_graph_projection(
                ROOT, paper_dir.name, receipt.payload
            )
        except ObligationClosureCredentialError:
            return True, None
    if schema in {*LEGACY_RECEIPT_SCHEMAS, OBLIGATION_RECEIPT_SCHEMA}:
        return False, None
    return True, None


def _review_bound_packet_cache_current(
    paper_dir: Path,
    payload: Mapping[str, Any],
    names: list[str],
) -> bool:
    """Require every cached display to remain bound by current review ledgers.

    This helper is not cache authority by itself.  Its callers must separately
    authenticate the current Lean declarations through either declaration-
    level semantic reuse or the current imported source/correspondence graph.
    """

    if any(
        not isinstance(payload.get(field), str)
        or not re.fullmatch(r"[0-9a-f]{64}", str(payload.get(field)))
        for field in (
            "paper_lean_tree_sha256",
            "library_lean_tree_sha256",
            "library_semantic_source_modules_sha256",
            "lean_display_engine_sha256",
        )
    ):
        return False
    targets = payload.get("semantic_targets")
    paper_targets = payload.get("paper_prerequisite_targets")
    library_targets = payload.get("library_semantic_targets")
    library_errors = payload.get("library_semantic_target_errors")
    if not all(
        isinstance(value, Mapping)
        for value in (targets, paper_targets, library_targets, library_errors)
    ):
        return False
    assert isinstance(targets, Mapping)
    assert isinstance(paper_targets, Mapping)
    assert isinstance(library_targets, Mapping)
    try:
        screening = _read_json(paper_dir / V11_SCREENING_NAME)
        paper_review = _read_json(paper_dir / PAPER_PREREQUISITE_LEDGER_NAME)
        library_review = _read_json(
            paper_dir / LIBRARY_SEMANTIC_REVIEW_NAME
        )
    except ValueError:
        return False
    screening_items = screening.get("items")
    paper_items = paper_review.get("items")
    library_items = library_review.get("items")
    if not all(
        isinstance(value, Mapping)
        for value in (screening_items, paper_items, library_items)
    ):
        return False
    assert isinstance(screening_items, Mapping)
    assert isinstance(paper_items, Mapping)
    assert isinstance(library_items, Mapping)

    def reviewed_display_matches(
        cached: Mapping[str, Any],
        reviewed: Mapping[str, Any],
        *,
        cached_hash_field: str,
        reviewed_hash_field: str,
        accepted_judgments: frozenset[str] = frozenset({"matches"}),
    ) -> bool:
        if set(reviewed) - set(cached):
            return False
        for name, raw_review in reviewed.items():
            raw_cached = cached.get(name)
            if not isinstance(raw_review, Mapping) or not isinstance(
                raw_cached, Mapping
            ):
                return False
            cached_hash = str(raw_cached.get(cached_hash_field) or "").strip()
            reviewed_hash = str(raw_review.get(reviewed_hash_field) or "").strip()
            if not (
                raw_review.get("judgment") in accepted_judgments
                and re.fullmatch(r"[0-9a-f]{64}", cached_hash)
                and cached_hash == reviewed_hash
            ):
                return False
        return True

    if set(targets) != set(names) or not reviewed_display_matches(
        targets,
        screening_items,
        cached_hash_field="display_sha256",
        reviewed_hash_field="lean_expanded_statement_sha256",
        accepted_judgments=frozenset(
            {"matches", APPROVED_CORRECTED_TARGET_MATCH}
        ),
    ):
        return False
    for name, target in targets.items():
        reviewed = screening_items.get(name)
        if not isinstance(target, Mapping) or not isinstance(reviewed, Mapping):
            return False
        if not (
            reviewed.get("review_claim_manifest_sha256")
            == target.get("review_claim_manifest_sha256")
            and reviewed.get("review_claim_atoms_sha256")
            == target.get("review_claim_atoms_sha256")
            and re.fullmatch(
                r"[0-9a-f]{64}",
                str(reviewed.get("source_review_target_sha256") or "")
                .strip()
                .lower(),
            )
        ):
            return False
    if not reviewed_display_matches(
        paper_targets,
        paper_items,
        cached_hash_field="display_sha256",
        reviewed_hash_field="paper_semantic_target_sha256",
    ):
        return False
    if not reviewed_display_matches(
        library_targets,
        library_items,
        cached_hash_field="display_sha256",
        reviewed_hash_field="library_semantic_target_sha256",
    ):
        return False
    return not any(str(value).strip() for value in library_errors.values())


def _recorded_source_bundle_matches(recorded: object, current: str) -> bool:
    """Match one current source card to authenticated graph bundle candidates."""

    if isinstance(recorded, str):
        candidates = (recorded,)
    elif isinstance(recorded, tuple):
        candidates = recorded
    else:
        return False
    if (
        not current
        or not candidates
        or not all(
            isinstance(candidate, str)
            and SOURCE_ARTIFACT_SHA256_RE.fullmatch(candidate) is not None
            for candidate in candidates
        )
    ):
        return False
    return tuple(sorted(set(candidates))) == candidates and current in candidates


def _recorded_graph_source_cards_current(
    source_map: Mapping[str, Any],
    projection: RecordedObligationGraphProjection,
) -> bool:
    """Check every source-owned result and prerequisite card before reuse."""

    source_items = source_map.get("items")
    if not isinstance(source_items, Mapping):
        return False
    source_keys = set(projection.card_review_declarations_by_source_item)
    expected = projection.source_input_bundle_sha256s_by_source_item
    if source_keys != set(expected):
        return False
    for source_key in source_keys:
        record = source_items.get(source_key)
        if not isinstance(record, Mapping):
            return False
        _text, digest, error = source_semantic_input_bundle(
            record, require_context_roles=True
        )
        if error or not _recorded_source_bundle_matches(
            expected[source_key], digest
        ):
            return False
    return True


def _current_packet_lean_cache_selection(
    paper_dir: Path,
    specification_names: Iterable[str],
    *,
    source_map: Mapping[str, Any] | None = None,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None | object = (
        _AUTO_SEMANTIC_REUSE_AUTHORITY
    ),
) -> _PacketLeanCacheSelection | None:
    """Select one cache authority for the current semantic presentation.

    For schema-6 papers the recorded obligation graph authenticates the exact
    reviewed display digest for every result and
    prerequisite, independent of code location, checkout path, or producer
    container. Full-card callers also supply the current source map: recorded
    verdicts can own those cards only while all source bundles still match.
    A source-only change can instead use the exact current-v11 graph and its
    independent current ledgers. Display-only callers omit that context. This
    projection never checks Lean or grants current closure. Older receipts
    retain their exact container and historical semantic-reuse paths.
    """

    path = _packet_lean_cache_path(paper_dir)
    if not path.is_file():
        return None
    try:
        payload = _read_json(path)
    except ValueError:
        return None
    names = sorted({str(name).strip() for name in specification_names if str(name).strip()})
    basic_shape_invalid = (
        payload.get("schema") != PACKET_LEAN_CACHE_SCHEMA
        or payload.get("paper") != paper_dir.name
        or payload.get("specifications") != names
    )
    if basic_shape_invalid:
        return None
    for field in (
        "semantic_targets",
        "paper_prerequisite_targets",
        "library_semantic_targets",
        "library_semantic_target_errors",
    ):
        if not isinstance(payload.get(field), Mapping):
            return None

    # A source-aware packet is a presentation of the current review
    # transaction.  When that transaction has a validated graph, its exact
    # displays and declaration sources own the cards even while an older graph
    # remains the accepted closure credential.  A stale cache must be refreshed
    # from the current graph; it cannot fall through to historical display
    # bytes or verdict metadata.
    if source_map is not None:
        try:
            current_projection = load_current_v11_review_graph_projection(
                ROOT, paper_dir
            )
        except (OSError, TypeError, ValueError):
            return None
        if current_projection is not None:
            if not _current_v11_graph_packet_cache_current(
                payload, names, current_projection
            ):
                return None
            return _PacketLeanCacheSelection(
                payload=payload,
                authority="current_v11_graph",
                current_graph_projection=current_projection,
            )
    graph_selected, graph_projection = _recorded_graph_packet_projection(paper_dir)
    if graph_selected:
        recorded_sources_current = source_map is None or (
            graph_projection is not None
            and _recorded_graph_source_cards_current(source_map, graph_projection)
        )
        if (
            graph_projection is not None
            and recorded_sources_current
            and graph_projection.reviewed_display_surface_complete
        ):
            if _recorded_graph_packet_cache_current(
                payload, names, graph_projection
            ):
                return _PacketLeanCacheSelection(
                    payload=_recorded_graph_packet_cache_projection(payload, graph_projection),
                    authority="accepted_graph",
                    recorded_graph_projection=graph_projection,
                )
        elif graph_projection is not None and recorded_sources_current:
            # Historical schema-6 graphs may authenticate canonical Lean
            # semantic signatures without recording the pretty-display digest.
            # Their accepted closure remains valid, but only their strict
            # historical semantic reader can authorize cached presentation
            # bytes.
            if not _packet_cache_display_integrity(payload):
                return None
            if semantic_reuse_authority is _AUTO_SEMANTIC_REUSE_AUTHORITY:
                semantic_reuse_authority = (
                    current_dashboard_semantic_reuse_authority(
                        paper_dir
                    )
                )
            if isinstance(
                semantic_reuse_authority, CurrentSemanticReuseAuthority
            ) and _semantic_authority_packet_cache_current(
                paper_dir, payload, names, semantic_reuse_authority
            ):
                return _PacketLeanCacheSelection(
                    payload=payload,
                    authority="accepted_graph_historical_display_reader",
                    recorded_graph_projection=graph_projection,
                )

        # A current migration graph may legitimately differ from the still
        # accepted historical graph.  It can own the pre-closeout packet's
        # display bytes without replacing that historical acceptance
        # credential or bypassing the current semantic ledgers.
        try:
            current_projection = load_current_v11_review_graph_projection(
                ROOT, paper_dir
            )
        except (OSError, TypeError, ValueError):
            current_projection = None
        if current_projection is not None and _current_v11_graph_packet_cache_current(
            payload, names, current_projection
        ):
            return _PacketLeanCacheSelection(
                payload=payload,
                authority="current_v11_graph",
                current_graph_projection=current_projection,
            )
        return None
    if not _packet_cache_display_integrity(payload):
        return None
    exact_container_current = (
        payload.get("paper_lean_tree_sha256") == _paper_lean_tree_sha256(paper_dir)
        and payload.get("library_semantic_source_modules_sha256")
        == _library_semantic_source_modules_sha256(
            payload.get("library_semantic_targets", {})
        )
        and payload.get("lean_display_engine_sha256")
        == _packet_lean_display_engine_sha256()
        and _packet_cache_display_protocols_current(payload)
    )
    if exact_container_current:
        return _PacketLeanCacheSelection(
            payload=payload,
            authority="exact_container",
        )
    if semantic_reuse_authority is _AUTO_SEMANTIC_REUSE_AUTHORITY:
        semantic_reuse_authority = (
            current_dashboard_semantic_reuse_authority(paper_dir)
        )
    if isinstance(
        semantic_reuse_authority, CurrentSemanticReuseAuthority
    ) and _semantic_authority_packet_cache_current(
        paper_dir, payload, names, semantic_reuse_authority
    ):
        return _PacketLeanCacheSelection(
            payload=payload,
            authority="current_semantic_reuse",
        )
    return None


def _current_packet_lean_cache(
    paper_dir: Path,
    specification_names: Iterable[str],
    *,
    semantic_reuse_authority: CurrentSemanticReuseAuthority | None | object = (
        _AUTO_SEMANTIC_REUSE_AUTHORITY
    ),
) -> dict[str, Any] | None:
    """Return the payload selected by the one packet-cache authority check."""

    selected = _current_packet_lean_cache_selection(
        paper_dir,
        specification_names,
        semantic_reuse_authority=semantic_reuse_authority,
    )
    return dict(selected.payload) if selected is not None else None


def packet_lean_cache_missing_stages(
    paper_dir: Path,
    source_map: Mapping[str, Any],
) -> tuple[str, ...]:
    """Return exact Lean-cache stages still missing for a fresh review.

    The persisted cache is operational transport, not evidence.  This helper
    therefore checks both its current content identity and the complete
    Lean-produced paper/library prerequisite closure before a planner may move
    from materialization to reviewer-owned semantic decisions.
    """

    try:
        specifications = list(
            EvidenceRouteSet.from_source_map(
                source_map
            ).result_specifications()
        )
    except ObligationRouteError:
        return ("specifications", "paper-prerequisites", "library")
    cache = _exact_current_packet_lean_cache_transport(
        paper_dir, specifications
    )
    if cache is None:
        return ("specifications", "paper-prerequisites", "library")
    semantic_targets = cache.get("semantic_targets")
    paper_targets = cache.get("paper_prerequisite_targets")
    library_targets = cache.get("library_semantic_targets")
    library_errors = cache.get("library_semantic_target_errors")
    graph_native_library_sources = cache.get("library_declaration_sources")
    if not isinstance(semantic_targets, Mapping) or set(semantic_targets) != set(
        specifications
    ):
        return ("specifications", "paper-prerequisites", "library")
    if not isinstance(paper_targets, Mapping):
        return ("paper-prerequisites", "library")
    required_paper = {
        str(name).strip()
        for target in semantic_targets.values()
        if isinstance(target, Mapping)
        for name in target.get("prerequisite_declarations", ())
        if str(name).strip()
    }
    required_paper.update(
        explicit_source_semantic_declarations(source_map, library=False)
    )
    required_paper.update(
        str(name).strip()
        for target in paper_targets.values()
        if isinstance(target, Mapping)
        for name in target.get("direct_paper_declarations", ())
        if str(name).strip()
    )
    if not required_paper.issubset(paper_targets):
        return ("paper-prerequisites", "library")
    if not isinstance(library_targets, Mapping) or not isinstance(
        library_errors, Mapping
    ):
        return ("library",)
    try:
        selected_library_targets = selected_library_semantic_prerequisite_targets(
            source_map,
            library_targets,
        )
    except ValueError:
        return ("library",)
    if source_map.get("semantic_route_schema") == 2:
        required_library = set(selected_library_targets)
    else:
        required_library = {
            str(name).strip()
            for target in [*semantic_targets.values(), *paper_targets.values()]
            if isinstance(target, Mapping)
            for name in target.get(
                "library_declarations",
                target.get("direct_library_declarations", ()),
            )
            if str(name).strip()
            and (
                isinstance(graph_native_library_sources, Mapping)
                or str(name).strip().startswith("AppliedModelingLib.")
            )
        }
        required_library.update(
            explicit_source_semantic_declarations(source_map, library=True)
        )
        required_library.update(
            str(name).strip()
            for target in library_targets.values()
            if isinstance(target, Mapping)
            for name in target.get("direct_library_declarations", ())
            if str(name).strip()
            and (
                isinstance(graph_native_library_sources, Mapping)
                or str(name).strip().startswith("AppliedModelingLib.")
            )
        )
    unresolved_errors = {
        str(name).strip()
        for name, error in library_errors.items()
        if str(name).strip() and str(error).strip()
    }
    sources_incomplete = (
        isinstance(graph_native_library_sources, Mapping)
        and set(graph_native_library_sources) != set(library_targets)
    )
    if (
        not required_library.issubset(library_targets)
        or unresolved_errors
        or sources_incomplete
    ):
        return ("library",)
    return ()


def _source_records_by_declaration(
    source_map: Mapping[str, Any],
) -> dict[str, list[Mapping[str, Any]]]:
    """Index source-map records by every paper-facing Lean route they name."""

    out: dict[str, list[Mapping[str, Any]]] = {}
    raw_items = source_map.get("items")
    items: Iterable[tuple[str, Any]]
    if isinstance(raw_items, Mapping):
        items = raw_items.items()
    elif isinstance(raw_items, list):
        items = (
            (str(item.get("id") or item.get("source_item") or ""), item)
            for item in raw_items
            if isinstance(item, Mapping)
        )
    else:
        return out
    for _key, raw_item in items:
        if not isinstance(raw_item, Mapping):
            continue
        routes: set[str] = set()
        for field in ("lean_declarations", "review_rows"):
            values = raw_item.get(field)
            if isinstance(values, list):
                routes.update(str(value).strip() for value in values if str(value).strip())
        contract = raw_item.get("semantic_contract")
        if isinstance(contract, Mapping):
            for field in ("spec_declaration", "evidence_declaration"):
                value = str(contract.get(field) or "").strip()
                if value:
                    routes.add(value)
        for route in routes:
            out.setdefault(route, []).append(raw_item)
    return out


def _source_map_records(source_map: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    """Return source-map records in their declared, stable source order."""

    raw_items = source_map.get("items")
    if isinstance(raw_items, Mapping):
        return [item for item in raw_items.values() if isinstance(item, Mapping)]
    if isinstance(raw_items, list):
        return [item for item in raw_items if isinstance(item, Mapping)]
    return []


def _typed_result_records(
    source_map: Mapping[str, Any],
) -> tuple[
    dict[str, Mapping[str, Any]],
    dict[str, Any],
]:
    """Return source result records by Spec and typed route by source item.

    New role-typed maps must never fall back from a definition's
    ``lean_declarations`` list to a paper-claim row. The route core is the one
    authority for that distinction. Historical non-typed packet fixtures keep
    their presentation-only fallback in the callers below.
    """

    paper = str(source_map.get("paper") or "").strip()
    raw_items = source_map.get("items")
    if not paper or not isinstance(raw_items, Mapping):
        return {}, {}
    try:
        route_set = EvidenceRouteSet.from_source_map(
            source_map,
        )
        route_by_spec = route_set.result_route_by_specification()
    except ObligationRouteError as exc:
        raise ValueError("invalid typed source route surface: " + str(exc)) from exc
    records_by_spec = {
        specification: raw_items[route.source_item_id]
        for specification, route in route_by_spec.items()
        if isinstance(raw_items.get(route.source_item_id), Mapping)
    }
    return records_by_spec, route_set.by_source_item()


def explicit_source_semantic_declarations(
    source_map: Mapping[str, Any], *, library: bool
) -> set[str]:
    """Return the historical namespace-partitioned presentation seeds.

    Current graph-native audit passes the complete unpartitioned route set to
    Lean and must not call this helper.  It remains only for the older staged
    packet/dashboard path, whose results never grant acceptance.
    """

    paper = str(source_map.get("paper") or "").strip()
    if not paper:
        return set()
    try:
        route_set = EvidenceRouteSet.from_source_map(
            source_map
        )
    except ObligationRouteError as exc:
        raise ValueError("invalid typed source route surface: " + str(exc)) from exc
    return set(
        route_set.legacy_source_semantic_declarations_by_namespace(
            library=library
        )
    )


def _short_declaration_name(value: object) -> str:
    return str(value or "").strip().rsplit(".", 1)[-1]


def _validate_recorded_graph_card_surface(
    projection: RecordedObligationGraphProjection,
    claim_rows: Iterable[
        tuple[Mapping[str, Any], tuple[Mapping[str, Any], ...], str]
    ],
    paper_prerequisites: Iterable[Mapping[str, Any]],
    library_prerequisites: Iterable[Mapping[str, Any]],
) -> None:
    """Require exact two-way parity between graph review roots and cards."""

    expected = {
        str(source_item): set(declarations)
        for source_item, declarations in (
            projection.card_review_declarations_by_source_item.items()
        )
    }
    verdict_keys = set(projection.source_lean_verdicts_by_source_item)
    source_bundle_keys = set(
        projection.source_input_bundle_sha256s_by_source_item
    )
    if set(expected) != verdict_keys or set(expected) != source_bundle_keys:
        raise ValueError(
            "recorded accepted graph does not bind every selected semantic "
            "review item to one verdict and source bundle"
        )

    actual: dict[str, set[str]] = {}
    seen_cards: set[tuple[str, str]] = set()

    def record_card(source_item: str, declaration: str) -> None:
        identity = (source_item, declaration)
        if identity in seen_cards:
            raise ValueError(
                "prepared review cards repeat graph identity "
                + source_item
                + " -> "
                + declaration
            )
        seen_cards.add(identity)
        actual.setdefault(source_item, set()).add(declaration)

    for item, _records, _proof in claim_rows:
        source_item = str(item.get("source_item_key") or "").strip()
        declaration = str(
            item.get("semantic_review_declaration")
            or item.get("full_name")
            or ""
        ).strip()
        if not source_item or not declaration:
            raise ValueError("prepared claim card has no graph review identity")
        record_card(source_item, declaration)
    for entry in [*paper_prerequisites, *library_prerequisites]:
        source_item = str(entry.get("source_item") or "").strip()
        declaration = str(entry.get("lean_name") or "").strip()
        if not source_item or not declaration:
            raise ValueError(
                "prepared prerequisite card has no graph review identity"
            )
        record_card(source_item, declaration)

    if actual != expected:
        missing_items = sorted(set(expected) - set(actual))
        extra_items = sorted(set(actual) - set(expected))
        declaration_mismatches = sorted(
            source_item
            for source_item in set(actual) & set(expected)
            if actual[source_item] != expected[source_item]
        )
        details = []
        if missing_items:
            details.append("missing source items: " + ", ".join(missing_items))
        if extra_items:
            details.append("extra source items: " + ", ".join(extra_items))
        if declaration_mismatches:
            details.append(
                "declaration mismatch: " + ", ".join(declaration_mismatches)
            )
        raise ValueError(
            "prepared review cards do not exactly cover the recorded graph "
            "semantic surface"
            + (" (" + "; ".join(details) + ")" if details else "")
        )


def _intake_dependency_order(paper_dir: Path) -> dict[str, int]:
    """Read the approved claim-level order for human review.

    An intake freeze is the strongest recorded source-claim DAG
    linearization.  Historical v11 papers intentionally do not acquire a
    second intake authority; for them, use the explicit
    ``review_surface.include_names`` order already used by the dashboard.
    This is presentation metadata only and does not replace Lean closure
    evidence used for formal closeout.
    """

    path = paper_dir / INTAKE_FREEZE_NAME
    order: dict[str, int] = {}
    if path.is_file():
        try:
            payload = _read_json(path)
        except ValueError:
            payload = {}
        raw_items = payload.get("items")
        if isinstance(raw_items, list):
            for raw_item in raw_items:
                if not isinstance(raw_item, Mapping):
                    continue
                raw_rank = raw_item.get("dependency_order")
                if not isinstance(raw_rank, int) or raw_rank < 0:
                    continue
                for field in ("spec_declaration", "proof_declaration"):
                    name = _short_declaration_name(raw_item.get(field))
                    if name:
                        order[name] = raw_rank
    if order:
        return order

    status_path = paper_dir / "status.json"
    if not status_path.is_file():
        return {}
    try:
        status = _read_json(status_path)
    except ValueError:
        return {}
    review_surface = status.get("review_surface")
    configured = (
        review_surface.get("include_names")
        if isinstance(review_surface, Mapping)
        else None
    )
    if not isinstance(configured, list):
        return {}
    for rank, raw_name in enumerate(configured, start=1):
        name = _short_declaration_name(raw_name)
        if name and name not in order:
            order[name] = rank
    return order


def _semantic_route(record: Mapping[str, Any], field: str) -> str:
    contract = record.get("semantic_contract")
    if isinstance(contract, Mapping):
        value = str(contract.get(field) or "").strip()
        if value:
            return value
    return ""


def current_v11_screening_rows(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    semantic_targets: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Load current raw-source-to-Spec screening outcomes, if present.

    The record states what source bundle and full ``Spec`` were compared and
    any discrepancy found.  It is hash-bound, so a packet can never display a
    verdict for stale source text or a changed ``Spec`` declaration.
    """

    from scripts.direct_semantic_review_binding import (
        direct_source_spec_semantic_identity_matches,
    )

    path = paper_dir / V11_SCREENING_NAME
    if not path.is_file():
        return {}
    try:
        payload = _read_json(path)
    except ValueError:
        return {}
    if (
        payload.get("schema") != V11_SCREENING_SCHEMA
        or payload.get("paper") != paper_dir.name
        or payload.get("prompt_version")
        != V11_SCREENING_PROMPT_VERSION
    ):
        return {}
    raw_items = payload.get("items")
    records_by_spec, _route_by_source_item = _typed_result_records(source_map)
    if not records_by_spec:
        source_records = _source_map_records(source_map)
        records_by_spec = {
            _semantic_route(record, "spec_declaration"): record
            for record in source_records
            if _semantic_route(record, "spec_declaration")
        }
    if not isinstance(raw_items, Mapping):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for full_name, raw in raw_items.items():
        name = str(full_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            continue
        record = records_by_spec.get(name)
        target = semantic_targets.get(name)
        if record is None or target is None:
            continue
        source_text, source_digest, source_error = source_semantic_input_bundle(
            record, require_context_roles=True
        )
        # ``source_input_bundle_sha256`` binds the quoted source plus its
        # permitted context and anchors.  ``paper_statement_sha256`` binds
        # the literal source semantic target that the reviewer compared to
        # the transparent Spec.  They are intentionally distinct whenever a
        # claim has contextual anchors, so do not collapse the second check
        # to the bundle digest here.
        source_statement_digest = statement_digest(source_text)
        spec_digest = str(target.get("display_sha256") or "").strip().lower()
        target_protocol = str(
            target.get("lean_target_protocol") or V11_LEAN_TARGET_PROTOCOL
        ).strip()
        review_declaration = str(
            target.get("semantic_review_declaration") or name
        ).strip()
        verdict = str(raw.get("judgment") or "").strip().lower()
        corrected_target = record.get("corrected_target")
        approved_corrected_target = bool(
            verdict == APPROVED_CORRECTED_TARGET_MATCH
            and str(record.get("coverage_status") or "").strip()
            == "corrected_source_statement"
            and isinstance(corrected_target, Mapping)
            and corrected_target.get("archival_equivalence_claimed") is False
            and corrected_target_screening_binding_is_current(
                raw, corrected_target
            )
        )
        has_metadata = bool(
            str(raw.get("validator") or payload.get("validator") or "").strip()
            and str(raw.get("validated_at") or payload.get("validated_at") or "").strip()
        )
        current = bool(
            (
                approved_corrected_target
                if str(record.get("coverage_status") or "").strip()
                == "corrected_source_statement"
                else verdict in {"matches", "mismatch", "uncertain"}
            )
            and not source_error
            and direct_source_spec_semantic_identity_matches(raw, {
                "source_input_bundle_sha256": source_digest,
                "paper_statement_sha256": source_statement_digest,
                "lean_expanded_statement_sha256": spec_digest,
                "lean_target_protocol": target_protocol,
            })
            and re.fullmatch(
                r"[0-9a-f]{64}",
                str(raw.get("source_review_target_sha256") or "")
                .strip()
                .lower(),
            )
            and raw.get("semantic_target_declaration") == name
            and (
                str(raw.get("semantic_review_declaration") or name).strip()
                == review_declaration
            )
            and has_metadata
        )
        out[name] = {
            "judgment": verdict or "not recorded",
            "reason": str(raw.get("reason") or "").strip(),
            "validator": str(raw.get("validator") or payload.get("validator") or "").strip(),
            "validated_at": str(raw.get("validated_at") or payload.get("validated_at") or "").strip(),
            "current": current,
        }
    return out


def _claim_review_rows(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    interface_items: Mapping[str, Mapping[str, Any]] | Iterable[Mapping[str, Any]],
    *,
    typed_route_selection: tuple[
        Mapping[str, Mapping[str, Any]], Mapping[str, Any]
    ]
    | None = None,
) -> list[tuple[Mapping[str, Any], list[Mapping[str, Any]], str]]:
    """Select one human row per source claim, in approved DAG order.

    Each source-map item pairs a transparent ``Spec`` review proposition with a
    theorem whose type is that proposition.  The dashboard deliberately shows
    both Lean declarations; the packet instead shows the ``Spec`` once and
    names the paired theorem as its verification endpoint.  That keeps the
    human surface source-claim based and prevents duplicate review rows.
    """

    if not isinstance(interface_items, Mapping):
        interface_items = {
            str(item.get("full_name") or "").strip(): item
            for item in interface_items
            if str(item.get("full_name") or "").strip()
        }
    records_by_declaration = _source_records_by_declaration(source_map)
    order = _intake_dependency_order(paper_dir)
    selected: list[tuple[int, int, Mapping[str, Any], list[Mapping[str, Any]], str]] = []
    covered: set[str] = set()
    if typed_route_selection is None:
        records_by_spec, route_by_source_item = _typed_result_records(source_map)
    else:
        raw_records_by_spec, raw_routes = typed_route_selection
        records_by_spec = dict(raw_records_by_spec)
        route_by_source_item = dict(raw_routes)
    raw_items = source_map.get("items")
    record_items = (
        list(raw_items.items())
        if isinstance(raw_items, Mapping)
        else [(str(index), record) for index, record in enumerate(_source_map_records(source_map))]
    )
    for source_index, (source_key, record) in enumerate(record_items):
        if not isinstance(record, Mapping):
            continue
        route = route_by_source_item.get(str(source_key))
        if route is not None:
            spec_name = route.spec_declaration
            proof_name = route.evidence_declaration
        else:
            spec_name = _semantic_route(record, "spec_declaration")
            proof_name = _semantic_route(record, "evidence_declaration")
        if not spec_name and not route_by_source_item:
            routes = record.get("lean_declarations")
            if isinstance(routes, list):
                spec_name = next((str(route).strip() for route in routes if str(route).strip()), "")
        item = interface_items.get(spec_name)
        if item is None and route is not None and spec_name:
            # A role-typed source map already selects the exact Spec and proof
            # endpoint. The packet displays Lean's cached expanded target, so
            # reparsing PaperInterface merely to rediscover that name is both
            # redundant and brittle. Historical untyped maps retain the
            # parser-backed path below.
            item = {
                "kind": "def",
                "name": _short_declaration_name(spec_name),
                "full_name": spec_name,
                "interface_source": "",
                "lean_statement": "",
            }
        if item is None:
            continue
        covered.add(spec_name)
        if proof_name:
            covered.add(proof_name)
        rank = order.get(_short_declaration_name(spec_name), 10_000 + source_index)
        selected.append(
            (
                rank,
                source_index,
                item,
                records_by_declaration.get(
                    spec_name,
                    [records_by_spec.get(spec_name, record)],
                ),
                proof_name,
            )
        )

    # A legacy map must not hide a PaperInterface specification.  In contrast,
    # an activated v11 source-contract map is the deliberate claim surface:
    # paper-local helper Specs not selected by a one-claim-to-one-Spec route
    # must not silently enlarge its human-review denominator.
    if not route_by_source_item and source_map.get("semantic_contract_schema") != 1:
        for fallback_index, item in enumerate(interface_items.values(), start=len(selected)):
            full_name = str(item.get("full_name") or "").strip()
            if not full_name or full_name in covered:
                continue
            selected.append(
                (
                    20_000 + fallback_index,
                    fallback_index,
                    item,
                    records_by_declaration.get(full_name, []),
                    "",
                )
            )
    return [
        (item, records, proof_name)
        for _rank, _index, item, records, proof_name in sorted(selected, key=lambda entry: entry[:2])
    ]


def _dependency_first_entries(
    entries: Iterable[Mapping[str, Any]],
    *,
    name_field: str,
    dependency_field: str,
    normalize_dependency: Callable[[str], str] | None = None,
) -> list[Mapping[str, Any]]:
    """Return a deterministic dependency-first ordering for review cards.

    The order is solely a human-reading aid.  It makes a definition visible
    before the card which uses it, without trying to recreate Lean's proof or
    elaboration traversal in Python.  Lean has already supplied the direct
    dependencies in the cached display targets; Python merely topologically
    presents those reported edges.  Repeated cards or a genuine cycle are
    malformed presentation input and fail closed instead of being silently
    overwritten or assigned an arbitrary order.
    """

    materialized = list(entries)
    names = [str(entry.get(name_field) or "").strip() for entry in materialized]
    if any(not name for name in names):
        raise ValueError("prepared prerequisite card has no Lean declaration name")
    seen_names: set[str] = set()
    duplicate_names: set[str] = set()
    for name in names:
        if name in seen_names:
            duplicate_names.add(name)
        seen_names.add(name)
    duplicates = sorted(duplicate_names)
    if duplicates:
        raise ValueError(
            "prepared prerequisite cards repeat Lean declarations: "
            + ", ".join(duplicates)
        )
    by_name = dict(zip(names, materialized, strict=True))
    order: list[Mapping[str, Any]] = []
    temporary: set[str] = set()
    permanent: set[str] = set()

    def normalized(raw: object) -> str:
        value = str(raw or "").strip()
        return normalize_dependency(value) if normalize_dependency and value else value

    def visit(name: str) -> None:
        if name in permanent:
            return
        if name in temporary:
            raise ValueError(
                "prepared prerequisite dependency graph contains a cycle at "
                + name
            )
        entry = by_name.get(name)
        if entry is None:
            return
        temporary.add(name)
        raw_dependencies = entry.get(dependency_field, ())
        dependencies = (
            raw_dependencies if isinstance(raw_dependencies, (list, tuple, set)) else ()
        )
        for dependency in sorted(
            {normalized(raw) for raw in dependencies if normalized(raw)}
        ):
            # Generated projections can normalize back to their own review
            # owner.  That is one card, not a semantic dependency cycle.
            if dependency != name and dependency in by_name:
                visit(dependency)
        temporary.remove(name)
        permanent.add(name)
        order.append(entry)

    for name in sorted(by_name):
        visit(name)
    return order


def _governing_declaration_projection(
    semantic_targets: Mapping[str, Mapping[str, Any]],
    paper_targets: Mapping[str, Mapping[str, Any]],
    library_targets: Mapping[str, Mapping[str, Any]],
    *,
    reviewed_paper_declarations: Iterable[str] = (),
    reviewed_library_declarations: Iterable[str] = (),
) -> tuple[
    list[dict[str, Any]],
    dict[str, list[dict[str, str]]],
    dict[str, list[dict[str, str]]],
]:
    """Project Lean's authenticated retained-declaration closure for readers.

    Semantic result targets and prerequisite targets already carry direct
    dependency edges emitted by Lean.  This helper only follows those typed
    edges, checks that every reachable declaration has its authenticated
    display, and assigns stable packet destinations.  It does not parse Lean,
    create semantic-review rows, or change the result-card denominator.

    The third return value gives the same direct navigation for declarations
    already rendered as source-connected prerequisite review cards.  Those
    cards remain the sole display for their declaration; their transitive
    support is still reachable without duplicating the reviewed body.
    """

    paper_reviewed = {
        str(name).strip() for name in reviewed_paper_declarations if str(name).strip()
    }
    library_reviewed = {
        str(name).strip()
        for name in reviewed_library_declarations
        if str(name).strip()
    }
    overlap = sorted(paper_reviewed & library_reviewed)
    if overlap:
        raise ValueError(
            "governing declarations have both paper and library review cards: "
            + ", ".join(overlap)
        )

    by_name: dict[str, tuple[str, Mapping[str, Any]]] = {}
    for location, targets in (("paper", paper_targets), ("library", library_targets)):
        for raw_name, raw_target in targets.items():
            name = str(raw_name).strip()
            if not name or not isinstance(raw_target, Mapping):
                raise ValueError(
                    "governing declaration graph contains an invalid "
                    + location
                    + " target"
                )
            if name in by_name:
                raise ValueError(
                    "governing declaration graph repeats Lean declaration " + name
                )
            by_name[name] = (location, raw_target)

    def dependency_names(
        name: str, location: str, target: Mapping[str, Any]
    ) -> tuple[str, ...]:
        fields = (
            ("direct_paper_declarations", "direct_library_declarations")
            if location == "paper"
            else ("direct_library_declarations",)
        )
        values: list[str] = []
        for field in fields:
            raw_values = target.get(field, ())
            if not isinstance(raw_values, (list, tuple)):
                raise ValueError(
                    f"governing declaration {name} has malformed {field}"
                )
            values.extend(
                str(value).strip() for value in raw_values if str(value).strip()
            )
        return tuple(sorted(set(values)))

    def result_roots(name: str, target: Mapping[str, Any]) -> tuple[str, ...]:
        values: list[str] = []
        for field in ("prerequisite_declarations", "library_declarations"):
            raw_values = target.get(field, ())
            if not isinstance(raw_values, (list, tuple)):
                raise ValueError(
                    f"semantic result target {name} has malformed {field}"
                )
            values.extend(
                str(value).strip() for value in raw_values if str(value).strip()
            )
        return tuple(sorted(set(values)))

    roots_by_spec = {
        str(specification): result_roots(str(specification), target)
        for specification, target in semantic_targets.items()
    }
    reachable: set[str] = set()
    pending = sorted(
        {
            name for roots in roots_by_spec.values() for name in roots
        }
        | paper_reviewed
        | library_reviewed,
        reverse=True,
    )
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        located = by_name.get(name)
        if located is None:
            raise ValueError(
                "authenticated governing declaration display is unavailable for "
                + name
            )
        location, target = located
        display = target.get("display")
        display_sha256 = str(target.get("display_sha256") or "").strip().lower()
        if (
            not isinstance(display, str)
            or not display.strip()
            or not re.fullmatch(r"[0-9a-f]{64}", display_sha256)
            or hashlib.sha256(display.encode("utf-8")).hexdigest() != display_sha256
        ):
            raise ValueError(
                "authenticated governing declaration display is invalid for " + name
            )
        reachable.add(name)
        for dependency in reversed(dependency_names(name, location, target)):
            if dependency not in reachable:
                pending.append(dependency)

    dependencies = {
        name: dependency_names(name, *by_name[name]) for name in reachable
    }
    users_by_dependency: dict[str, set[str]] = {name: set() for name in reachable}
    remaining_dependencies: dict[str, int] = {}
    for name, names in dependencies.items():
        missing = sorted(set(names) - reachable)
        if missing:
            raise ValueError(
                "authenticated governing declaration closure is incomplete for "
                + name
                + ": "
                + ", ".join(missing)
            )
        remaining_dependencies[name] = len(names)
        for dependency in names:
            users_by_dependency[dependency].add(name)

    ready = sorted(name for name, count in remaining_dependencies.items() if count == 0)
    ordered: list[str] = []
    while ready:
        name = ready.pop(0)
        ordered.append(name)
        for user in sorted(users_by_dependency[name]):
            remaining_dependencies[user] -= 1
            if remaining_dependencies[user] == 0:
                ready.append(user)
        ready.sort()
    if len(ordered) != len(reachable):
        cycle = sorted(reachable - set(ordered))
        raise ValueError(
            "authenticated governing declaration graph contains a cycle: "
            + ", ".join(cycle)
        )

    def link(name: str) -> dict[str, str]:
        if name in paper_reviewed:
            anchor_kind = "paper-prerequisite"
        elif name in library_reviewed:
            anchor_kind = "library-prerequisite"
        else:
            anchor_kind = "governing-declaration"
        return {"lean_name": name, "anchor_kind": anchor_kind}

    direct_links_by_spec = {
        specification: [link(name) for name in roots]
        for specification, roots in roots_by_spec.items()
    }
    direct_links_by_declaration = {
        name: [link(dependency) for dependency in dependencies[name]]
        for name in ordered
    }
    entries: list[dict[str, Any]] = []
    for name in ordered:
        if name in paper_reviewed or name in library_reviewed:
            continue
        location, target = by_name[name]
        entries.append(
            {
                "lean_name": name,
                "location": location,
                "declaration_kind": str(target.get("declaration_kind") or "declaration"),
                "display": str(target.get("display") or ""),
                "display_sha256": str(target.get("display_sha256") or ""),
                "governing_declaration_links": direct_links_by_declaration[name],
            }
        )
    return entries, direct_links_by_spec, direct_links_by_declaration


def _claim_presentation_sections(
    status: Mapping[str, Any],
    rows: list[PreparedClaimRow],
) -> list[tuple[str, list[PreparedClaimRow]]]:
    """Group source cards for human reading without changing audit coverage.

    A paper can place appendix/supplement claims after main-text claims in its
    human review packet.  The group setting is presentation metadata only:
    every configured card remains in the same source-claim denominator, and
    material dependency cards are still shown before all source claims.
    """

    source_rows = [row for row in rows if not bool(row[0].get("is_assumption"))]
    assumption_rows = [row for row in rows if bool(row[0].get("is_assumption"))]

    def append_assumptions(
        sections: list[tuple[str, list[PreparedClaimRow]]],
    ) -> list[tuple[str, list[PreparedClaimRow]]]:
        if assumption_rows:
            sections.append(("Source-model assumptions", assumption_rows))
        return sections

    review_surface = status.get("review_surface")
    raw_sections = (
        review_surface.get("presentation_sections")
        if isinstance(review_surface, Mapping)
        else None
    )
    if raw_sections is None:
        return append_assumptions([("", source_rows)] if source_rows else [])
    if not isinstance(raw_sections, list) or not raw_sections:
        raise ValueError("review_surface.presentation_sections must be a nonempty list")

    lookup: dict[str, PreparedClaimRow] = {}
    for row in source_rows:
        item = row[0]
        full_name = str(item.get("full_name") or "").strip()
        short_name = _short_declaration_name(full_name)
        candidates = {full_name, short_name}
        if short_name.endswith("Spec"):
            candidates.add(short_name[: -len("Spec")])
        for candidate in candidates:
            if candidate:
                lookup[candidate] = row

    section_for_row: dict[str, str] = {}
    seen: set[str] = set()
    for raw in raw_sections:
        if not isinstance(raw, Mapping):
            raise ValueError("each presentation section must be an object")
        title = str(raw.get("title") or "").strip()
        names = raw.get("names")
        if (
            not title
            or not isinstance(names, list)
            or not names
            or not all(isinstance(name, str) and name.strip() for name in names)
        ):
            raise ValueError(
                "each presentation section needs a title and nonempty names"
            )
        for raw_name in names:
            name = str(raw_name).strip()
            row = lookup.get(name)
            if row is None:
                raise ValueError(
                    "presentation section references an unknown source card: " + name
                )
            full_name = str(row[0].get("full_name") or "").strip()
            if full_name in seen:
                raise ValueError(
                    "presentation sections repeat source card: " + name
                )
            seen.add(full_name)
            section_for_row[full_name] = title
    unassigned = [
        str(row[0].get("full_name") or "").strip()
        for row in source_rows
        if str(row[0].get("full_name") or "").strip() not in seen
    ]
    if unassigned:
        raise ValueError(
            "presentation sections must cover every source card; missing "
            + ", ".join(unassigned)
        )
    # `_claim_review_rows` has already read the approved intake's DAG
    # linearization.  Section metadata gives it headings only: it cannot move
    # a definition after a result which uses that definition.  A paper section
    # may therefore occur in more than one contiguous run when an earlier
    # prerequisite is needed by a claim in another paper section.
    grouped: list[tuple[str, list[PreparedClaimRow]]] = []
    used_titles: dict[str, int] = {}
    for row in source_rows:
        full_name = str(row[0].get("full_name") or "").strip()
        configured_title = section_for_row[full_name]
        if grouped and grouped[-1][0].split(" (continued", 1)[0] == configured_title:
            grouped[-1][1].append(row)
            continue
        used_titles[configured_title] = used_titles.get(configured_title, 0) + 1
        occurrence = used_titles[configured_title]
        displayed_title = (
            configured_title
            if occurrence == 1
            else configured_title + " (continued" + ("" if occurrence == 2 else " " + str(occurrence - 1)) + ")"
        )
        grouped.append((displayed_title, [row]))
    return append_assumptions(grouped)


def _v11_packet_surface_error(
    status: Mapping[str, Any], source_map: Mapping[str, Any]
) -> str:
    """Return why an unmarked packet would misrepresent its review surface."""

    if not explicit_raw_source_spec_screening_requested(status, source_map):
        return "the paper has not explicitly activated the v11 raw-source-to-Spec review surface"
    if source_map.get("semantic_contract_schema") != 1:
        return "the source map has not prepared the v11 one-claim-to-one-Spec contract surface"
    return ""


def _authenticated_recorded_prerequisite_row(
    paper_dir: Path,
    projection: RecordedObligationGraphProjection,
    *,
    location: str,
    declaration: str,
    source_item: str,
    semantic_target_sha256: str,
) -> dict[str, Any]:
    """Recover the exact ledger row authenticated by an accepted issuance."""

    metadata = getattr(
        projection, "prerequisite_review_metadata_by_declaration", {}
    )
    if not isinstance(metadata, Mapping) or declaration not in metadata:
        raise ValueError(
            "recorded prerequisite has no authenticated review metadata: "
            + declaration
        )
    recorded_metadata = metadata[declaration]
    if not isinstance(recorded_metadata, Mapping):
        raise ValueError(
            "recorded prerequisite has malformed authenticated review metadata: "
            + declaration
        )
    authenticated_record_sha256 = str(
        recorded_metadata.get("_evidence_record_sha256") or ""
    ).strip().lower()

    if location == "paper":
        path_name = PAPER_PREREQUISITE_LEDGER_NAME
        declaration_field = "paper_declaration"
        target_field = "paper_semantic_target_sha256"
        protocol_field = "paper_semantic_target_protocol"
        target_protocol = PAPER_PREREQUISITE_TARGET_PROTOCOL
    elif location == "library":
        path_name = LIBRARY_SEMANTIC_REVIEW_NAME
        declaration_field = "library_declaration"
        target_field = "library_semantic_target_sha256"
        protocol_field = "library_semantic_target_protocol"
        target_protocol = LIBRARY_SEMANTIC_TARGET_PROTOCOL
    else:
        raise ValueError("unknown recorded prerequisite location: " + location)

    payload = _read_json(paper_dir / path_name)
    items = payload.get("items")
    raw = items.get(declaration) if isinstance(items, Mapping) else None
    if (
        payload.get("schema") != 1
        or payload.get("paper") != paper_dir.name
        or not isinstance(raw, Mapping)
        or raw.get(declaration_field) != declaration
        or raw.get("source_item") != source_item
        or raw.get(target_field) != semantic_target_sha256
        or raw.get(protocol_field) != target_protocol
        or raw.get("judgment") not in POSITIVE_SEMANTIC_MATCH_JUDGMENTS
        or not re.fullmatch(r"[0-9a-f]{64}", authenticated_record_sha256)
        or hashlib.sha256(canonical_json_bytes(raw)).hexdigest()
        != authenticated_record_sha256
        or any(
            raw.get(field) != value
            for field, value in recorded_metadata.items()
            if field != "_evidence_record_sha256"
        )
    ):
        raise ValueError(
            "recorded prerequisite ledger row does not match its authenticated "
            "accepted-graph metadata: "
            + declaration
        )
    return dict(raw)


def _recorded_library_declaration_source(
    declaration: str,
    authenticated_row: Mapping[str, Any],
) -> dict[str, Any]:
    """Read one exact current source slice pinned by an authenticated row."""

    source_path = str(authenticated_row.get("library_source_path") or "").strip()
    line_start = authenticated_row.get("library_line_start")
    line_end = authenticated_row.get("library_line_end")
    expected_digest = str(
        authenticated_row.get("library_definition_sha256") or ""
    ).strip().lower()
    if (
        not source_path
        or Path(source_path).is_absolute()
        or not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
        or line_start < 1
        or line_end < line_start
        or not re.fullmatch(r"[0-9a-f]{64}", expected_digest)
    ):
        raise ValueError(
            "recorded library prerequisite has incomplete declaration-source "
            "metadata: "
            + declaration
        )
    root = ROOT.resolve()
    path = (root / source_path).resolve()
    try:
        path.relative_to(root)
    except ValueError as exc:
        raise ValueError(
            "recorded library prerequisite source resolves outside the repository: "
            + declaration
        ) from exc
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeDecodeError) as exc:
        raise ValueError(
            "could not read recorded library prerequisite source for "
            + declaration
            + ": "
            + str(exc)
        ) from exc
    line_count = line_end - line_start + 1

    def authenticated_window(start: int) -> tuple[str, int, int] | None:
        end = start + line_count - 1
        if start < 1 or end > len(lines):
            return None
        candidate = "\n".join(lines[start - 1 : end]).strip()
        if (
            not candidate
            or hashlib.sha256(candidate.encode("utf-8")).hexdigest()
            != expected_digest
        ):
            return None
        return candidate, start, end

    matched = authenticated_window(line_start)
    if matched is None:
        # Line insertions do not change the accepted source bytes.  Recover
        # their current display coordinates using only the authenticated
        # fixed line count and digest; zero or multiple exact windows remain
        # ambiguous and fail closed.
        matches = [
            candidate
            for start in range(1, len(lines) - line_count + 2)
            if (candidate := authenticated_window(start)) is not None
        ]
        if len(matches) != 1:
            raise ValueError(
                "recorded library prerequisite source does not uniquely match "
                "its authenticated declaration digest: "
                + declaration
            )
        matched = matches[0]
    definition, current_line_start, current_line_end = matched
    return {
        "library_definition": definition,
        "library_definition_sha256": expected_digest,
        "current_named_library_definition_sha256": expected_digest,
        "library_definition_error": "",
        "library_source_path": source_path,
        "library_line_start": current_line_start,
        "library_line_end": current_line_end,
        "library_definition_recorded_graph_authenticated": True,
    }


def _recorded_graph_prerequisite_cards(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    packet_cache: Mapping[str, Any],
    projection: RecordedObligationGraphProjection,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Render the graph's exact source-owned roots without a fresh-review lane."""

    source_items = source_map.get("items", {})
    paper_cards: list[dict[str, Any]] = []
    library_cards: list[dict[str, Any]] = []
    owners: dict[str, str] = {}
    for source_key, declarations in projection.card_review_declarations_by_source_item.items():
        for name in declarations:
            if name in owners and owners[name] != source_key:
                raise ValueError("recorded prerequisite has ambiguous source ownership: " + name)
            owners[name] = source_key
    for location, cards, field in (
        ("paper", paper_cards, "paper_prerequisite_targets"),
        ("library", library_cards, "library_semantic_targets"),
    ):
        for name, target in sorted(packet_cache.get(field, {}).items()):
            source_key = owners.get(name, "")
            record = source_items.get(source_key)
            if not source_key or not isinstance(record, Mapping):
                raise ValueError("recorded prerequisite has no exact source card: " + name)
            state, error = source_anchor_display_state(
                paper_dir, record, source_item_key=source_key
            )
            if error:
                raise ValueError("recorded prerequisite source: " + error)
            source_text, source_digest, error = source_semantic_input_bundle(
                record, require_context_roles=True
            )
            if error:
                raise ValueError("recorded prerequisite source: " + error)
            authenticated_row = _authenticated_recorded_prerequisite_row(
                paper_dir,
                projection,
                location=location,
                declaration=name,
                source_item=source_key,
                semantic_target_sha256=str(target.get("display_sha256") or ""),
            )
            declaration_source = (
                _recorded_library_declaration_source(name, authenticated_row)
                if location == "library"
                else {}
            )
            recorded_metadata = (
                getattr(
                    projection,
                    "prerequisite_review_metadata_by_declaration",
                    {},
                ).get(name, {})
            )
            cards.append({
                **declaration_source,
                "lean_name": name,
                "source_item": source_key,
                "source_locator": record.get("source_location", "not recorded"),
                "verbatim_source_input": source_text,
                "source_input_bundle_sha256": source_digest,
                "source_connection_error": "",
                "source_connection_state": state,
                "source_connection_display_only": state == PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE,
                "approved_review_contexts": list(record.get("approved_review_contexts") or []),
                "corrected_target_review_sha256": str(
                    authenticated_row.get("corrected_target_review_sha256") or ""
                ).strip().lower(),
                "semantic_judgment": str(
                    authenticated_row.get("judgment") or ""
                ).strip().lower(),
                f"{location}_semantic_target": target.get("display", ""),
                f"{location}_semantic_target_sha256": target.get("display_sha256", ""),
                f"{location}_semantic_target_kind": target.get("declaration_kind", ""),
                "direct_paper_declarations": list(target.get("direct_paper_declarations", ())),
                "direct_library_declarations": list(target.get("direct_library_declarations", ())),
                "semantic_reason": str(
                    recorded_metadata.get("reason") or ""
                ).strip(),
                "semantic_validator": str(
                    recorded_metadata.get("validator") or ""
                ).strip(),
                "semantic_validator_type": str(
                    recorded_metadata.get("validator_type") or ""
                ).strip(),
                "semantic_validated_at": str(
                    recorded_metadata.get("validated_at") or ""
                ).strip(),
            })
    return paper_cards, library_cards


def model_convention_contexts_from_source_map(
    source_map: Mapping[str, Any],
    *,
    include_additional_assumptions: bool = False,
) -> tuple[list[dict[str, Any]], str]:
    """Collect bound conventions and optionally assumption records for display."""

    schema = source_map.get("approved_review_context_schema")
    if schema is None:
        return [], ""
    if schema != 1:
        return [], "paper statement map has an unknown approved-review-context schema"
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        return [], "paper statement map has no items object"
    contexts_by_id: dict[str, dict[str, Any]] = {}
    identities_by_id: dict[str, str] = {}
    assumptions_by_record: dict[str, dict[str, Any]] = {}
    for source_item, raw in raw_items.items():
        if not isinstance(raw, Mapping):
            return [], f"source item `{source_item}` is not an object"
        contexts, error = validated_approved_review_contexts(raw)
        if error:
            return [], f"source item `{source_item}`: {error}"
        for context in contexts:
            if context.get("kind") != "source_model_convention":
                if include_additional_assumptions:
                    assumptions_by_record[str(context["record_sha256"])] = dict(context)
                continue
            context_id = str(context.get("id") or "").strip()
            record_sha256 = str(context.get("record_sha256") or "").strip().lower()
            prior = identities_by_id.get(context_id)
            if prior is not None and prior != record_sha256:
                return [], (
                    f"approved review context `{context_id}` has inconsistent "
                    "records across source items"
                )
            identities_by_id[context_id] = record_sha256
            contexts_by_id[context_id] = dict(context)
    return (
        [contexts_by_id[key] for key in sorted(contexts_by_id)]
        + [assumptions_by_record[key] for key in sorted(assumptions_by_record)],
        "",
    )


def prepared_review_surface(
    paper: str,
    *,
    allow_draft: bool = False,
) -> PreparedReviewSurface:
    """Build the exact typed review cards once for packet and dashboard use.

    This is a presentation projection over already prepared Lean display
    bytes and independently hash-bound source/judgment ledgers.  It never
    parses a role-typed ``PaperInterface.lean`` and never launches Lean.  A
    missing or unauthenticated packet cache is an explicit miss, not a reason
    to fall through to a second v11 discovery implementation.
    """

    paper_dir = ROOT / "papers" / paper
    if not paper_dir.is_dir():
        raise ValueError(f"unknown paper: {paper}")
    source_map = _read_json(paper_dir / SOURCE_MAP_NAME)
    status = _read_json(paper_dir / "status.json")
    model_contexts, model_context_error = model_convention_contexts_from_source_map(
        source_map, include_additional_assumptions=True
    )
    if model_context_error:
        raise ValueError("invalid report-context presentation source: " + model_context_error)
    context_presentation, context_presentation_error = report_context_presentation(
        paper_dir, model_contexts
    )
    if context_presentation_error or context_presentation is None:
        raise ValueError(
            "invalid report-context presentation: "
            + (context_presentation_error or "projection is unavailable")
        )
    surface_error = _v11_packet_surface_error(status, source_map)
    if surface_error and not allow_draft:
        raise ValueError(
            "refusing to produce an unmarked human-review surface: "
            + surface_error
            + ". Complete the v11 preparation first, or request a visibly "
            "incomplete diagnostic."
        )

    records_by_spec, typed_routes = _typed_result_records(source_map)
    if not typed_routes:
        raise ValueError("human-review preparation requires recorded typed source routes")
    interface_items = {}
    raw_claim_rows = _claim_review_rows(
        paper_dir,
        source_map,
        interface_items,
        typed_route_selection=(records_by_spec, typed_routes),
    )
    specifications = [
        str(item.get("full_name") or "")
        for item, _records, _proof in raw_claim_rows
    ]
    cache_selection = _current_packet_lean_cache_selection(
        paper_dir, specifications, source_map=source_map
    )
    if cache_selection is None:
        raise ValueError(
            "packet Lean displays are not cached for this exact paper Lean surface; "
            "run --prepare-lean-cache --stage specifications. A selected v11 "
            "paper materializes its complete saved graph in that one step; a "
            "legacy paper may then request the paper-prerequisites and library "
            "stages."
        )
    packet_cache = cache_selection.payload
    graph_projection = cache_selection.recorded_graph_projection
    semantic_targets = {
        str(name): dict(target)
        for name, target in packet_cache["semantic_targets"].items()
        if isinstance(target, Mapping)
    }
    if set(semantic_targets) != {name for name in specifications if name}:
        raise ValueError(
            "packet Lean-cache lacks a complete semantic Spec display set; "
            "rerun --prepare-lean-cache --stage specifications"
        )
    paper_prerequisite_targets = {
        str(name): dict(target)
        for name, target in paper_semantic_review_targets_from_cache(
            packet_cache
        ).items()
        if isinstance(target, Mapping)
    }
    paper_prerequisite_support_digests = {
        str(name): str(digest).strip().lower()
        for name, digest in paper_semantic_review_support_from_cache(
            packet_cache
        ).items()
        if isinstance(name, str) and isinstance(digest, str)
    }
    library_semantic_targets = {
        str(name): dict(target)
        for name, target in packet_cache["library_semantic_targets"].items()
        if isinstance(target, Mapping)
    }
    library_semantic_target_errors = {
        str(name): str(error)
        for name, error in packet_cache["library_semantic_target_errors"].items()
        if str(name).strip() and str(error).strip()
    }
    source_key_by_spec = {
        route.spec_declaration: source_key
        for source_key, route in typed_routes.items()
        if str(route.spec_declaration or "").strip()
    }
    raw_map_items = source_map.get("items")
    map_items = raw_map_items if isinstance(raw_map_items, Mapping) else {}
    review_surface = status.get("review_surface")
    raw_assumptions = (
        review_surface.get("assumption_names")
        if isinstance(review_surface, Mapping)
        else ()
    )
    if not isinstance(raw_assumptions, list):
        raw_assumptions = ()
    assumption_names = {
        str(name).strip()
        for name in raw_assumptions
        if str(name).strip()
    }

    prepared_rows: list[PreparedClaimRow] = []
    for row_index, (item, raw_records, proof_endpoint) in enumerate(
        raw_claim_rows, start=1
    ):
        records = tuple(
            record for record in raw_records if isinstance(record, Mapping)
        )
        prepared = dict(item)
        full_name = str(item.get("full_name") or "").strip()
        short_name = _short_declaration_name(full_name)
        target = semantic_targets.get(full_name, {})
        display = str(target.get("display") or "")
        source_key = source_key_by_spec.get(full_name, "")
        primary_record = records[0] if records else records_by_spec.get(full_name)
        source_text = ""
        source_digest = ""
        source_error = ""
        if isinstance(primary_record, Mapping):
            source_text, source_digest, source_error = (
                source_semantic_input_bundle(
                    primary_record, require_context_roles=True
                )
            )
        prepared.update(
            {
                "name": short_name,
                "full_name": full_name,
                "kind": str(item.get("kind") or "def"),
                "interface_source": "",
                "lean_statement": display,
                "paper_statement": source_text,
                "agent_statement": "",
                "verbatim_source_input": source_text,
                "source_input_bundle_sha256": source_digest,
                "source_item_key": source_key,
                "source_status": (
                    str(primary_record.get("source_status") or "direct source text")
                    if isinstance(primary_record, Mapping)
                    else "source connection unavailable"
                ),
                "source_note": (
                    str(primary_record.get("source_note") or source_error)
                    if isinstance(primary_record, Mapping)
                    else source_error
                ),
                "approved_review_contexts": (
                    list(primary_record.get("approved_review_contexts") or [])
                    if isinstance(primary_record, Mapping)
                    else []
                ),
                "human_claim_source_key": source_key,
                "human_claim_title": (
                    str(
                        (map_items.get(source_key) or {}).get("source_item")
                        or (map_items.get(source_key) or {}).get("title")
                        or source_key
                        or short_name
                    ).strip()
                    if isinstance(map_items.get(source_key), Mapping)
                    else source_key or short_name
                ),
                "human_claim_proof_endpoint": proof_endpoint,
                "human_claim_dag_order": row_index,
                "is_assumption": (
                    short_name in assumption_names or full_name in assumption_names
                ),
                "is_proposition_spec": True,
                "proposition_spec_role": "proof_routed",
                "proposition_spec_proof": proof_endpoint,
                "semantic_expanded_statement": display,
                "semantic_expanded_statement_sha256": str(
                    target.get("display_sha256") or ""
                ),
                "review_claim_manifest_sha256": str(
                    target.get("review_claim_manifest_sha256") or ""
                ),
                "review_claim_atoms_sha256": str(
                    target.get("review_claim_atoms_sha256") or ""
                ),
                # Atom self-digests exclude pretty display strings. Only the
                # full target display is authenticated by this graph reader;
                # fresh review material retains its separately prepared roles.
                "review_claim_atoms": (
                    [] if graph_projection is not None
                    else list(target.get("review_claim_atoms", ()))
                ),
                "semantic_target_kind": str(
                    target.get("semantic_target_kind")
                    or SemanticReviewTargetKind.SPEC_PROPOSITION.value
                ),
                "semantic_review_declaration": str(
                    target.get("semantic_review_declaration") or full_name
                ),
                "semantic_target_protocol": str(
                    target.get("lean_target_protocol") or V11_LEAN_TARGET_PROTOCOL
                ),
                "library_review_owner_declarations": list(
                    target.get("library_declarations", ())
                ),
                "paper_semantic_prerequisite_declarations": list(
                    target.get("prerequisite_declarations", ())
                ),
                "llm_match_judgment": "not recorded",
                "llm_match_reason": "",
                "llm_match_validator": "",
                "llm_match_validator_type": "llm_as_judge",
                "llm_match_validated_at": "",
                "llm_match_stale": False,
                "llm_match_source": "",
                "llm_match_lean_statement_sha256": str(
                    target.get("display_sha256") or ""
                ),
                "llm_match_paper_statement_sha256": (
                    statement_digest(source_text)
                    if source_text
                    else ""
                ),
                "llm_match_current": False,
            }
        )
        prepared_rows.append((prepared, records, proof_endpoint))

    if graph_projection is None:
        # Pre-graph papers retain their exact current screening reader.  A
        # graph-backed presentation must not consult it: the accepted graph is
        # the one recorded verdict authority for that surface.
        bind_current_v11_source_spec_screening(
            paper_dir, [item for item, _records, _proof in prepared_rows]
        )
    else:
        graph_verdicts = graph_projection.source_lean_verdicts_by_source_item
        graph_source_bundles = (
            graph_projection.source_input_bundle_sha256s_by_source_item
        )
        for item, _records, _proof in prepared_rows:
            source_key = str(item.get("source_item_key") or "").strip()
            specification = str(item.get("full_name") or "").strip()
            recorded_metadata = (
                getattr(
                    graph_projection,
                    "source_review_metadata_by_specification",
                    {},
                ).get(specification, {})
            )
            source_digest = str(
                item.get("source_input_bundle_sha256") or ""
            ).strip()
            verdict = str(graph_verdicts.get(source_key) or "").strip()
            expected_source_digest = graph_source_bundles.get(source_key)
            if (
                not source_key
                or not verdict
                or not _recorded_source_bundle_matches(
                    expected_source_digest, source_digest
                )
            ):
                raise ValueError(
                    "recorded accepted graph does not authenticate the exact "
                    "source card for "
                    + str(item.get("full_name") or item.get("name") or source_key)
                )
            item.update(
                {
                    # The graph is the sole verdict authority here.
                    "llm_match_judgment": (
                        "mismatch" if verdict == "does_not_match" else verdict
                    ),
                    "llm_match_reason": str(
                        recorded_metadata.get("reason") or ""
                    ).strip(),
                    "llm_match_stale": False,
                    "llm_match_source": "accepted obligation graph",
                    "llm_match_validator": (
                        str(recorded_metadata.get("validator") or "").strip()
                        or "accepted closeout"
                    ),
                    "llm_match_validator_type": (
                        str(
                            recorded_metadata.get("validator_type") or ""
                        ).strip()
                        or "recorded_semantic_review"
                    ),
                    "llm_match_validated_at": str(
                        recorded_metadata.get("validated_at") or ""
                    ).strip(),
                    "llm_match_current": True,
                    "llm_match_recorded_graph_sha256": (
                        graph_projection.graph_sha256
                    ),
                }
            )

    current_projection = cache_selection.current_graph_projection
    if graph_projection is not None:
        paper_prerequisites, library_prerequisites = _recorded_graph_prerequisite_cards(
            paper_dir, source_map, packet_cache, graph_projection
        )
    else:
        if paper_prerequisite_targets and current_projection is None:
            current_projection = load_current_v11_review_graph_projection(ROOT, paper_dir)
            if current_projection is None:
                raise ValueError(
                    "paper prerequisite cards require saved current graph source coordinates"
                )
        paper_prerequisites = _prepared_paper_prerequisites(
            paper_dir,
            semantic_targets,
            source_map_payload=source_map,
            semantic_targets_by_name_override=paper_prerequisite_targets,
            declaration_sources_override=(
                current_projection.paper_declaration_sources
                if paper_prerequisite_targets and current_projection is not None else {}
            ),
            supporting_declarations_sha256_by_name=paper_prerequisite_support_digests,
        )
        library_review_inputs: list[Mapping[str, Any]] = [
            item for item, _records, _proof in prepared_rows
        ]
        library_review_inputs.extend(
            {
                "library_review_owner_declarations": prerequisite.get(
                    "direct_library_declarations", ()
                )
            }
            for prerequisite in paper_prerequisites
        )
        explicit_library_declarations = explicit_source_semantic_declarations(
            source_map, library=True
        )
        if explicit_library_declarations:
            library_review_inputs.append(
                {
                    "library_review_owner_declarations": sorted(
                        explicit_library_declarations
                    )
                }
            )
        library_prerequisites = _prepared_library_prerequisites(
            paper_dir,
            library_review_inputs,
            semantic_targets_override=library_semantic_targets,
            semantic_target_errors_override=library_semantic_target_errors,
            declaration_sources_override=packet_cache.get(
                "library_declaration_sources"
            ),
            source_map_payload=source_map,
        )

    if graph_projection is not None:
        for entry in [*paper_prerequisites, *library_prerequisites]:
            source_key = str(entry.get("source_item") or "").strip()
            source_digest = str(
                entry.get("source_input_bundle_sha256") or ""
            ).strip()
            verdict = str(
                graph_projection.source_lean_verdicts_by_source_item.get(
                    source_key
                )
                or ""
            ).strip()
            expected_source_digest = (
                graph_projection.source_input_bundle_sha256s_by_source_item.get(
                    source_key
                )
            )
            if (
                not source_key
                or not verdict
                or not _recorded_source_bundle_matches(
                    expected_source_digest, source_digest
                )
            ):
                raise ValueError(
                    "recorded accepted graph does not authenticate the exact "
                    "prerequisite source card for "
                    + str(entry.get("lean_name") or entry.get("label") or source_key)
                )
            recorded_judgment = str(
                entry.get("semantic_judgment") or ""
            ).strip().lower()
            displayed_judgment = (
                recorded_judgment
                if verdict == "matches"
                and recorded_judgment in POSITIVE_SEMANTIC_MATCH_JUDGMENTS
                else "mismatch"
                if verdict == "does_not_match"
                else verdict
            )
            entry.update(
                {
                    "semantic_judgment": displayed_judgment,
                    "semantic_current": True,
                    "semantic_status": "accepted closeout",
                    "semantic_recorded_graph_sha256": (
                        graph_projection.graph_sha256
                    ),
                }
            )
        _attach_recorded_graph_prerequisite_contexts(
            [*paper_prerequisites, *library_prerequisites], source_map
        )
        _validate_recorded_graph_card_surface(
            graph_projection,
            prepared_rows,
            paper_prerequisites,
            library_prerequisites,
        )

    # Current graph packets can expose the complete Lean-emitted dependency
    # closure even when only a strict subset of those declarations are
    # source-owned semantic prerequisite rows.  Accepted-graph fallback keeps
    # using its authenticated reviewed roots: historical packet-cache helper
    # metadata is transport, not accepted-graph authority, so it is never
    # promoted here.  No graph acquisition occurs in either lane.
    governing_declarations: list[dict[str, Any]] = []
    if current_projection is not None:
        governing_declarations, result_links, declaration_links = (
            _governing_declaration_projection(
                current_projection.semantic_targets,
                current_projection.paper_prerequisite_targets,
                current_projection.library_semantic_targets,
                reviewed_paper_declarations=(
                    str(entry.get("lean_name") or "")
                    for entry in paper_prerequisites
                ),
                reviewed_library_declarations=(
                    str(entry.get("lean_name") or "")
                    for entry in library_prerequisites
                ),
            )
        )
        prepared_rows = [
            (
                {
                    **item,
                    "governing_declaration_links": list(
                        result_links.get(str(item.get("full_name") or ""), ())
                    ),
                },
                records,
                proof_endpoint,
            )
            for item, records, proof_endpoint in prepared_rows
        ]
        paper_prerequisites = [
            {
                **entry,
                "governing_declaration_links": list(
                    declaration_links.get(str(entry.get("lean_name") or ""), ())
                ),
            }
            for entry in paper_prerequisites
        ]
        library_prerequisites = [
            {
                **entry,
                "governing_declaration_links": list(
                    declaration_links.get(str(entry.get("lean_name") or ""), ())
                ),
            }
            for entry in library_prerequisites
        ]

    # Keep editorial wording beside, rather than inside, every hash-bound
    # approved context.  PDF and browser renderers consume this same derived
    # per-card projection and therefore cannot select different summaries.
    prepared_rows = [
        (
            {
                **item,
                "approved_review_context_presentation": row_context_presentation(
                    item.get("approved_review_contexts"), context_presentation
                ),
            },
            records,
            proof_endpoint,
        )
        for item, records, proof_endpoint in prepared_rows
    ]
    paper_prerequisites = [
        {
            **entry,
            "approved_review_context_presentation": row_context_presentation(
                entry.get("approved_review_contexts"), context_presentation
            ),
        }
        for entry in paper_prerequisites
    ]
    library_prerequisites = [
        {
            **entry,
            "approved_review_context_presentation": row_context_presentation(
                entry.get("approved_review_contexts"), context_presentation
            ),
        }
        for entry in library_prerequisites
    ]

    # Interpret Lean's direct prerequisite edges exactly once.  Both PDF and
    # browser receive these ordered tuples, so navigation cannot drift even
    # though it remains a nonaccepting presentation concern.
    paper_prerequisites = [
        dict(entry)
        for entry in _dependency_first_entries(
            paper_prerequisites,
            name_field="lean_name",
            dependency_field="direct_paper_declarations",
        )
    ]
    library_prerequisites = [
        dict(entry)
        for entry in _dependency_first_entries(
            library_prerequisites,
            name_field="lean_name",
            dependency_field="direct_library_declarations",
            normalize_dependency=None,
        )
    ]
    return PreparedReviewSurface(
        paper_dir=paper_dir,
        source_map=source_map,
        status=status,
        surface_error=surface_error,
        presentation_authority=cache_selection.authority,
        report_context_presentation_sha256=(
            context_presentation.presentation_sha256
        ),
        recorded_graph_projection=graph_projection,
        claim_rows=tuple(prepared_rows),
        claim_sections=tuple(
            (title, tuple(section_rows))
            for title, section_rows in _claim_presentation_sections(
                status, prepared_rows
            )
        ),
        paper_prerequisites=tuple(paper_prerequisites),
        library_prerequisites=tuple(library_prerequisites),
        governing_declarations=tuple(governing_declarations),
    )


def _prepared_paper_prerequisites(
    paper_dir: Path,
    semantic_targets: Mapping[str, Mapping[str, Any]],
    *,
    ledger_payload: Mapping[str, Any] | None = None,
    source_map_payload: Mapping[str, Any] | None = None,
    semantic_targets_by_name_override: Mapping[str, Mapping[str, Any]] | None = None,
    declaration_sources_override: Mapping[str, Mapping[str, Any]] | None = None,
    supporting_declarations_sha256_by_name: Mapping[str, str] | None = None,
    prerequisite_names: Iterable[str] | None = None,
    semantic_target_error: str = "",
) -> list[dict[str, Any]]:
    """Return source-connected paper-local primitives retained in Spec displays.

    An inductive state, transition relation, or structure is not a harmless
    unexpanded name.  Lean identifies it while expanding the paper claim; this
    function then requires the same raw-source connection and independent
    semantic judgment used for a reusable library primitive.  These cards are
    prerequisite review material, not additional paper-claim denominator rows.
    """

    if source_map_payload is None:
        try:
            source_map = _read_json(paper_dir / SOURCE_MAP_NAME)
        except ValueError:
            source_map = {}
    else:
        source_map = dict(source_map_payload)
    names = sorted(
        {
            str(name).strip()
            for target in semantic_targets.values()
            for name in target.get("prerequisite_declarations", ())
            if str(name).strip()
        }
    )
    if semantic_targets_by_name_override is None:
        names = sorted(
            set(names)
            | explicit_source_semantic_declarations(source_map, library=False)
        )
    else:
        names = sorted(
            set(names)
            | {
                str(name).strip()
                for name in semantic_targets_by_name_override
                if str(name).strip()
            }
        )
    if prerequisite_names is not None:
        names = sorted(set(prerequisite_names))
    if not names:
        return []
    if semantic_targets_by_name_override is not None:
        semantic_targets_by_name = {
            str(name).strip(): dict(target)
            for name, target in semantic_targets_by_name_override.items()
            if str(name).strip() and isinstance(target, Mapping)
        }
        missing = sorted(set(names) - set(semantic_targets_by_name))
        semantic_target_error = semantic_target_error or (
            "packet Lean-cache is missing paper-prerequisite targets: "
            + ", ".join(missing[:4])
            if missing
            else ""
        )
    else:
        raise ValueError("prepared paper cards require saved Lean targets")
    names = sorted(set(semantic_targets_by_name) or set(names))
    if ledger_payload is None:
        ledger_path = paper_dir / PAPER_PREREQUISITE_LEDGER_NAME
        try:
            ledger = _read_json(ledger_path) if ledger_path.is_file() else {}
        except ValueError:
            ledger = {}
    else:
        ledger = dict(ledger_payload)
    raw_items = ledger.get("items") if isinstance(ledger, Mapping) else {}
    ledger_items = raw_items if isinstance(raw_items, Mapping) else {}
    if declaration_sources_override is None:
        raise ValueError("prepared paper cards require saved Lean source coordinates")
    declarations = {
        str(name).strip(): dict(record)
        for name, record in declaration_sources_override.items()
        if str(name).strip()
        and str(name).strip() in names
        and isinstance(record, Mapping)
    }
    entries = project_paper_semantic_prerequisites(
        paper_dir,
        claim_semantic_targets=semantic_targets,
        prerequisite_semantic_targets=semantic_targets_by_name,
        semantic_target_errors={
            name: semantic_target_error
            for name in names
            if name not in semantic_targets_by_name and semantic_target_error
        },
        declaration_sources=declarations,
        source_map=source_map,
        ledger=ledger,
        repository_root=ROOT,
        file_bytes_override=None,
        supporting_declarations_sha256_by_name=(
            supporting_declarations_sha256_by_name or {}
        ),
    )

    # Public repositories deliberately omit the complete source artifact.  A
    # valid release projection may restore the exact pinned excerpt for packet
    # display, but it cannot change ``semantic_current`` or grant closeout
    # credit.  Keep this decoration outside the shared semantic projector.
    source_items = {
        str(key).strip(): raw
        for key, raw in (
            source_map.get("items", {}).items()
            if isinstance(source_map.get("items"), Mapping)
            else []
        )
        if str(key).strip() and isinstance(raw, Mapping)
    }
    for entry in entries:
        source_item_key = str(entry.get("source_item") or "").strip()
        source_record = source_items.get(source_item_key)
        if isinstance(source_record, Mapping):
            entry["approved_review_contexts"] = list(
                source_record.get("approved_review_contexts") or []
            )
        if not entry.get("source_connection_error"):
            continue
        name = str(entry.get("lean_name") or "").strip()
        raw = ledger_items.get(name)
        raw = raw if isinstance(raw, Mapping) else {}
        if source_record is None and isinstance(raw.get("source_anchor_evidence"), list):
            source_record = raw
        if source_record is None:
            continue
        state, display_error = source_anchor_display_state(
            paper_dir,
            source_record,
            source_item_key=source_item_key,
        )
        if display_error or state != PUBLIC_SOURCE_DISPLAY_PROJECTION_STATE:
            continue
        source_input, source_digest, bundle_error = (
            source_semantic_input_bundle(
                source_record, require_context_roles=True
            )
        )
        if bundle_error:
            continue
        entry.update(
            {
                "verbatim_source_input": source_input,
                "source_input_bundle_sha256": source_digest,
                "source_connection_error": "",
                "source_connection_state": state,
                "source_connection_display_only": True,
                "semantic_current": False,
                "semantic_status": "release-projected excerpt (display only)",
            }
        )
    _attach_identity_bound_prerequisite_contexts(entries, source_items)
    return entries


def _attach_identity_bound_prerequisite_contexts(
    entries: list[dict[str, Any]],
    source_items: Mapping[str, Mapping[str, Any]],
) -> None:
    """Attach only source context authenticated by the current review binding.

    The semantic prerequisite projector has already matched each current
    ledger row to one exact source item.  Keep the human-facing context on that
    same row: a corrected target is displayable only when the current ledger
    disposition and its correction digest both bind the selected map record.
    """

    for entry in entries:
        source_item = str(entry.get("source_item") or "").strip()
        source_record = source_items.get(source_item)
        if not isinstance(source_record, Mapping):
            continue
        entry["approved_review_contexts"] = list(
            source_record.get("approved_review_contexts") or []
        )
        correction_required = source_requires_approved_corrected_target(
            source_record
        )
        entry["corrected_target_required"] = correction_required
        if not correction_required:
            continue
        corrected_target = source_record.get("corrected_target")
        expected_digest = str(
            entry.get("corrected_target_review_sha256") or ""
        ).strip().lower()
        recorded_digest = (
            str(corrected_target.get("corrected_target_review_sha256") or "")
            .strip()
            .lower()
            if isinstance(corrected_target, Mapping)
            else ""
        )
        if (
            str(entry.get("semantic_judgment") or "").strip().lower()
            != APPROVED_CORRECTED_TARGET_MATCH
            or entry.get("semantic_current") is not True
            or not isinstance(corrected_target, Mapping)
            or corrected_target.get("archival_equivalence_claimed") is not False
            or recorded_digest != expected_digest
            or expected_digest != corrected_target_review_digest(corrected_target)
        ):
            continue
        entry["coverage_status"] = CORRECTED_SOURCE_STATEMENT_STATUS
        entry["corrected_target"] = freeze_json(dict(corrected_target))


def _attach_recorded_graph_prerequisite_contexts(
    entries: list[dict[str, Any]], source_map: Mapping[str, Any]
) -> None:
    """Restore only correction contexts authenticated by accepted row intent."""

    _attach_identity_bound_prerequisite_contexts(
        [
            entry
            for entry in entries
            if entry.get("semantic_judgment")
            == APPROVED_CORRECTED_TARGET_MATCH
        ],
        source_map_items_by_key(source_map),
    )


def _prepared_library_prerequisites(
    folder: Path,
    claims: Iterable[Mapping[str, Any]],
    *,
    require_build: bool = True,
    semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
    semantic_target_errors_override: Mapping[str, str] | None = None,
    source_map_payload: Mapping[str, Any] | None = None,
    ledger_payload: Mapping[str, Any] | None = None,
    declaration_sources_override: Mapping[str, Mapping[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    """Return material library definitions and their source-match status.

    A reusable library name may simplify paper code, but it does not bypass
    paper-source fidelity.  Each displayed prerequisite has (i) exact Lean
    declaration text from the library, (ii) an explicitly selected byte-pinned
    paper source item, and (iii) a freshness-checked raw-source-to-definition
    semantic judgment.  The source item's own raw bundle is used verbatim,
    exactly as for a paper-local Spec.  An absent connection or judgment is
    shown as pending and cannot be mistaken for a checked definition.
    """

    # A current graph-backed caller supplies the complete Lean-owned reusable
    # target set.  Stay entirely on that path: do not consult the historical
    # Python glossary, projection-owner map, qualified-name regex, or source
    # declaration parser.  Those remain only for rendering pre-graph papers.
    if semantic_targets_override is None:
        raise ValueError("prepared library cards require saved Lean targets")
    semantic_targets = {
        str(name).strip(): dict(target)
        for name, target in semantic_targets_override.items()
        if str(name).strip() and isinstance(target, Mapping)
    }
    semantic_target_errors = {
        str(name).strip(): str(error).strip()
        for name, error in (semantic_target_errors_override or {}).items()
        if str(name).strip() and str(error).strip()
    }
    required_names = {
        str(name).strip()
        for claim in claims
        for name in (
            claim.get("library_review_owner_declarations", ())
            if isinstance(
                claim.get("library_review_owner_declarations"),
                (list, tuple, set),
            )
            else ()
        )
        if str(name).strip()
    }
    for name in sorted(required_names - set(semantic_targets) - set(semantic_target_errors)):
        semantic_target_errors[name] = (
            "unified Lean graph omitted a required reusable semantic target"
        )
    if source_map_payload is None:
        try:
            source_map = _read_json(folder / SOURCE_MAP_NAME)
        except Exception:  # noqa: BLE001 - absence remains a visible pending item.
            source_map = {}
    else:
        source_map = dict(source_map_payload)
    source_items = source_map_items_by_key(source_map)
    if ledger_payload is None:
        ledger, _ledger_error = _prepared_library_ledger(folder)
    else:
        ledger = dict(ledger_payload)
    raw_ledger_items = ledger.get("items") if isinstance(ledger, Mapping) else {}
    ledger_items = raw_ledger_items if isinstance(raw_ledger_items, Mapping) else {}
    declaration_sources = (
        {
            str(name).strip(): dict(source)
            for name, source in declaration_sources_override.items()
            if str(name).strip() and isinstance(source, Mapping)
        }
        if declaration_sources_override is not None
        else lean_graph_library_declaration_sources(
            ROOT,
            semantic_targets=semantic_targets,
            semantic_target_errors=semantic_target_errors,
            file_bytes_override=None,
        )
    )
    entries = project_library_semantic_prerequisites(
        folder,
        semantic_targets=semantic_targets,
        semantic_target_errors=semantic_target_errors,
        declaration_sources=declaration_sources,
        source_map=source_map,
        ledger=ledger,
        repository_root=ROOT,
        file_bytes_override=None,
        required_names=required_names,
    )
    entries = _project_public_library_source_excerpts(
        folder,
        entries,
        ledger_items=ledger_items,
        source_items=source_items,
    )
    _attach_identity_bound_prerequisite_contexts(entries, source_items)
    return entries



def _prepared_library_ledger(folder: Path) -> tuple[Mapping[str, Any], str]:
    """Load an optional per-paper source-to-library review ledger.

    This lane deliberately reuses the paper statement map's raw source item.
    It never accepts a glossary explanation as the source side of the
    comparison, and an absent ledger is an explicit pending review rather than
    an implicit trust decision.
    """

    path = folder / LIBRARY_SEMANTIC_REVIEW_NAME
    if not _dashboard_is_file(path):
        return {}, "no library semantic-review ledger is recorded"
    payload = _dashboard_json_payload(path)
    if not isinstance(payload, Mapping):
        return {}, "library semantic-review ledger is unreadable"
    if payload.get("schema") != LIBRARY_SEMANTIC_REVIEW_SCHEMA:
        return {}, "library semantic-review ledger has an unsupported schema"
    if str(payload.get("paper") or "").strip() != folder.name:
        return {}, "library semantic-review ledger names a different paper"
    if (
        str(payload.get("prompt_version") or "").strip()
        != REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION
    ):
        return {}, "library semantic-review ledger has a stale or missing prompt version"
    if (
        str(payload.get("target_protocol") or "").strip()
        != LIBRARY_SEMANTIC_TARGET_PROTOCOL
    ):
        return {}, "library semantic-review ledger has a stale or missing target protocol"
    return payload, ""


def current_dashboard_semantic_reuse_authority(
    folder: Path,
) -> CurrentSemanticReuseAuthority | None:
    """Load one tracked, exact-input semantic authority for display reuse.

    A schema-6 accepted graph that carries the complete reviewed-display
    projection already owns this presentation. Do not read a legacy raw
    source-record authority in that case. Historical accepted graphs without
    display digests retain their strict recorded reader, while an invalid
    selected graph fails closed instead of falling through.

    This is not a planner, a Lean run, or a new receipt. The authority loader
    verifies its own content-addressed receipt, the exact raw-audit bytes, the
    declaration-level semantic identity, and every watched repository input.
    A miss leaves the dashboard on its ordinary fail-closed fresh path.
    """

    try:
        graph_selected, graph_projection = (
            _recorded_graph_packet_projection(folder)
        )
    except (OSError, RuntimeError, ValueError):
        graph_selected, graph_projection = False, None
    if graph_selected and (
        graph_projection is None
        or graph_projection.reviewed_display_surface_complete
    ):
        return None

    raw_path = folder / "audit" / "source_record_audit.json"
    try:
        raw_bytes = raw_path.read_bytes()
        raw_payload = json.loads(raw_bytes)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(raw_payload, Mapping) or raw_payload.get("paper") != folder.name:
        return None
    from scripts.source_record_semantic_reuse import (
        load_current_semantic_reuse_authority,
    )

    return load_current_semantic_reuse_authority(
        root=ROOT,
        paper_dir=folder,
        raw_audit_file_sha256=hashlib.sha256(raw_bytes).hexdigest(),
        raw_audit=raw_payload,
    )


def bind_current_v11_source_spec_screening(
    folder: Path,
    claim_rows: list[dict[str, Any]],
) -> None:
    """Attach a current v11 raw-source/expanded-Spec verdict to claim cards.

    The interactive dashboard and the mark-up packet share one semantic row
    per paper source claim.  A legacy ``statement_match_llm.json`` may still
    describe paired implementation declarations, so it is not a substitute
    for the v11 source-to-transparent-Spec screen.  This projection accepts a
    v11 row only when it binds the exact displayed source bundle, current
    PaperInterface bytes, and the Lean-elaborated expanded Spec shown on the
    card.
    """

    path = folder / V11_RAW_SOURCE_SPEC_SCREENING_FILE
    payload = _dashboard_json_payload(path)
    if not isinstance(payload, Mapping):
        return
    if (
        payload.get("schema") != V11_RAW_SOURCE_SPEC_SCREENING_SCHEMA
        or payload.get("paper") != folder.name
        or payload.get("prompt_version")
        != V11_RAW_SOURCE_SPEC_SCREENING_PROMPT_VERSION
    ):
        return
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return
    source_map = _dashboard_json_payload(folder / SOURCE_MAP_NAME) or {}
    source_map_items = source_map.get("items") if isinstance(source_map, Mapping) else None
    if not isinstance(source_map_items, Mapping):
        source_map_items = {}

    # This recorded-ledger projection is used only while preparing a human
    # review surface.  Keep the large semantic-obligation validator and its
    # Lean producer dependency out of planner startup.
    from scripts.semantic_obligation_review import (
        _normalize_llm_match_judgment,
    )

    def is_current_approved_corrected_target(
        claim_row: Mapping[str, Any], screening_row: Mapping[str, Any]
    ) -> bool:
        """Recognize the narrow v11 disposition for an approved correction.

        The raw-screening ledger distinguishes a literal source match from a
        comparison against the map's approved corrected target.  It is a
        positive source-to-Spec review only when the exact source-map item
        declares that correction and pins the same correction record.  The
        strict evidence audit independently validates the complete map and
        approval artifact at closeout; this dashboard projection deliberately
        mirrors its row-level admissibility rule rather than flattening the
        raw verdict globally.
        """

        if (
            str(screening_row.get("judgment") or "").strip().lower()
            != APPROVED_CORRECTED_TARGET_MATCH
        ):
            return False
        source_key = str(claim_row.get("human_claim_source_key") or "").strip()
        source_record = source_map_items.get(source_key)
        if not isinstance(source_record, Mapping):
            return False
        corrected_target = source_record.get("corrected_target")
        if (
            str(source_record.get("coverage_status") or "").strip()
            != CORRECTED_SOURCE_STATEMENT_STATUS
            or not isinstance(corrected_target, Mapping)
            or corrected_target.get("archival_equivalence_claimed") is not False
        ):
            return False
        return corrected_target_screening_binding_is_current(
            screening_row, corrected_target
        )

    payload_validator = str(payload.get("validator") or "").strip()
    payload_validated_at = str(payload.get("validated_at") or "").strip()
    for row in claim_rows:
        full_name = str(row.get("full_name") or "").strip()
        raw = raw_items.get(full_name)
        if not full_name or not isinstance(raw, Mapping):
            continue
        approved_corrected_target = is_current_approved_corrected_target(row, raw)
        # Preserve the reviewed disposition on the reviewer-facing card.
        # Earlier code flattened a current approved correction to ``matches``
        # here, even though the raw ledger and the displayed reason correctly
        # said it was not an archival equivalence.
        verdict = _normalize_llm_match_judgment(raw.get("judgment"))
        source_sha256 = str(row.get("source_input_bundle_sha256") or "").strip()
        verbatim_source_input = str(row.get("verbatim_source_input") or "")
        paper_target_sha256 = (
            statement_digest(verbatim_source_input)
            if verbatim_source_input
            # Compatibility for pre-v11 cached presentation fixtures. Real
            # v11 cards always retain the literal source input above.
            else source_sha256
        )
        expanded_sha256 = str(
            row.get("semantic_expanded_statement_sha256") or ""
        ).strip()
        claim_manifest_sha256 = str(
            row.get("review_claim_manifest_sha256") or ""
        ).strip()
        claim_atoms_sha256 = str(
            row.get("review_claim_atoms_sha256") or ""
        ).strip()
        target_protocol = str(
            row.get("semantic_target_protocol")
            or V11_RAW_SOURCE_SPEC_LEAN_TARGET_PROTOCOL
        ).strip()
        review_declaration = str(
            row.get("semantic_review_declaration") or full_name
        ).strip()
        current = bool(
            verdict
            in {*POSITIVE_SEMANTIC_MATCH_JUDGMENTS, "mismatch", "uncertain"}
            and source_sha256
            and raw.get("source_input_bundle_sha256") == source_sha256
            and raw.get("paper_statement_sha256") == paper_target_sha256
            and raw.get("lean_expanded_statement_sha256") == expanded_sha256
            and raw.get("review_claim_manifest_sha256")
            == claim_manifest_sha256
            and raw.get("review_claim_atoms_sha256") == claim_atoms_sha256
            # This field preserves the exact pretty-printed review worksheet
            # as trace evidence.  Within one unchanged target protocol, the
            # exact source input, expanded proposition, canonical claim
            # manifest, and canonical role atoms own semantic reuse.  Any
            # printer change capable of changing what the reviewer
            # semantically sees must advance the target protocol instead.
            and SOURCE_ARTIFACT_SHA256_RE.fullmatch(
                str(raw.get("source_review_target_sha256") or "")
                .strip()
                .lower()
            )
            and raw.get("source_input_protocol")
            == "verbatim_source_anchor_bundle_v1"
            and raw.get("lean_target_protocol") == target_protocol
            and raw.get("semantic_target_declaration") == full_name
            and str(raw.get("semantic_review_declaration") or full_name).strip()
            == review_declaration
            and bool(str(raw.get("validator") or payload_validator).strip())
            and bool(str(raw.get("validated_at") or payload_validated_at).strip())
        )
        if not current:
            continue
        source_key = str(row.get("human_claim_source_key") or "").strip()
        source_record = source_map_items.get(source_key)
        exact_routes: list[dict[str, Any]] = []
        if source_key and isinstance(source_record, Mapping):
            _statement, source_statement_sha256 = _source_item_coverage_statement(
                dict(source_record)
            )
            source_location = _source_item_coverage_location(dict(source_record))
            route_policy = source_item_effective_route_policy(dict(source_record))
            route_kind = (
                CORRECTED_TARGET_ROUTE_KIND
                if _source_item_is_corrected_target(dict(source_record))
                else "source_model_convention"
                if route_policy["is_model_convention"]
                else "direct"
            )
            if source_statement_sha256 and source_location:
                exact_routes = [
                    {
                        "source_item": source_key,
                        "source_statement_sha256": source_statement_sha256,
                        "source_location": source_location,
                        "route_kind": route_kind,
                    }
                ]
        row.update(
            {
                "llm_match_judgment": verdict,
                "llm_match_reason": str(raw.get("reason") or "").strip(),
                "llm_match_stale": False,
                "llm_match_source": path.name,
                "llm_match_validator": str(
                    raw.get("validator") or payload_validator
                ).strip(),
                "llm_match_validator_type": str(
                    raw.get("validator_type")
                    or payload.get("validator_type")
                    or "llm_as_judge"
                ).strip(),
                "llm_match_validated_at": str(
                    raw.get("validated_at") or payload_validated_at
                ).strip(),
                "llm_match_lean_statement_sha256": expanded_sha256,
                "llm_match_paper_statement_sha256": paper_target_sha256,
                "llm_match_resolution": (
                    CORRECTED_TARGET_MATCH_RESOLUTION
                    if approved_corrected_target
                    else ""
                ),
                "llm_match_boundary_type": "",
                "llm_match_boundary_names": [],
                "llm_match_conditional_premises": [],
                "llm_match_resolution_reason": "",
                "llm_match_source_routes": exact_routes,
                "llm_match_current": True,
            }
        )


def _source_item_corrected_target(item: dict[str, Any]) -> dict[str, Any] | None:
    """Return the structured corrected target only when its basic shape is usable.

    Full map-schema and source-ledger validation lives in
    ``audit_evidence_integrity.py``.  Dashboard checks still fail closed here
    when a source route or coverage row tries to use a malformed target.
    """

    target = item.get("corrected_target")
    if not isinstance(target, dict):
        return None
    if target.get("schema") != CORRECTED_TARGET_SCHEMA:
        return None
    statement = str(target.get("statement") or "").strip()
    if not statement:
        return None
    return target


def _source_item_is_corrected_target(item: dict[str, Any]) -> bool:
    return (
        str(item.get("coverage_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
    )


def _source_item_coverage_statement(item: dict[str, Any]) -> tuple[str, str]:
    """Return the statement/digest a coverage row is allowed to credit.

    Ordinary source items use the archival source statement.  A corrected item
    is intentionally different: only its explicit repaired target may be
    matched to Lean, while the archival statement remains visible in the
    inventory and never receives proof credit.
    """

    if _source_item_is_corrected_target(item):
        target = _source_item_corrected_target(item)
        if target is None:
            return "", ""
        statement = normalize_statement(str(target.get("statement") or ""))
        return statement, statement_digest(statement)
    statement = normalize_statement(str(item.get("statement") or ""))
    return statement, statement_digest(statement) if statement else ""


def _source_item_coverage_location(item: dict[str, Any]) -> str:
    """Return the archival anchor associated with the reviewed target."""

    if _source_item_is_corrected_target(item):
        target = _source_item_corrected_target(item)
        if target is None:
            return ""
        return str(target.get("archival_source_locator") or "").strip()
    return str(item.get("source_location") or "").strip()
