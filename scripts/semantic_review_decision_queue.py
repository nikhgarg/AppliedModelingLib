#!/usr/bin/env python3
"""Identity-bound, self-contained work queues for semantic review.

The review reissuers deliberately do not make semantic judgments.  They do,
however, have to preserve what the reviewer actually saw.  A bare tuple of
``source_item``, ``judgment``, and ``reason`` is insufficient: if the source
bundle or Lean target changes between queue preparation and receipt issuance,
the old verdict could otherwise be attached to new mathematics.

This module gives paper-local and reusable-library review lanes one compact
queue protocol.  Source excerpts are deduplicated at the top level, declaration
code and Lean-produced semantic displays are retained once per declaration,
and each filled decision is bound to the selected source-bundle digest and
semantic-target digest.  Receipt writers still recompute current material and
must compare those identities before accepting the verdict.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.corrected_target_identity import CORRECTED_TARGET_REVIEW_PROTOCOL
from scripts.semantic_review_binding import (
    reusable_semantic_judgment as reusable_semantic_judgment,
    unique_reusable_judgment_bindings,
)
from scripts.source_review_input import (
    approved_corrected_target_review_context,
    source_anchor_file_error,
    source_semantic_input_bundle,
    validated_approved_review_contexts,
)


QUEUE_SCHEMA = 3
QUEUE_PROTOCOL = "identity-bound-semantic-review-work-queue-v3"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")


class SemanticReviewDecisionQueueError(ValueError):
    """Raised when review material or a filled decision is not identity-bound."""


def changed_only_template_surface(
    payload: Mapping[str, Any],
    entries: list[dict[str, Any]],
    existing_items: Mapping[str, Any],
    *,
    reusable_judgment: Callable[
        [object, Mapping[str, Any]], dict[str, str] | None
    ],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Keep only rows whose exact reviewer authority cannot be reused."""

    entries_by_name = {
        str(entry.get("lean_name") or "").strip(): entry
        for entry in entries
        if str(entry.get("lean_name") or "").strip()
    }
    bindings = unique_reusable_judgment_bindings(
        entries_by_name,
        existing_items,
        reusable_judgment=reusable_judgment,
    )
    changed_names = set(entries_by_name) - set(bindings)
    filtered = dict(payload)
    filtered["items"] = {
        name: item
        for name, item in payload.get("items", {}).items()
        if name in changed_names
    }
    filtered["unrouted_declarations"] = [
        name
        for name in payload.get("unrouted_declarations", [])
        if name in changed_names
    ]
    return filtered, [
        entry
        for entry in entries
        if str(entry.get("lean_name") or "").strip() in changed_names
    ]


def template_output_path(
    paper_dir: Path,
    raw_path: Path,
    *,
    repository_root: Path,
) -> Path:
    """Return a new paper-local queue path without allowing overwrite."""

    path = raw_path if raw_path.is_absolute() else repository_root / raw_path
    path = path.resolve()
    try:
        path.relative_to(paper_dir.resolve())
    except ValueError as exc:
        raise SemanticReviewDecisionQueueError(
            "--emit-template must remain inside the paper folder"
        ) from exc
    if path.exists():
        raise SemanticReviewDecisionQueueError(
            f"refusing to overwrite existing decision template: {path}"
        )
    return path


def content_addressed_queue_path(
    paper_dir: Path,
    payload: Mapping[str, Any],
    *,
    filename_prefix: str,
) -> Path:
    """Derive one deterministic paper-local queue name from reviewed material."""

    digest = str(payload.get("review_material_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(digest):
        raise SemanticReviewDecisionQueueError(
            "current review queue has no exact material identity"
        )
    if not filename_prefix or not re.fullmatch(r"[a-z0-9_]+", filename_prefix):
        raise SemanticReviewDecisionQueueError(
            "content-addressed queue prefix is invalid"
        )
    return paper_dir / "audit" / f"{filename_prefix}{digest}.json"


def normalized_decisions(
    payload: Mapping[str, Any],
    *,
    paper: str,
    valid_verdicts: frozenset[str],
) -> dict[str, dict[str, Any]]:
    """Validate one filled queue and normalize its reviewer decisions."""

    raw_items = validated_queue_items(payload, paper=paper)
    raw_redirects = payload.get("source_item_redirects", {})
    if not isinstance(raw_redirects, Mapping) or not all(
        isinstance(source, str)
        and source.strip()
        and isinstance(target, str)
        and target.strip()
        for source, target in raw_redirects.items()
    ):
        raise SemanticReviewDecisionQueueError(
            "source_item_redirects must map nonempty source-map item ids"
        )
    redirects = {
        str(source).strip(): str(target).strip()
        for source, target in raw_redirects.items()
    }
    decisions: dict[str, dict[str, Any]] = {}
    for raw_name, raw in raw_items.items():
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            raise SemanticReviewDecisionQueueError(
                "each decision must have a nonempty declaration name and object"
            )
        judgment = str(raw.get("judgment") or "").strip().lower()
        reason = str(raw.get("reason") or "").strip()
        if judgment not in valid_verdicts:
            raise SemanticReviewDecisionQueueError(
                f"{name}: unsupported judgment `{judgment}`"
            )
        if not reason:
            raise SemanticReviewDecisionQueueError(
                f"{name}: reviewer reason is required"
            )
        decision = {**dict(raw), "judgment": judgment, "reason": reason}
        source_item = decision.get("source_item")
        if isinstance(source_item, str) and source_item.strip() in redirects:
            decision["source_item"] = redirects[source_item.strip()]
        decisions[name] = decision
    return decisions


def _text_digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256(value: object, *, label: str) -> str:
    digest = str(value or "").strip().lower()
    if not _SHA256_RE.fullmatch(digest):
        raise SemanticReviewDecisionQueueError(f"{label} must be a lowercase SHA-256 digest")
    return digest


def _validated_supporting_declarations(
    value: object,
) -> dict[str, dict[str, Any]]:
    """Validate exact graph-bound declarations shown as review context."""

    if not isinstance(value, Mapping) or not value:
        raise SemanticReviewDecisionQueueError(
            "supporting declarations must be a nonempty object"
        )
    result: dict[str, dict[str, Any]] = {}
    for raw_name, raw in sorted(value.items()):
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            raise SemanticReviewDecisionQueueError(
                "supporting declaration context is malformed"
            )
        scope = str(raw.get("scope") or "").strip()
        if scope not in {"paper_prerequisite", "library_prerequisite", "source_claim_use"}:
            raise SemanticReviewDecisionQueueError(
                f"{name}: supporting declaration has an invalid review scope"
            )
        target = str(raw.get("semantic_target") or "")
        target_digest = _sha256(
            raw.get("semantic_target_sha256"),
            label=f"{name} supporting semantic target",
        )
        if not target or _text_digest(target) != target_digest:
            raise SemanticReviewDecisionQueueError(
                f"{name}: supporting semantic target was modified"
            )
        if scope == "source_claim_use":
            if (
                not str(raw.get("lean_name") or "").strip()
                or "declaration_source" in raw
                or "declaration_source_sha256" in raw
            ):
                raise SemanticReviewDecisionQueueError(
                    f"{name}: source-claim use must name its exact display, not declaration code"
                )
            result[name] = dict(raw)
            continue
        declaration = str(raw.get("declaration_source") or "")
        declaration_digest = _sha256(
            raw.get("declaration_source_sha256"),
            label=f"{name} supporting declaration source",
        )
        if not declaration or _text_digest(declaration) != declaration_digest:
            raise SemanticReviewDecisionQueueError(
                f"{name}: supporting declaration source was modified"
            )
        result[name] = dict(raw)
    return result


def supporting_declarations_sha256(value: object) -> str:
    """Return the canonical identity of validated reviewer support context."""

    return _canonical_digest(_validated_supporting_declarations(value))


def selected_supporting_declarations_sha256(
    value: object,
    names: Iterable[str],
) -> str | None:
    """Return one row's exact support identity from a deduplicated bundle."""

    support = _validated_supporting_declarations(value)
    selected_names = tuple(sorted({str(name).strip() for name in names if str(name).strip()}))
    unknown = sorted(set(selected_names) - set(support))
    if unknown:
        raise SemanticReviewDecisionQueueError(
            "selected supporting declarations are absent from the review bundle: "
            + ", ".join(unknown[:4])
        )
    if not selected_names:
        return None
    return _canonical_digest({name: support[name] for name in selected_names})


def review_support_from_targets(
    review_targets: Mapping[str, Any],
    *,
    root_declarations: Iterable[str] | None = None,
    include_descendant_context: bool = True,
    include_nearest_source_use_context: bool = True,
) -> tuple[dict[str, dict[str, Any]], dict[str, tuple[str, ...]]]:
    """Project Lean-owned prerequisite displays and per-root dependency closure.

    With no roots, return every graph-bound paper/library prerequisite. With
    roots, return each root and, by default, only Lean-produced dependency and
    nearest source-use context.  A caller may request roots alone when a direct
    source-to-Spec card needs the meaning of a model parameter but should not
    become a recursive prerequisite review.

    A prerequisite can deliberately be more general than the paper model.  In
    that case its source fidelity is judged at its nearest use beneath a
    source-claim ``Spec`` (for example, a generic candidate record whose
    selected use fixes the paper's Gaussian law).  The graph therefore also
    follows the same Lean-produced edges *backward* through every declaration
    on each path until the nearest direct prerequisite of a selected source
    claim, then displays the consuming Spec itself. The restriction can occur
    in that Spec's arguments rather than in the generic prerequisite.
    Keeping the intervening declarations matters too. This is review
    context, not a new dependency or an inferred source route: the row's
    byte-pinned source connection remains the typed source-map connection.

    Python validates and transports the graph; it does not rediscover
    dependencies from Lean syntax, file layout, or declaration names.
    Source routing does not terminate display context: even an independently
    reviewed model can reference a constructor whose meaning the result
    reviewer needs. The retained Lean graph already bounds the material
    prerequisite surface, without proof-only or ordinary foundational detail.
    """

    paper_targets = review_targets.get("paper_prerequisite_targets", {})
    library_targets = review_targets.get("library_semantic_targets", {})
    paper_sources = review_targets.get("paper_declaration_sources", {})
    library_sources = review_targets.get("library_declaration_sources", {})
    library_errors = review_targets.get("library_semantic_target_errors", {})
    semantic_targets = review_targets.get("semantic_targets", {})
    if not all(
        isinstance(value, Mapping)
        for value in (
            paper_targets,
            library_targets,
            paper_sources,
            library_sources,
            library_errors,
            semantic_targets,
        )
    ):
        raise SemanticReviewDecisionQueueError(
            "current review graph has malformed prerequisite material"
        )
    if set(paper_targets) & set(library_targets):
        raise SemanticReviewDecisionQueueError(
            "current review graph has ambiguous prerequisite ownership"
        )

    all_targets = {**dict(paper_targets), **dict(library_targets)}

    # The direct prerequisites of a selected source claim are the boundary at
    # which a broad implementation helper becomes part of a particular paper
    # claim.  They are provided by Lean's semantic-claim graph, never guessed
    # from identifiers or source text.
    source_claim_prerequisites: set[str] = set()
    source_claim_uses: dict[str, set[str]] = {}
    for specification, raw_target in semantic_targets.items():
        if not isinstance(raw_target, Mapping):
            raise SemanticReviewDecisionQueueError(
                f"{specification}: semantic target material is malformed"
            )
        prerequisite_lists = [
            raw_target.get(field, ())
            for field in ("prerequisite_declarations", "library_declarations")
        ]
        if not all(isinstance(names, (list, tuple)) for names in prerequisite_lists):
            raise SemanticReviewDecisionQueueError(
                f"{specification}: Lean source-claim prerequisite list is malformed"
            )
        for raw_name in (name for names in prerequisite_lists for name in names):
            name = str(raw_name).strip()
            if name in all_targets:
                source_claim_prerequisites.add(name)
                source_claim_uses.setdefault(name, set()).add(specification)

    reverse_dependencies: dict[str, set[str]] = {
        name: set() for name in all_targets
    }
    for parent, target in all_targets.items():
        if not isinstance(target, Mapping):
            raise SemanticReviewDecisionQueueError(
                f"{parent}: prerequisite target material is malformed"
            )
        children = [
            str(name).strip()
            for field in (
                "direct_paper_declarations",
                "direct_library_declarations",
            )
            for name in target.get(field, ())
            if str(name).strip()
        ]
        unknown_children = sorted(set(children) - set(all_targets))
        if unknown_children:
            raise SemanticReviewDecisionQueueError(
                f"{parent}: Lean dependency edge leaves the material "
                "prerequisite surface: " + ", ".join(unknown_children[:4])
            )
        for child in children:
            reverse_dependencies[child].add(parent)
    roots = (
        tuple(sorted({str(name).strip() for name in root_declarations if str(name).strip()}))
        if root_declarations is not None
        else ()
    )
    unknown_roots = sorted(set(roots) - set(all_targets))
    if unknown_roots:
        raise SemanticReviewDecisionQueueError(
            "review support roots are outside the graph prerequisite surface: "
            + ", ".join(unknown_roots[:4])
        )

    names_by_root: dict[str, tuple[str, ...]] = {}
    selected_source_uses: set[str] = set()
    selected_names: set[str]
    if root_declarations is None:
        selected_names = set(all_targets)
    else:
        selected_names = set()
        for root in roots:
            # The direct source-claim prerequisite is itself reviewer context:
            # its bounded semantic target tells the reviewer what an abstract
            # parameter in the result Spec actually means.  Its descendants
            # and nearest source-facing uses then supply the compact Lean-owned
            # path needed to assess that meaning.  Omitting the root left a
            # result reviewer with an opaque model parameter despite a complete
            # graph-owned declaration being available.
            reached: set[str] = {root}
            pending = [root]
            if include_descendant_context:
                while pending:
                    current = pending.pop()
                    target = all_targets.get(current)
                    if not isinstance(target, Mapping):
                        raise SemanticReviewDecisionQueueError(
                            f"{current}: prerequisite target material is malformed"
                        )
                    children = [
                        str(name).strip()
                        for field in (
                            "direct_paper_declarations",
                            "direct_library_declarations",
                        )
                        for name in target.get(field, ())
                        if str(name).strip()
                    ]
                    unknown_children = sorted(set(children) - set(all_targets))
                    if unknown_children:
                        raise SemanticReviewDecisionQueueError(
                            f"{current}: Lean dependency edge leaves the material "
                            "prerequisite surface: " + ", ".join(unknown_children[:4])
                        )
                    for child in children:
                        if child == root or child in reached:
                            continue
                        reached.add(child)
                        pending.append(child)

            # Show the path to the closest source-claim use(s) of this
            # declaration as independently hash-bound Lean context.  Keep
            # each intermediate parent because that is where a generic helper
            # often receives the source restriction.  Do not walk past a
            # source-claim prerequisite: farther ancestors belong to a
            # different claim's wider proof route and would only obscure the
            # local model restriction the reviewer needs to inspect.
            uses: set[str] = set()
            if include_nearest_source_use_context:
                source_use_context: set[str] = set()
                seen_parents = {root}
                pending_parents = [root]
                while pending_parents:
                    current = pending_parents.pop()
                    for parent in sorted(reverse_dependencies[current]):
                        if parent in seen_parents:
                            continue
                        seen_parents.add(parent)
                        source_use_context.add(parent)
                        if parent in source_claim_prerequisites:
                            continue
                        pending_parents.append(parent)
                reached.update(source_use_context)
                for boundary in seen_parents & source_claim_prerequisites:
                    uses.update(source_claim_uses[boundary])
            names_by_root[root] = tuple(sorted(
                reached | {f"source_claim_use:{name}" for name in uses}
            ))
            selected_source_uses.update(uses)
            selected_names.update(reached)

    selected_library_errors = sorted(
        name
        for name in selected_names & set(library_errors)
        if str(library_errors.get(name) or "").strip()
    )
    if selected_library_errors:
        raise SemanticReviewDecisionQueueError(
            "current review graph has unresolved library prerequisite displays: "
            + ", ".join(selected_library_errors[:4])
        )
    missing_paper_sources = sorted(
        selected_names & set(paper_targets) - set(paper_sources)
    )
    if missing_paper_sources:
        raise SemanticReviewDecisionQueueError(
            "current review graph lacks paper prerequisite declaration sources: "
            + ", ".join(missing_paper_sources[:4])
        )
    missing_library_sources = sorted(
        selected_names & set(library_targets) - set(library_sources)
    )
    if missing_library_sources:
        raise SemanticReviewDecisionQueueError(
            "current review graph lacks library prerequisite declaration sources: "
            + ", ".join(missing_library_sources[:4])
        )

    support: dict[str, dict[str, Any]] = {}
    for name in sorted(selected_names):
        raw_target = all_targets[name]
        if name in paper_targets:
            raw_source = paper_sources[name]
            scope = "paper_prerequisite"
            declaration_field = "paper_declaration_source"
            declaration_digest_field = "paper_declaration_sha256"
        else:
            raw_source = library_sources[name]
            scope = "library_prerequisite"
            declaration_field = "library_definition"
            declaration_digest_field = "library_definition_sha256"
        if not isinstance(raw_target, Mapping) or not isinstance(raw_source, Mapping):
            raise SemanticReviewDecisionQueueError(
                f"{name}: prerequisite review material is malformed"
            )
        target = str(raw_target.get("display") or "")
        target_digest = str(raw_target.get("display_sha256") or "").strip().lower()
        declaration = str(raw_source.get(declaration_field) or "")
        declaration_digest = str(
            raw_source.get(declaration_digest_field) or ""
        ).strip().lower()
        if (
            (scope == "library_prerequisite" and str(raw_source.get("library_definition_error") or "").strip())
            or not target
            or _text_digest(target) != target_digest
            or not declaration
            or _text_digest(declaration) != declaration_digest
        ):
            raise SemanticReviewDecisionQueueError(
                f"{name}: prerequisite display or declaration source is stale"
            )
        support[name] = {
            "scope": scope,
            "semantic_target": target,
            "semantic_target_sha256": target_digest,
            "declaration_source": declaration,
            "declaration_source_sha256": declaration_digest,
        }
    for specification in sorted(selected_source_uses):
        key = f"source_claim_use:{specification}"
        if key in support:
            raise SemanticReviewDecisionQueueError(
                f"{specification}: source-use context key collides with a prerequisite"
            )
        target = semantic_targets[specification]
        support[key] = {
            "scope": "source_claim_use",
            "lean_name": specification,
            "semantic_target": str(target.get("display") or ""),
            "semantic_target_sha256": str(target.get("display_sha256") or ""),
        }
    if support:
        _validated_supporting_declarations(support)
    return support, names_by_root


def _source_context(
    paper_dir: Path,
    source_item: str,
    source_record: Mapping[str, Any],
) -> dict[str, Any]:
    error = source_anchor_file_error(paper_dir, source_record)
    if error:
        raise SemanticReviewDecisionQueueError(
            f"{source_item}: exact source-anchor bytes are unavailable: {error}"
        )
    source_input, source_digest, error = source_semantic_input_bundle(
        source_record,
        require_context_roles=True,
    )
    if error or not source_input:
        raise SemanticReviewDecisionQueueError(
            f"{source_item}: could not construct exact semantic source input: "
            + (error or "empty source input")
        )
    context: dict[str, Any] = {
        "source_locator": str(source_record.get("source_location") or "not recorded"),
        "verbatim_source_input": source_input,
        "verbatim_source_input_sha256": _text_digest(source_input),
        "source_input_bundle_sha256": _sha256(
            source_digest,
            label=f"{source_item} source bundle",
        ),
    }
    approved_contexts, context_error = validated_approved_review_contexts(
        source_record
    )
    if context_error:
        raise SemanticReviewDecisionQueueError(
            f"{source_item}: malformed approved review context: {context_error}"
        )
    if approved_contexts:
        context["approved_review_contexts"] = approved_contexts
    corrected_target, corrected_target_error = approved_corrected_target_review_context(
        source_record
    )
    if corrected_target_error:
        raise SemanticReviewDecisionQueueError(
            f"{source_item}: {corrected_target_error}"
        )
    if corrected_target is not None:
        context["approved_corrected_target"] = corrected_target
    return context


def enrich_queue(
    payload: Mapping[str, Any],
    *,
    paper_dir: Path,
    source_map: Mapping[str, Any],
    material_by_name: Mapping[str, Mapping[str, Any]],
    semantic_target_field: str,
    semantic_target_sha256_field: str,
    declaration_source_field: str,
    declaration_source_sha256_field: str,
    declaration_identity_fields: tuple[str, ...] = (),
    optional_declaration_identity_fields: tuple[str, ...] = (),
    supporting_declarations: Mapping[str, Mapping[str, Any]] | None = None,
    supporting_declaration_names_by_item: Mapping[str, Iterable[str]] | None = None,
) -> dict[str, Any]:
    """Attach exact, deduplicated review material to a routed blank queue."""

    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items:
        raise SemanticReviewDecisionQueueError("decision queue has no routed items")
    source_items = source_map.get("items")
    if not isinstance(source_items, Mapping):
        raise SemanticReviewDecisionQueueError("paper statement map has no source items")

    requested_source_items = sorted(
        {
            str(source_item).strip()
            for raw in raw_items.values()
            if isinstance(raw, Mapping)
            for source_item in raw.get("candidate_source_items", ())
            if str(source_item).strip()
        }
    )
    source_contexts: dict[str, Any] = {}
    for source_item in requested_source_items:
        source_record = source_items.get(source_item)
        if not isinstance(source_record, Mapping):
            raise SemanticReviewDecisionQueueError(
                f"candidate source item `{source_item}` is absent from the statement map"
            )
        source_contexts[source_item] = _source_context(
            paper_dir,
            source_item,
            source_record,
        )

    validated_support: dict[str, dict[str, Any]] = {}
    if supporting_declarations is not None:
        validated_support = _validated_supporting_declarations(
            supporting_declarations
        )
    if supporting_declaration_names_by_item is not None and not validated_support:
        raise SemanticReviewDecisionQueueError(
            "per-item support selections require supporting declarations"
        )
    if supporting_declaration_names_by_item is not None:
        unknown_support_items = sorted(
            set(supporting_declaration_names_by_item) - set(raw_items)
        )
        if unknown_support_items:
            raise SemanticReviewDecisionQueueError(
                "support selections name declarations outside the review queue: "
                + ", ".join(unknown_support_items[:4])
            )

    declaration_contexts: dict[str, Any] = {}
    items: dict[str, Any] = {}
    for raw_name, raw in raw_items.items():
        name = str(raw_name or "").strip()
        if not name or not isinstance(raw, Mapping):
            raise SemanticReviewDecisionQueueError("decision queue has a malformed item")
        material = material_by_name.get(name)
        if not isinstance(material, Mapping):
            raise SemanticReviewDecisionQueueError(
                f"{name}: current exact review material is unavailable"
            )
        target = str(material.get(semantic_target_field) or "").strip()
        target_digest = _sha256(
            material.get(semantic_target_sha256_field),
            label=f"{name} semantic target",
        )
        if not target or _text_digest(target) != target_digest:
            raise SemanticReviewDecisionQueueError(
                f"{name}: Lean semantic display and digest disagree"
            )
        if "⋯" in target:
            raise SemanticReviewDecisionQueueError(
                f"{name}: Lean semantic target contains pretty-printer elision (`⋯`); "
                "expose a readable semantic Spec or source-mapped prerequisite "
                "before issuing a reviewer decision"
            )
        declaration = str(material.get(declaration_source_field) or "").strip()
        declaration_digest = _sha256(
            material.get(declaration_source_sha256_field),
            label=f"{name} declaration source",
        )
        if not declaration or _text_digest(declaration) != declaration_digest:
            raise SemanticReviewDecisionQueueError(
                f"{name}: exact declaration source and digest disagree"
            )
        declaration_identity: dict[str, Any] = {}
        for field in declaration_identity_fields:
            if field not in material:
                raise SemanticReviewDecisionQueueError(
                    f"{name}: declaration identity field `{field}` is unavailable"
                )
            declaration_identity[field] = material[field]
        for field in optional_declaration_identity_fields:
            if field in material:
                declaration_identity[field] = material[field]
        declaration_contexts[name] = {
            "semantic_target": target,
            "semantic_target_sha256": target_digest,
            "declaration_source": declaration,
            "declaration_source_sha256": declaration_digest,
        }
        if declaration_identity:
            declaration_contexts[name]["declaration_identity"] = declaration_identity

        candidates = [
            str(value).strip()
            for value in raw.get("candidate_source_items", ())
            if str(value).strip()
        ]
        selected = str(raw.get("source_item") or "").strip()
        if selected and selected not in candidates:
            raise SemanticReviewDecisionQueueError(
                f"{name}: selected source item is not among its typed candidates"
            )
        item = dict(raw)
        if supporting_declaration_names_by_item is not None:
            raw_support_names = supporting_declaration_names_by_item.get(name, ())
            support_names = sorted(
                {
                    str(value).strip()
                    for value in raw_support_names
                    if str(value).strip()
                }
            )
            unknown_support = sorted(set(support_names) - set(validated_support))
            if unknown_support:
                raise SemanticReviewDecisionQueueError(
                    f"{name}: selected support is absent from the review bundle: "
                    + ", ".join(unknown_support[:4])
                )
            item["supporting_declarations"] = support_names
        items[name] = item

    review_material = {
        "declarations": declaration_contexts,
        "source_items": source_contexts,
    }
    if validated_support:
        review_material["supporting_declarations"] = validated_support
    return {
        **dict(payload),
        "schema": QUEUE_SCHEMA,
        "review_context_protocol": QUEUE_PROTOCOL,
        "comment": (
            "Non-evidence review work queue. Inspect the exact deduplicated source "
            "inputs, expanded Lean semantic targets, declaration code, and every "
            "graph-bound semantic prerequisite below; "
            "then select one typed source item and fill judgment and reason. The "
            "selected source key and declaration key bind that decision to the "
            "canonical material in this file; the receipt writer will reject it "
            "if the source text, source bundle, Lean target, or exact declaration "
            "source has changed before issuance."
        ),
        "items": items,
        "review_material": review_material,
        "review_material_sha256": _canonical_digest(review_material),
    }


def validated_queue_items(
    payload: Mapping[str, Any],
    *,
    paper: str,
) -> dict[str, dict[str, Any]]:
    """Validate embedded review context and return identity-bound item rows."""

    if payload.get("schema") != QUEUE_SCHEMA or payload.get("paper") != paper:
        raise SemanticReviewDecisionQueueError(
            "decision file has the wrong schema or paper"
        )
    if payload.get("review_context_protocol") != QUEUE_PROTOCOL:
        raise SemanticReviewDecisionQueueError(
            "decision file has a stale or missing review-context protocol"
        )
    material = payload.get("review_material")
    if not isinstance(material, Mapping):
        raise SemanticReviewDecisionQueueError("decision file has no review material")
    if _canonical_digest(material) != _sha256(
        payload.get("review_material_sha256"),
        label="review material",
    ):
        raise SemanticReviewDecisionQueueError("embedded review material was modified")
    declarations = material.get("declarations")
    source_items = material.get("source_items")
    if not isinstance(declarations, Mapping) or not isinstance(source_items, Mapping):
        raise SemanticReviewDecisionQueueError("embedded review material is malformed")
    supporting = material.get("supporting_declarations")
    validated_supporting: dict[str, dict[str, Any]] = {}
    supporting_digest = ""
    if supporting is not None:
        validated_supporting = _validated_supporting_declarations(supporting)
        supporting_digest = _canonical_digest(validated_supporting)

    for source_item, raw in source_items.items():
        if not str(source_item).strip() or not isinstance(raw, Mapping):
            raise SemanticReviewDecisionQueueError("embedded source context is malformed")
        text = str(raw.get("verbatim_source_input") or "")
        if not text or _text_digest(text) != _sha256(
            raw.get("verbatim_source_input_sha256"),
            label=f"{source_item} source text",
        ):
            raise SemanticReviewDecisionQueueError(
                f"{source_item}: embedded source text was modified"
            )
        _sha256(raw.get("source_input_bundle_sha256"), label=f"{source_item} source bundle")
        corrected_target = raw.get("approved_corrected_target")
        if corrected_target is not None:
            if not isinstance(corrected_target, Mapping):
                raise SemanticReviewDecisionQueueError(
                    f"{source_item}: embedded approved corrected target is malformed"
                )
            if not str(corrected_target.get("statement") or "").strip():
                raise SemanticReviewDecisionQueueError(
                    f"{source_item}: embedded approved corrected target has no statement"
                )
            _sha256(
                corrected_target.get("corrected_target_review_sha256"),
                label=f"{source_item} approved corrected target",
            )
            if (
                str(corrected_target.get("corrected_target_protocol") or "").strip()
                != CORRECTED_TARGET_REVIEW_PROTOCOL
            ):
                raise SemanticReviewDecisionQueueError(
                    f"{source_item}: embedded approved corrected target has an unknown review protocol"
                )
        approved_contexts = raw.get("approved_review_contexts")
        if approved_contexts is not None:
            if not isinstance(approved_contexts, list) or not approved_contexts:
                raise SemanticReviewDecisionQueueError(
                    f"{source_item}: embedded approved review contexts are malformed"
                )
            for context in approved_contexts:
                if not isinstance(context, Mapping):
                    raise SemanticReviewDecisionQueueError(
                        f"{source_item}: embedded approved review context is malformed"
                    )
                _sha256(
                    context.get("record_sha256"),
                    label=f"{source_item} approved review context",
                )

    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items:
        raise SemanticReviewDecisionQueueError("decision file needs a nonempty items object")
    items: dict[str, dict[str, Any]] = {}
    for raw_name, raw in raw_items.items():
        name = str(raw_name or "").strip()
        context = declarations.get(name)
        if not name or not isinstance(raw, Mapping) or not isinstance(context, Mapping):
            raise SemanticReviewDecisionQueueError("decision item or declaration context is malformed")
        target = str(context.get("semantic_target") or "")
        target_digest = _sha256(
            context.get("semantic_target_sha256"),
            label=f"{name} semantic target",
        )
        if not target or _text_digest(target) != target_digest:
            raise SemanticReviewDecisionQueueError(
                f"{name}: embedded semantic target was modified"
            )
        declaration = str(context.get("declaration_source") or "")
        declaration_digest = _sha256(
            context.get("declaration_source_sha256"),
            label=f"{name} declaration source",
        )
        if not declaration or _text_digest(declaration) != declaration_digest:
            raise SemanticReviewDecisionQueueError(
                f"{name}: embedded declaration source was modified"
            )
        candidates = [
            str(value).strip()
            for value in raw.get("candidate_source_items", ())
            if str(value).strip()
        ]
        selected = str(raw.get("source_item") or "").strip()
        if not selected or selected not in candidates or selected not in source_items:
            raise SemanticReviewDecisionQueueError(
                f"{name}: select one displayed typed source item before judgment"
            )
        current_source = _sha256(
            source_items[selected].get("source_input_bundle_sha256"),
            label=f"{selected} source bundle",
        )
        row = dict(raw)
        # These private derived fields are not reviewer-authored data.  They
        # carry the already-validated canonical context into the issuer so a
        # selected source needs only one key, not manually duplicated hashes.
        row["_reviewed_semantic_target_sha256"] = target_digest
        row["_reviewed_declaration_source_sha256"] = declaration_digest
        row["_reviewed_source_input_bundle_sha256"] = current_source
        row["_reviewed_verbatim_source_input_sha256"] = _sha256(
            source_items[selected].get("verbatim_source_input_sha256"),
            label=f"{selected} source text",
        )
        approved_corrected_target = source_items[selected].get(
            "approved_corrected_target"
        )
        if approved_corrected_target is not None:
            # Preserve the exact correction worksheet shown to the clean
            # reviewer.  A later issuer may accept the distinct corrected
            # disposition only after checking this frozen context against the
            # current approval-pinned source-map target.
            row["_reviewed_approved_corrected_target"] = dict(
                approved_corrected_target
            )
        identity = context.get("declaration_identity")
        if identity is not None:
            if not isinstance(identity, Mapping) or not identity:
                raise SemanticReviewDecisionQueueError(
                    f"{name}: embedded declaration identity is malformed"
                )
            row["_reviewed_declaration_identity"] = dict(identity)
        raw_support_names = raw.get("supporting_declarations")
        if raw_support_names is None:
            item_support_digest = supporting_digest
        else:
            if not isinstance(raw_support_names, list) or not all(
                isinstance(value, str) and value.strip()
                for value in raw_support_names
            ):
                raise SemanticReviewDecisionQueueError(
                    f"{name}: supporting declaration selection is malformed"
                )
            support_names = tuple(sorted(set(raw_support_names)))
            if list(support_names) != raw_support_names:
                raise SemanticReviewDecisionQueueError(
                    f"{name}: supporting declaration selection must be sorted and unique"
                )
            unknown_support = sorted(set(support_names) - set(validated_supporting))
            if unknown_support:
                raise SemanticReviewDecisionQueueError(
                    f"{name}: supporting declaration selection is outside the review bundle"
                )
            item_support_digest = (
                _canonical_digest(
                    {
                        support_name: validated_supporting[support_name]
                        for support_name in support_names
                    }
                )
                if support_names
                else ""
            )
        if item_support_digest:
            row["_reviewed_supporting_declarations_sha256"] = item_support_digest
        items[name] = row
    if set(items) != set(declarations):
        raise SemanticReviewDecisionQueueError(
            "decision items and embedded declaration contexts do not have exact coverage"
        )
    return items


def validate_current_identity(
    name: str,
    decision: Mapping[str, Any],
    current_entry: Mapping[str, Any],
    *,
    semantic_target_sha256_field: str,
    declaration_source_sha256_field: str,
    declaration_identity: Mapping[str, Any] | None = None,
) -> None:
    """Reject time-of-review/time-of-issuance source-semantic identity drift.

    When supplied, current supporting-context identity binds an in-progress
    review to the exact material issued. This is not a historical semantic
    reuse key: unchanged issued judgments retain their separate reuse rules.
    """

    reviewed_target = _sha256(
        decision.get("_reviewed_semantic_target_sha256"),
        label=f"{name} reviewed semantic target",
    )
    current_target = _sha256(
        current_entry.get(semantic_target_sha256_field),
        label=f"{name} current semantic target",
    )
    if reviewed_target != current_target:
        raise SemanticReviewDecisionQueueError(
            f"{name}: Lean semantic target changed after review; prepare a new queue"
        )
    reviewed_declaration = _sha256(
        decision.get("_reviewed_declaration_source_sha256"),
        label=f"{name} reviewed declaration source",
    )
    current_declaration = _sha256(
        current_entry.get(declaration_source_sha256_field),
        label=f"{name} current declaration source",
    )
    if reviewed_declaration != current_declaration:
        raise SemanticReviewDecisionQueueError(
            f"{name}: Lean declaration source changed after review; prepare a new queue"
        )
    if "semantic_supporting_declarations_sha256" in current_entry:
        reviewed_support = str(
            decision.get("_reviewed_supporting_declarations_sha256") or ""
        )
        current_support = str(
            current_entry["semantic_supporting_declarations_sha256"] or ""
        )
        if reviewed_support != current_support:
            raise SemanticReviewDecisionQueueError(
                f"{name}: supporting semantic context changed after review; "
                "prepare a new queue"
            )
    reviewed_source = _sha256(
        decision.get("_reviewed_source_input_bundle_sha256"),
        label=f"{name} reviewed source input",
    )
    current_source = _sha256(
        current_entry.get("source_input_bundle_sha256"),
        label=f"{name} current source input",
    )
    if reviewed_source != current_source:
        raise SemanticReviewDecisionQueueError(
            f"{name}: source input changed after review; prepare a new queue"
        )
    reviewed_source_text = _sha256(
        decision.get("_reviewed_verbatim_source_input_sha256"),
        label=f"{name} reviewed source text",
    )
    current_source_text = str(current_entry.get("verbatim_source_input") or "")
    if not current_source_text or _text_digest(current_source_text) != reviewed_source_text:
        raise SemanticReviewDecisionQueueError(
            f"{name}: verbatim source text changed after review; prepare a new queue"
        )
    if declaration_identity is not None:
        reviewed_identity = decision.get("_reviewed_declaration_identity")
        if not isinstance(reviewed_identity, Mapping):
            raise SemanticReviewDecisionQueueError(
                f"{name}: review queue lacks the required Lean declaration identity; "
                "prepare a new queue"
            )
        if dict(reviewed_identity) != dict(declaration_identity):
            raise SemanticReviewDecisionQueueError(
                f"{name}: Lean declaration identity changed after review; prepare a new queue"
            )
