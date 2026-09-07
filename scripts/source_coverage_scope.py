"""Source-semantic selection policy for ordinary and deep paper coverage.

The ordinary closeout surface deliberately follows the source presentation,
not source-map keys or Lean declaration names. It contains named theoretical
statements, while standalone Formula/Equation/algorithmic-formula presentations
belong to the explicit deep mode. A separate explicit deep mode is available
when a review is intended to classify every prose claim, illustration, figure,
caption, or standalone computational presentation in the source inventory.
"""

from __future__ import annotations

import hashlib
import json
import posixpath
import re
from pathlib import Path
from typing import Any, Mapping

try:
    from source_named_result_index import (
        SOURCE_PRESENTATION_RECONCILIATION_FIELD,
        extract_named_result_presentations,
        reconcile_named_result_presentations,
        reviewed_source_presentation_inventory,
        source_text_uses_conditional_antecedent_subpart_selection,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_named_result_index import (
        SOURCE_PRESENTATION_RECONCILIATION_FIELD,
        extract_named_result_presentations,
        reconcile_named_result_presentations,
        reviewed_source_presentation_inventory,
        source_text_uses_conditional_antecedent_subpart_selection,
    )

try:
    from source_artifact_companion import source_text_companion_validation_issues
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_artifact_companion import source_text_companion_validation_issues

try:
    from source_archive_surface import source_archive_surface_validation_issues
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_archive_surface import source_archive_surface_validation_issues

try:
    from formalization_protocol import (
        coverage_protocol,
        formalization_coverage_protocol_digest,
        formalization_protocol_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.formalization_protocol import (
        coverage_protocol,
        formalization_coverage_protocol_digest,
        formalization_protocol_digest,
    )

try:
    from corrected_target_identity import (
        corrected_target_historical_record_projection,
        corrected_target_record_projection,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.corrected_target_identity import (
        corrected_target_historical_record_projection,
        corrected_target_record_projection,
    )


_COVERAGE_PROTOCOL = coverage_protocol()
_NORMAL_COVERAGE_PROTOCOL = _COVERAGE_PROTOCOL["normal_mode"]
_DEEP_COVERAGE_PROTOCOL = _COVERAGE_PROTOCOL["deep_mode"]
NAMED_THEORETICAL_STATEMENTS = _NORMAL_COVERAGE_PROTOCOL["id"]
DEEP_PAPER_WITH_ALL_PROSE_CLAIMS = _DEEP_COVERAGE_PROTOCOL["id"]
DEFAULT_SOURCE_COVERAGE_MODE = _COVERAGE_PROTOCOL["default_mode"]
# Schema 6 removes direct ``source_defect_ids`` cross-references from the
# source-to-Lean coverage identity.  The dedicated source-proof-fidelity gate
# owns those links and still validates every repaired defect against its exact
# Lean-checked semantic contract.  Schema 5 remains directly readable because
# this is one canonical identity-schema transition, not an engine-pair bridge.
SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA = 6
PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA = 5
LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA = 4
# The aggregate raw-cache projection makes the same ownership correction.
# Existing raw receipts remain reviewable through the current semantic graph;
# this cache digest is only a fast path and is never acceptance authority.
SOURCE_MAP_CACHE_SEMANTIC_DIGEST_SCHEMA = 3
PREVIOUS_SOURCE_MAP_CACHE_SEMANTIC_DIGEST_SCHEMA = 2
LEGACY_SOURCE_MAP_CACHE_SEMANTIC_DIGEST_SCHEMA = 1
# The strict source-to-Spec lane owns these receipt fields.  They are refreshed
# from Lean only after it has revalidated the already-reviewed atom bindings
# and closure dispositions, so they must not reopen an independent raw
# source-record review.  This is deliberately an exact schema field list:
# unknown correspondence metadata remains an identity input.
SOURCE_RECORD_DERIVED_CORRESPONDENCE_RECEIPT_FIELDS = frozenset(
    {
        "source_atoms_sha256",
        "spec_closure_sha256",
        "spec_surface_sha256",
        "closure_environment_sha256",
        "item_identity_sha256",
    }
)
_SOURCE_RECORD_CORRESPONDENCE_REQUIRED_FIELDS = frozenset(
    {
        "schema",
        "source_atom_bindings",
        "closure_node_dispositions",
        *SOURCE_RECORD_DERIVED_CORRESPONDENCE_RECEIPT_FIELDS,
    }
)
_SOURCE_RECORD_CORRESPONDENCE_SCHEMA = 1
_SOURCE_RECORD_CORRESPONDENCE_FIELD = "source_spec_correspondence"
CORRECTED_SOURCE_STATEMENT_STATUS = "corrected_source_statement"
USER_APPROVED_SCOPE_EXCLUSION_KEY = "user_approved_scope_exclusion"
SOURCE_PRESENTATION_ALIAS_FIELD = "source_presentation_alias"
SOURCE_PRESENTATION_ALIAS_SCHEMA = 1


def explicit_raw_source_spec_screening_requested(
    status_payload: object,
    source_map_payload: object | None = None,
) -> bool:
    """Recognize every explicit spelling of the strict v11 review lane.

    Source-to-Spec correspondence, direct raw-source screening, and the
    predecessor theorem-realization switch all select the same semantic
    protocol. Consumers must not key their behavior to only one spelling or a
    paper can pass the accepting gate while its planner, packet, or report
    falls back to legacy work.
    """

    if isinstance(source_map_payload, Mapping):
        schema = source_map_payload.get("source_spec_correspondence_schema")
        if (
            isinstance(schema, int)
            and not isinstance(schema, bool)
            and schema == _SOURCE_RECORD_CORRESPONDENCE_SCHEMA
        ):
            return True
    if not isinstance(status_payload, Mapping):
        return False
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, Mapping):
        return False
    if (
        review_surface.get("require_source_spec_correspondence") is True
        or review_surface.get("require_v11_raw_source_spec_screening") is True
    ):
        return True
    statement_review = review_surface.get("llm_statement_review")
    if not isinstance(statement_review, Mapping):
        return False
    # This historical explicit opt-in selects the current lane; it does not
    # authorize reuse of a judgment issued under the older prompt contract.
    if str(statement_review.get("required_prompt_version") or "").strip() == (
        "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-"
        "claim-atoms-v3"
    ):
        return True
    realization_schema = statement_review.get(
        "require_theorem_realization_contract_schema"
    )
    return bool(
        statement_review.get("require_theorem_realization_contract") is True
        or (
            isinstance(realization_schema, int)
            and not isinstance(realization_schema, bool)
            and realization_schema == 1
        )
    )
SOURCE_PRESENTATION_ALIAS_RELATION = "repeated_source_presentation"
SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD = "label_relation"
SOURCE_PRESENTATION_ALIAS_SAME_VISIBLE_LABEL = "same_visible_label"
SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT = (
    "source_explicit_renumbered_restatement"
)
SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD = (
    "source_restatement_evidence"
)
SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD = "prose_definition_presentations"
SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD = (
    "discovered_prose_definition_sha256"
)
SOURCE_PROSE_DEFINITION_PRESENTATION_SCHEMA = 1
SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD = (
    "source_prose_definition_reconciliation"
)
SOURCE_PROSE_DEFINITION_RECONCILIATION_SCHEMA = 2
SOURCE_PROSE_DEFINITION_RECONCILIATION_RELATION = (
    "source_item_represents_prose_definition"
)
SOURCE_PROSE_DEFINITION_RECONCILIATION_JUDGMENT = "semantically_equivalent"
SOURCE_PROSE_DEFINITION_ENTITY_KINDS = frozenset({"object", "predicate"})
SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES = frozenset({"agent", "human", "model"})
SOURCE_STANDARD_TERM_INTERPRETATION_FIELD = "source_standard_term_interpretation"
SOURCE_STANDARD_TERM_INTERPRETATION_SCHEMA = 1
SOURCE_STANDARD_TERM_INTERPRETATION_RELATION = (
    "source_uses_standard_term_without_source_definition"
)
SOURCE_STANDARD_TERM_INTERPRETATION_JUDGMENT = (
    "standard_interpretation_matches_source_use"
)
SOURCE_PROSE_DEFINITION_NORMAL_SCOPE = "normal_named_theory_definition"
SOURCE_PROSE_DEFINITION_REPEATED_SCOPE = "repeated_normal_definition"
SOURCE_PROSE_DEFINITION_REPETITION_JUDGMENT = "semantically_equivalent_restatement"
SOURCE_PROSE_DEFINITION_EXCLUSION_JUDGMENT = "excluded_from_normal_named_theory"
SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD = "normal_scope_exclusion_approval"
SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_SCHEMA = 1
SOURCE_PROSE_DEFINITION_EXCLUDED_SCOPE_DISPOSITIONS = frozenset(
    {
        "local_proof_notation",
        "computational_definition",
        "deep_only_definition",
    }
)
SOURCE_PROSE_DEFINITION_SCOPE_DISPOSITIONS = frozenset(
    {
        SOURCE_PROSE_DEFINITION_NORMAL_SCOPE,
        SOURCE_PROSE_DEFINITION_REPEATED_SCOPE,
        *SOURCE_PROSE_DEFINITION_EXCLUDED_SCOPE_DISPOSITIONS,
    }
)
VALID_SOURCE_PRESENTATION_ALIAS_LABEL_RELATIONS = frozenset(
    {
        SOURCE_PRESENTATION_ALIAS_SAME_VISIBLE_LABEL,
        SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT,
    }
)
SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION = (
    "source_declared_open_nonresult_observation"
)
SOURCE_RESOLVED_WITHIN_PAPER_OBSERVATION = (
    "source_resolved_within_paper_observation"
)
VALID_SOURCE_COVERAGE_MODES = frozenset(
    {NAMED_THEORETICAL_STATEMENTS, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS}
)

# These are recognized source-presentation categories. They intentionally say
# nothing about a source-map key or the spelling of a Lean declaration. The
# normal named-theory selector below is deliberately narrower than this set.
NAMED_THEORETICAL_SOURCE_KINDS = frozenset(
    set(_NORMAL_COVERAGE_PROTOCOL["included_source_kinds"])
    | set(_NORMAL_COVERAGE_PROTOCOL["deep_only_standalone_source_kinds"])
)
"""All recognized theoretical/display categories, not the normal selector."""

# The theorem-realization lane is narrower than ordinary paper coverage.  It
# follows source presentation categories, rather than map keys or Lean names:
# named results advertised as theorem-like claims (and an in-scope mathematical
# example) need a source-to-elaborated-statement realization check.  Definitions,
# model assumptions, and support rows still receive their ordinary source and
# raw-record checks, but are not artificial theorem-Spec obligations.
THEOREM_REALIZATION_SOURCE_KINDS = frozenset(
    {"lemma", "theorem", "proposition", "corollary", "claim", "runtime_claim", "example"}
)
THEOREM_REALIZATION_NONCLAIM_STATUSES = frozenset(
    {"added_audit_row", "quarantined_source_defect", "support_only"}
)

# Keep the source-specific explanation close to the machine policy without
# duplicating the list itself.  A labelled algorithm can be semantically
# important, but it is an independent coverage item only in deep mode; normal
# mode still audits it when a selected theorem depends on it.
_RECOGNIZED_THEORETICAL_SOURCE_KINDS = frozenset(
    {
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "claim",
        "definition",
        "predicate_vocabulary",
        "formula",
        "equation",
        # A source-labelled Algorithm is a named operational definition.  Its
        # correctness or runtime claim must not disappear merely because it is
        # presented as pseudocode rather than a theorem environment.
        "algorithm",
        "algorithmic_formula",
        "runtime_claim",
        "assumption",
        # A source may present its governing model as a visibly numbered
        # condition/setup rather than an `Assumption` environment. These are
        # normal-scope only when their own presentation is visibly named.
        "condition",
        "model",
    }
)
if NAMED_THEORETICAL_SOURCE_KINDS != _RECOGNIZED_THEORETICAL_SOURCE_KINDS:
    raise RuntimeError(
        "formalization protocol theoretical source kinds disagree with the source parser"
    )

# A source map can retain a standalone formula/equation/algorithm presentation
# for source fidelity, deep review, and later repair work. It is not a
# paper-facing named theoretical statement in the default closeout mode. This
# is a source-presentation policy, not a classification of the Lean function
# that happens to implement the display.
NORMAL_SCOPE_EXCLUDED_STANDALONE_SOURCE_KINDS = frozenset(
    _NORMAL_COVERAGE_PROTOCOL["deep_only_standalone_source_kinds"]
)
_NAMED_THEORETICAL_ALWAYS_SOURCE_KINDS = frozenset(
    {
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "definition",
        "predicate_vocabulary",
    }
)
_LABEL_REQUIRED_NAMED_SOURCE_KINDS = frozenset(
    _NORMAL_COVERAGE_PROTOCOL["label_required_source_kinds"]
)

# These are presentation categories that a map may retain for explicit deep
# review.  They are intentionally not ordinary named-theory obligations unless
# their own source text presents a labelled theoretical result.
DEEP_ONLY_SOURCE_KINDS = frozenset(
    {
        "example",
        "remark",
        "prose_assertion",
        "figure",
        "table",
        "caption",
        "figure_caption",
        "table_caption",
        "simulation",
        "empirical_observation",
        "computational_observation",
        "implementation_measurement",
        # Unnumbered source-model exposition and an explicitly constructed
        # model carrier may support selected claims without themselves being
        # a separate named paper result.  A selected mathematical use must be
        # represented by a typed source-to-Lean route, not inferred from these
        # inventory labels.
        "model_context",
        "model_construction",
    }
)
NAMED_OPEN_SOURCE_KINDS = frozenset({"open_problem"})
KNOWN_SOURCE_PRESENTATION_KINDS = (
    NAMED_THEORETICAL_SOURCE_KINDS
    | DEEP_ONLY_SOURCE_KINDS
    | NAMED_OPEN_SOURCE_KINDS
)

_NAMED_THEORETICAL_PRESENTATION_RE = re.compile(
    r"""
    \b(?:
        theorem|proposition|lemma|corollary|claim|definition|equation|formula|
        algorithm|assumption|condition|model
    )\b
    (?:\s*[-:.~()]|\s+\d|\s+[A-Z](?:\.\d+)*)
    """,
    re.IGNORECASE | re.VERBOSE,
)
_ISO_LIKE_TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z$"
)

# Direct source routes belong to one canonical source presentation.  A repeated
# proof-section restatement retains its own source anchor but must not create a
# second direct Lean target merely because the same result is printed again.
_DIRECT_SOURCE_ROUTE_FIELDS = (
    "lean_declarations",
    "proof_lean_declarations",
    "spec_lean_declarations",
)

_NAMED_THEORETICAL_HEADING_RE = re.compile(
    r"""
    ^\s*(?:
        \\begin\s*\{\s*(?:theorem|proposition|lemma|corollary|claim|definition)\*?\s*\}
      | (?:theorem|proposition|lemma|corollary|claim|definition|equation|formula|
           algorithm|assumption|condition|model)\b
        (?:\s*[-:.~()]|\s+\d|\s+[A-Z](?:\.\d+)*)
    )
    """,
    re.IGNORECASE | re.MULTILINE | re.VERBOSE,
)

_NAMED_OPERATIVE_PRESENTATION_RE = re.compile(
    r"""
    ^\s*(?:
        (?:equation|eq\.?|formula|algorithm|assumption|condition|model)\b
        \s*(?:[-:.~]|\()?\s*(?:[A-Z](?:\.\d+)*|[A-Z]?\d+(?:\.\d+)*)(?:\))?
        (?=\s*(?:$|[.:)\]\-\N{EN DASH}\N{EM DASH}]))
    )
    """,
    re.IGNORECASE | re.MULTILINE | re.VERBOSE,
)

# Some sources introduce a named item in running text rather than putting a
# delimiter after its label, e.g. ``Formula A gives ...`` or ``Condition 2
# requires ...``.  The label itself is still source presentation evidence.  A
# lower-case descriptive phrase such as ``the model has ...`` does not match.
_NAMED_LABELLED_ITEM_PREFIX_RE = re.compile(
    r"""
    ^\s*(?:equation|eq\.?|formula|algorithm|assumption|condition|model)\b
    \s+(?:\(?[A-Z](?:\.\d+)*\)?|\(?\d+(?:\.\d+)*\)?)\b
    """,
    re.IGNORECASE | re.MULTILINE | re.VERBOSE,
)

# Source-map routes are important for locating and validating a Lean endpoint,
# but they are not part of the source statement's mathematical identity.  The
# coverage sidecar separately pins every selected elaborated Lean signature.
_NAVIGATION_ONLY_ROUTE_FIELDS = frozenset(
    {
        "aliases",
        "lean_declarations",
        "proof_lean_declarations",
        "support_lean_declarations",
        "spec_lean_declarations",
        "evidence_declaration",
        "spec_declaration",
        # Source-claim atoms carry an exact Lean endpoint solely so audit
        # tooling can resolve a reviewed surface.  It is route navigation, not
        # source semantics: the atom's own semantic_claim and byte-pinned
        # source span remain in the source-content identity.
        "reviewed_lean_route",
        "review_rows",
        "source_routes",
    }
)

# The canonical artifact pin is an aggregate integrity obligation.  It must be
# checked on every closeout, but it is not the mathematical identity of each
# individual source item: changing an unrelated page in a source PDF should
# not reopen a byte-identical theorem quote and unchanged Lean proposition.
# The current byte-anchor validator, not this semantic projection, verifies
# current quote path/range/hash.  Keeping locator movement out of the digest
# lets an unchanged quoted statement retain its judgment after an unrelated
# source edit shifts line numbers.
_AGGREGATE_ONLY_ARTIFACT_FIELDS = frozenset(
    {
        "source_artifact_path",
        "source_artifact_sha256",
        "canonical_source_artifact_path",
        "canonical_source_artifact_sha256",
    }
)
_SOURCE_ITEM_NAVIGATION_ONLY_FIELDS = frozenset(
    {
        "source_location",
        "source_url",
        "source_text_file",
        "start_line",
        "end_line",
        "source_item",
        # Dashboard normalization carries the map key for navigation. The key
        # is not source content and must not make an otherwise identical source
        # claim receive a new semantic identity after a rename.
        "source_item_key",
        # A component's parent map key is a lookup handle. The component's
        # clause, exact source anchors, and structural partition pins carry
        # its semantic identity across a parent-key rename.
        "source_component_of",
    }
)

# ``source_status`` usually records the repository's current bookkeeping
# assessment (for example, whether a once-partial derivation has since been
# repaired).  It is not source text or a formalization premise.  A small set
# of status values is nevertheless consumed by the source-route policy below:
# it can turn a result route into a support route, quarantine a defect, or
# suppress a support-only vocabulary row. Model-convention routing is instead
# tied only to a source presentation explicitly classified as a ``model`` or
# ``assumption``. ``model_convention_ids`` are dependency/assumption pins; they
# cannot reclassify a theorem or lemma conclusion. The cache projection
# therefore omits ordinary status wording, but retains a
# normalized policy receipt when deleting the direct field would change one of
# those effects or when a legacy phrase-driven route needs a one-time refresh.
# Any source note, boundary, target, or other new metadata remains fail-closed.
_SOURCE_ITEM_ADMINISTRATIVE_METADATA_FIELDS = frozenset(
    {
        "source_status",
        # Independent source-kind review credentials authorize the source-kind
        # classification but do not change the classified source statement.
        # Their dedicated repository validator remains mandatory; keeping the
        # receipt payload out of the source-content digest prevents a reviewer,
        # validator, or timestamp refresh from reopening unchanged mathematics.
        "source_kind_validator",
        "source_kind_validated_at",
        "source_kind_human_approved",
        "source_kind_human_reviewer",
        "source_kind_human_reviewed_at",
        # Source-proof fidelity owns these cross-references and validates that
        # every repaired defect reaches an exact Lean-checked semantic
        # contract. Adding or renaming that bookkeeping link does not change
        # the source presentation or its source-to-Lean coverage judgment.
        # Corrected targets retain their governing defect identities inside
        # the separately preserved `corrected_target` payload.
        "source_defect_ids",
        # A byte-validated reconciliation core controls only the named-result
        # closeout consumer. It is not a source statement, premise, route, or
        # source-record semantic input; its dedicated validator remains
        # mandatory before it can select an item.
        SOURCE_PRESENTATION_RECONCILIATION_FIELD,
    }
)
_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD = "source_named_result_inventory_review"
_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_AUDIT_ONLY_FIELDS = frozenset(
    {
        "schema",
        "complete",
        "validator",
        "method",
        "validated_at",
        "source_artifact_sha256",
        "discovered_named_result_sha256",
        "discovered_candidate_presentation_sha256",
        SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD,
        # The policy-aware closeout owner binds this complete partition in
        # source assurance and terminal review material. It classifies review
        # intensity but does not change an exact source item's mathematical
        # source-to-Lean judgment.
        "source_region_partition",
    }
)
SOURCE_STATUS_POLICY_SCHEMA = 1
SOURCE_MODEL_CONVENTION_KINDS = frozenset({"assumption", "model"})
SOURCE_VOCABULARY_KINDS = frozenset({"definition", "predicate_vocabulary"})
# Positive presentation kinds whose non-Prop realization components can be
# discharged by an exact, current semantic-model/domain correspondence.  An
# assumption remains outside this set even when it is carried in model prose:
# proposition-bearing assumptions require an exact source-claim route.
SOURCE_DOMAIN_PRESENTATION_KINDS = frozenset({"model"}) | SOURCE_VOCABULARY_KINDS
SOURCE_DIRECT_ENDPOINT_KINDS = frozenset(
    {
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "claim",
        "runtime_claim",
        "definition",
        "predicate_vocabulary",
    }
)
QUARANTINED_SOURCE_DEFECT_STATUS = "quarantined_source_defect"
SUPPORT_ONLY_SOURCE_STATUS = "support_only"
_SOURCE_ANCHOR_NAVIGATION_ONLY_FIELDS = frozenset(
    {
        "path",
        "line_start",
        "line_end",
        "quoted_text_sha256",
    }
)

_PRESENTATION_TEXT_FIELDS = (
    "title",
    "statement",
    "source_evidence",
    "source_note",
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_TEX_ENVIRONMENT_NAME_RE = re.compile(r"^[A-Za-z@][A-Za-z0-9_@-]*$")
_TEX_BEGIN_ENVIRONMENT_RE = re.compile(
    r"^\\begin\s*\{\s*(?P<environment>[A-Za-z@][A-Za-z0-9_@-]*)(?:\*)?\s*\}",
    re.IGNORECASE,
)
_SOURCE_KIND_VISIBLE_TITLES = {
    "theorem": ("theorem",),
    "proposition": ("proposition",),
    "lemma": ("lemma",),
    "corollary": ("corollary",),
    "definition": ("definition",),
    "predicate_vocabulary": ("definition",),
}


def _normalized_source_kind(item: Mapping[str, object]) -> str:
    return str(item.get("source_kind") or "").strip().lower()


def _normalized_direct_source_status(
    item: Mapping[str, object], *, include_direct_source_status: bool
) -> str:
    if not include_direct_source_status:
        return ""
    return str(item.get("source_status") or "").strip().lower()


def _source_route_values_present(value: object) -> bool:
    """Match dashboard route-list normalization without importing its UI module."""

    if value is None:
        return False
    values = value if isinstance(value, (list, tuple, set)) else str(value).split(",")
    return any(str(entry or "").strip() for entry in values)


def source_item_effective_route_policy(
    item: object,
    *,
    include_direct_source_status: bool = True,
) -> dict[str, object]:
    """Return the status-sensitive source-routing policy for one map item.

    This is intentionally a policy summary, not a raw-status mirror.  It
    records the semantic routing effects that consumers actually use: direct
    and component eligibility, model-convention/support lanes, theorem-endpoint
    treatment, defect quarantine, and the narrow external-vocabulary exception.
    Map keys and Lean declaration names are absent by construction.
    """

    source_item = item if isinstance(item, Mapping) else {}
    source_kind = _normalized_source_kind(source_item)
    source_status = _normalized_direct_source_status(
        source_item,
        include_direct_source_status=include_direct_source_status,
    )
    # A model-convention dependency can be necessary to establish a named
    # theorem without turning that theorem into a model premise.  Route role
    # follows the source presentation itself, never a dependency-id list.
    is_model_convention = source_kind in SOURCE_MODEL_CONVENTION_KINDS
    is_quarantined_source_defect = (
        source_status == QUARANTINED_SOURCE_DEFECT_STATUS
    )
    is_support_only = source_status == SUPPORT_ONLY_SOURCE_STATUS
    is_source_declared_open_nonresult = bool(
        source_kind == "open_problem"
        and source_item.get("claim_bearing") is False
        and str(source_item.get("source_scope_classification") or "")
        .strip()
        .lower()
        == SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
        and str(source_item.get("coverage_status") or "").strip().lower()
        == "source_declared_open"
        and str(source_item.get("protocol_role") or "").strip().lower()
        == "source_declared_open"
    )
    is_source_resolved_within_paper = bool(
        source_kind == "open_problem"
        and source_item.get("claim_bearing") is False
        and str(source_item.get("source_scope_classification") or "")
        .strip()
        .lower()
        == SOURCE_RESOLVED_WITHIN_PAPER_OBSERVATION
        and str(source_item.get("coverage_status") or "").strip().lower()
        == "subsumed_by_selected_result"
        and str(source_item.get("protocol_role") or "").strip().lower()
        == "subsumed_by_selected_result"
        and bool(str(source_item.get("subsumed_by_source_item") or "").strip())
    )
    blocks_ordinary_result_route = (
        is_model_convention
        or is_quarantined_source_defect
        or is_support_only
        or is_source_declared_open_nonresult
        or is_source_resolved_within_paper
    )
    external_support_only_vocabulary = (
        is_support_only
        and source_kind in SOURCE_VOCABULARY_KINDS
        and _source_route_values_present(source_item.get("support_lean_declarations"))
        and not _source_route_values_present(source_item.get("lean_declarations"))
        and bool(
            str(source_item.get("source_note") or "").strip() or source_status
        )
    )
    return {
        "allows_direct_route": not blocks_ordinary_result_route,
        "allows_source_component_route": not blocks_ordinary_result_route,
        "allows_source_model_convention_route": is_model_convention,
        "allows_defect_or_remark_support_route": (
            is_quarantined_source_defect
            or is_support_only
            or is_source_declared_open_nonresult
            or is_source_resolved_within_paper
            or source_kind == "remark"
        ),
        "direct_source_endpoint_required": (
            source_kind in SOURCE_DIRECT_ENDPOINT_KINDS
            and not (is_quarantined_source_defect or is_support_only)
        ),
        "is_model_convention": is_model_convention,
        "is_quarantined_source_defect": is_quarantined_source_defect,
        "is_support_only": is_support_only,
        "is_source_declared_open_nonresult": is_source_declared_open_nonresult,
        "is_source_resolved_within_paper": is_source_resolved_within_paper,
        "external_support_only_vocabulary": external_support_only_vocabulary,
    }


def _legacy_source_item_status_route_policy(item: object) -> dict[str, object]:
    """Reproduce the pre-policy phrase route solely for cache-transition safety.

    This is never used to route new evidence. It exists only to identify an
    old receipt that was generated while a free status phrase containing
    ``convention`` could alter source routing. The current structured policy
    must differ before a transition marker is emitted, so ordinary historical
    receipts remain reusable.
    """

    current = source_item_effective_route_policy(
        item, include_direct_source_status=True
    )
    if not isinstance(item, Mapping):
        return current
    source_kind = _normalized_source_kind(item)
    source_status = _normalized_direct_source_status(
        item, include_direct_source_status=True
    )
    legacy_model_convention = source_kind in SOURCE_MODEL_CONVENTION_KINDS or (
        "convention" in source_status
    )
    if legacy_model_convention == bool(current["is_model_convention"]):
        return current

    is_quarantined_source_defect = bool(current["is_quarantined_source_defect"])
    is_support_only = bool(current["is_support_only"])
    blocks_ordinary_result_route = (
        legacy_model_convention or is_quarantined_source_defect or is_support_only
    )
    legacy = dict(current)
    legacy.update(
        {
            "allows_direct_route": not blocks_ordinary_result_route,
            "allows_source_component_route": not blocks_ordinary_result_route,
            "allows_source_model_convention_route": legacy_model_convention,
            "is_model_convention": legacy_model_convention,
        }
    )
    return legacy


def source_item_direct_status_policy_projection(item: object) -> dict[str, object] | None:
    """Return a cache pin only when direct status changes effective policy.

    The normal ``source_status`` field remains deliberately absent from the
    cache and per-item semantic identities. This function compares the current
    structured policy both with the direct field ignored and with the narrow
    legacy phrase policy. It adds no projection for ordinary wording, including
    a model item redundantly labelled as a convention, preserving byte-identical
    cache receipts for previously safe work. A malformed direct value also
    fails closed rather than being silently treated as an administrative label.
    """

    if not isinstance(item, Mapping) or "source_status" not in item:
        return None
    raw_status = item.get("source_status")
    current = source_item_effective_route_policy(item, include_direct_source_status=True)
    without_status = source_item_effective_route_policy(
        item, include_direct_source_status=False
    )
    legacy = _legacy_source_item_status_route_policy(item)
    if (
        isinstance(raw_status, str)
        and current == without_status
        and current == legacy
    ):
        return None
    projection: dict[str, object] = {
        "schema": SOURCE_STATUS_POLICY_SCHEMA,
        "effective_route_policy": current,
    }
    if legacy != current:
        # A raw receipt created under the former free-phrase behavior cannot
        # be reused for the new structured interpretation. The old policy is
        # recorded only as a boolean route summary, never as status prose.
        projection["legacy_status_route_policy"] = legacy
    if not isinstance(raw_status, str):
        projection["direct_source_status_shape"] = type(raw_status).__name__
    return projection


def _source_anchor_semantic_projection(value: object) -> object:
    """Drop source-anchor navigation while preserving its literal text.

    An anchor's path/range/hash is a current-byte verification mechanism.  The
    exact quote remains source content, and is checked against its new range
    before semantic cache reuse.  Unknown anchor metadata stays fail-closed.
    """

    if isinstance(value, dict):
        return {
            str(raw_key): _source_anchor_semantic_projection(raw_value)
            for raw_key, raw_value in value.items()
            if str(raw_key).strip().lower()
            not in _SOURCE_ANCHOR_NAVIGATION_ONLY_FIELDS
        }
    if isinstance(value, list):
        return [_source_anchor_semantic_projection(item) for item in value]
    if isinstance(value, tuple):
        return [_source_anchor_semantic_projection(item) for item in value]
    return value


def _source_prose_definition_reconciliation_semantic_projection(
    value: object,
) -> object:
    """Keep immutable binding pins while omitting audit credential wording."""

    if not isinstance(value, Mapping):
        return value
    semantic_fields = (
        "schema",
        "relation",
        "presentation_sha256",
        "source_item_statement_sha256",
        "judgment",
    )
    return {field: value.get(field) for field in semantic_fields}


def _source_standard_term_interpretation_semantic_projection(
    value: object,
) -> object:
    """Keep standard-term meaning while omitting reviewer-only credentials.

    A standard-term interpretation supplies source-semantic content absent from
    the paper's prose. Its literal source use, source-map statement pin, and
    mathematical interpretation therefore remain raw-cache inputs. The
    reviewer explanation and identity are checked by the dedicated validator
    but can be refreshed without reopening unchanged mathematical evidence.
    """

    if not isinstance(value, Mapping):
        return value
    semantic_fields = (
        "schema",
        "relation",
        "source_term",
        "source_provided_definition",
        "source_item_statement_sha256",
        "standard_interpretation",
        "judgment",
    )
    projected = {field: value.get(field) for field in semantic_fields}
    projected["source_term_use_anchor"] = _source_anchor_semantic_projection(
        value.get("source_term_use_anchor")
    )
    return projected


def _source_record_refreshable_correspondence(value: object) -> bool:
    """Return whether one exact correspondence belongs to the strict lane.

    The raw source-record lane is not allowed to interpret a source-to-Spec
    mapping. It can omit a correspondence only when the enclosing object has
    the exact current schema shape. Any malformed object, unknown field, or
    non-literal lookalike stays in the identity and therefore fails closed.
    The strict correspondence lane independently validates every binding and
    disposition against Lean's live closure.
    """

    if not isinstance(value, Mapping) or set(value) != _SOURCE_RECORD_CORRESPONDENCE_REQUIRED_FIELDS:
        return False
    schema = value.get("schema")
    if (
        not isinstance(schema, int)
        or isinstance(schema, bool)
        or schema != _SOURCE_RECORD_CORRESPONDENCE_SCHEMA
        or not isinstance(value.get("source_atom_bindings"), list)
        or not isinstance(value.get("closure_node_dispositions"), list)
    ):
        return False
    return all(
        isinstance(value.get(field), str)
        and _SHA256_RE.fullmatch(str(value[field]).strip())
        for field in SOURCE_RECORD_DERIVED_CORRESPONDENCE_RECEIPT_FIELDS
    )


def source_record_source_item_projection(item: object) -> object:
    """Project one map item for raw source-record identity only.

    This is intentionally narrower than the general source-statement
    projection. Source-record generation never consumes source-to-Spec
    correspondence; strict closeout owns that evidence separately. Omit the
    complete field only when its exact current schema identifies it as
    strict-lane evidence. Preserve every malformed, future-shaped, or
    lookalike field so schema drift fails closed.
    """

    if not isinstance(item, Mapping):
        return item
    projected: dict[str, object] = {str(key): value for key, value in item.items()}
    correspondence = item.get(_SOURCE_RECORD_CORRESPONDENCE_FIELD)
    if not _source_record_refreshable_correspondence(correspondence):
        return projected
    projected.pop(_SOURCE_RECORD_CORRESPONDENCE_FIELD, None)
    return projected


def _source_record_identity_canonical_payload(value: object) -> object:
    """Canonicalize the order-insensitive raw source-item identity payload."""

    if isinstance(value, Mapping):
        return {
            str(key): _source_record_identity_canonical_payload(child)
            for key, child in sorted(value.items(), key=lambda item: str(item[0]))
        }
    if isinstance(value, list):
        children = [_source_record_identity_canonical_payload(child) for child in value]
        return sorted(
            children,
            key=lambda child: json.dumps(
                child, ensure_ascii=True, sort_keys=True, separators=(",", ":")
            ),
        )
    if isinstance(value, tuple):
        return _source_record_identity_canonical_payload(list(value))
    return value


def source_record_source_item_record_sha256(item: object) -> str:
    """Return the exact raw-audit map-item provenance digest.

    It is independent of the legacy ``source_map_item_record_digest`` because
    that generic helper also authenticates response associations and list
    payloads.  Only a source-map item receives the narrowly scoped
    correspondence-receipt projection above.
    """

    encoded = json.dumps(
        _source_record_identity_canonical_payload(
            source_record_source_item_projection(item)
        ),
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def source_record_source_item_semantic_sha256(item: object, mode: str) -> str:
    """Return the raw lane's keyless source semantic identity.

    The general source-item digest continues to bind correspondence evidence
    for consumers that own it.  Raw source-record reuse instead uses this
    projection, because a validated update to the five derived closure hashes
    has no source claim or raw-review consequence.
    """

    projected = source_record_source_item_projection(item)
    if not isinstance(projected, Mapping):
        return ""
    return source_item_coverage_sha256(dict(projected), mode)


def source_record_source_item_supported_identity_sha256s(
    item: object, mode: str
) -> frozenset[tuple[str, str]]:
    """Return equivalent canonical encodings of one raw source-item identity.

    Current raw receipts omit a complete recognized correspondence because the
    raw generator does not consume it. Earlier receipts retained its semantic
    fields, either literally or with an exact whole-Spec carrier normalized to
    a sentinel. Reconstruct those encodings from the current correspondence so
    unchanged raw review can migrate without an engine-pair bridge. The strict
    lane must still validate the current correspondence independently.

    This is an encoding-normalization rule, not an engine-version bridge: the
    accepted identities are derived directly from the current item, and the
    caller must still validate the current source-to-Spec correspondence lane.
    """

    canonical_record = source_record_source_item_record_sha256(item)
    canonical_semantic = source_record_source_item_semantic_sha256(item, mode)
    identities = {(canonical_record, canonical_semantic)}
    if not isinstance(item, Mapping):
        return frozenset(identities)
    correspondence = item.get(_SOURCE_RECORD_CORRESPONDENCE_FIELD)
    if not _source_record_refreshable_correspondence(correspondence):
        return frozenset(identities)
    assert isinstance(correspondence, Mapping)
    literal_projection: dict[str, object] = {
        str(key): value for key, value in item.items()
    }
    prior_correspondence = {
        str(key): value
        for key, value in correspondence.items()
        if str(key) not in SOURCE_RECORD_DERIVED_CORRESPONDENCE_RECEIPT_FIELDS
    }
    literal_projection[_SOURCE_RECORD_CORRESPONDENCE_FIELD] = prior_correspondence
    literal_encoded = json.dumps(
        _source_record_identity_canonical_payload(literal_projection),
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    identities.add(
        (
            hashlib.sha256(literal_encoded).hexdigest(),
            source_item_coverage_sha256(literal_projection, mode),
        )
    )

    root_surface = str(correspondence.get("spec_surface_sha256") or "").strip().lower()
    normalized_projection = dict(literal_projection)
    normalized_correspondence = dict(prior_correspondence)
    normalized_bindings: list[object] = []
    for raw_binding in correspondence.get("source_atom_bindings", []):
        if not isinstance(raw_binding, Mapping):
            normalized_bindings.append(raw_binding)
            continue
        binding = {str(key): value for key, value in raw_binding.items()}
        raw_components = raw_binding.get("spec_component_sha256s")
        components = (
            [str(value).strip().lower() for value in raw_components]
            if isinstance(raw_components, list)
            else []
        )
        if components == [root_surface]:
            binding["spec_component_sha256s"] = ["complete_spec_surface_v1"]
        normalized_bindings.append(binding)
    normalized_correspondence["source_atom_bindings"] = normalized_bindings
    normalized_projection[_SOURCE_RECORD_CORRESPONDENCE_FIELD] = normalized_correspondence
    normalized_encoded = json.dumps(
        _source_record_identity_canonical_payload(normalized_projection),
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    identities.add(
        (
            hashlib.sha256(normalized_encoded).hexdigest(),
            source_item_coverage_sha256(normalized_projection, mode),
        )
    )
    return frozenset(identities)


def source_record_human_review_semantic_sha256(item: object, mode: str) -> str:
    """Return the source meaning owned by the raw human-review lane.

    ``source_spec_correspondence`` is independently authenticated by the
    strict source-to-Spec lane.  A refresh of that complete, recognized
    receipt must therefore neither manufacture nor invalidate a judgment
    about the source premise itself.  Keep malformed or future-shaped values
    in the digest so an unrecognized correspondence evolution still fails
    closed instead of being silently projected away.

    This identity is for cross-receipt human-response transport only.  The raw
    receipt continues to authenticate its exact map record and its own stored
    semantic identity before this narrower comparison is used.
    """

    if not isinstance(item, Mapping):
        return ""
    projected: dict[str, object] = {
        str(key): value for key, value in item.items()
    }
    correspondence = item.get(_SOURCE_RECORD_CORRESPONDENCE_FIELD)
    if _source_record_refreshable_correspondence(correspondence):
        projected.pop(_SOURCE_RECORD_CORRESPONDENCE_FIELD, None)
    return source_item_coverage_sha256(projected, mode)


def _source_semantic_projection(
    value: object,
    *,
    direct_source_item: bool = False,
    retain_direct_administrative_metadata: bool = False,
    project_corrected_target_authority: bool = True,
) -> object:
    """Drop navigation-only routes and source locators from a semantic digest.

    This is deliberately field-based rather than a declaration-name heuristic.
    A source map may retain routes for validation and navigation, but a route
    rename with the same checked proposition must not change the source-side
    content identity.  Unknown non-route fields remain in the digest so a new
    semantic source annotation fails closed by default. Historical readers can
    disable the corrected-target authority projection to replay the literal
    target representation their frozen digest generation used.
    """

    if isinstance(value, dict):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            normalized = key.strip().lower()
            if (
                normalized in _NAVIGATION_ONLY_ROUTE_FIELDS
                or normalized in _AGGREGATE_ONLY_ARTIFACT_FIELDS
                or normalized in _SOURCE_ITEM_NAVIGATION_ONLY_FIELDS
                or (
                    # This is a schema-level exception, not a normalized
                    # metadata vocabulary.  Only the literal top-level JSON
                    # field may be administrative; a case or whitespace
                    # lookalike is unknown semantic metadata and must remain
                    # in the item identity.
                    direct_source_item
                    and not retain_direct_administrative_metadata
                    and key in _SOURCE_ITEM_ADMINISTRATIVE_METADATA_FIELDS
                )
            ):
                continue
            if (
                direct_source_item
                and key == SOURCE_PRESENTATION_ALIAS_FIELD
                and raw_value is None
            ):
                # Inventory readers may materialize an absent optional alias
                # relation as JSON null.  Both mean this is the canonical
                # presentation.  A real alias object remains semantic and is
                # retained below.
                continue
            if (
                direct_source_item
                and project_corrected_target_authority
                and key == "corrected_target"
            ):
                # This literal source-item field has its own schema authority.
                # Its projection omits only derived correction digests and the
                # paper-local locator for the recognized excerpt protocol;
                # unknown target or approval fields remain semantic inputs.
                projected[key] = _source_semantic_projection(
                    corrected_target_record_projection(raw_value)
                )
                continue
            if normalized == "source_anchor_evidence":
                projected[key] = _source_anchor_semantic_projection(raw_value)
                continue
            if key == SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD:
                projected[key] = (
                    _source_prose_definition_reconciliation_semantic_projection(
                        raw_value
                    )
                )
                continue
            if key == SOURCE_STANDARD_TERM_INTERPRETATION_FIELD:
                projected[key] = (
                    _source_standard_term_interpretation_semantic_projection(
                        raw_value
                    )
                )
                continue
            projected[key] = _source_semantic_projection(raw_value)
        return projected
    if isinstance(value, list):
        return [_source_semantic_projection(item) for item in value]
    if isinstance(value, tuple):
        return [_source_semantic_projection(item) for item in value]
    return value


def _source_map_cache_value_projection(value: object) -> object:
    """Recursively preserve a source-map value for aggregate cache identity."""

    if isinstance(value, Mapping):
        return {
            str(raw_key): _source_map_cache_value_projection(raw_value)
            for raw_key, raw_value in value.items()
        }
    if isinstance(value, list):
        return [_source_map_cache_value_projection(item) for item in value]
    if isinstance(value, tuple):
        return [_source_map_cache_value_projection(item) for item in value]
    return value


def _source_named_result_inventory_review_cache_projection(value: object) -> object:
    """Keep source-classification content, not receipt bookkeeping, in raw reuse.

    ``environment_kinds`` and ``heading_kinds`` can change the independently
    selected source surface, so they remain semantic cache inputs.  The
    completion receipt and its digest merely certify the closeout consumer and
    are validated there; retaining them would force an unrelated raw audit for
    a timestamp or a source-presentation reconciliation repair.
    """

    if not isinstance(value, Mapping):
        return _source_map_cache_value_projection(value)
    projected: dict[str, object] = {}
    for raw_key, raw_value in value.items():
        key = str(raw_key)
        if key in _SOURCE_NAMED_RESULT_INVENTORY_REVIEW_AUDIT_ONLY_FIELDS:
            continue
        if key == SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD and isinstance(
            raw_value, list
        ):
            projected[key] = [
                _prose_definition_presentation_projection(record)
                if isinstance(record, Mapping)
                else _source_map_cache_value_projection(record)
                for record in raw_value
            ]
            continue
        projected[key] = _source_map_cache_value_projection(raw_value)
    return projected


def _source_map_cache_selected_item_keys(
    map_payload: object,
) -> set[str] | None:
    """Return the current aggregate raw-audit source selection when exact.

    The aggregate source-record generator consumes only source items selected
    by the map's active presentation mode.  A status-policy transition on an
    excluded Formula, figure, or prose item cannot alter that generated raw
    surface.  Conversely, an invalid map or an inability to reproduce the
    selector returns ``None`` so callers retain every status-policy marker and
    fail closed.

    This deliberately invokes the same source-presentation selector used by
    the generator.  It never makes a choice from a map key or Lean route.
    """

    if not isinstance(map_payload, dict):
        return None
    raw_items = map_payload.get("items")
    if not isinstance(raw_items, dict):
        return None
    mode, mode_error = source_coverage_mode_from_map(map_payload)
    if mode_error:
        return None
    try:
        selected = filter_source_map_items_for_coverage(
            raw_items,
            mode,
            declared_environment_kinds=source_named_result_environment_kinds_from_map(
                map_payload
            ),
        )
    except (AttributeError, KeyError, TypeError, ValueError):
        # The cache is an optimization. Any unexpected selector failure must
        # retain the status transition as a semantic input rather than assume
        # that an item is irrelevant.
        return None
    return set(selected)


def source_map_cache_semantic_projection(value: object) -> object:
    """Project a whole source map for expensive raw-audit cache eligibility.

    The full source-map byte SHA remains archival provenance.  This separate
    cache projection removes ordinary direct item bookkeeping fields listed in
    ``_SOURCE_ITEM_ADMINISTRATIVE_METADATA_FIELDS``.  When that field changes
    an effective source-route policy, it instead adds a compact policy receipt.
    It does not reuse the broader per-item semantic projection: source anchors,
    route metadata, unknown fields, and every nested field remain cache inputs
    here. It also omits only the exact, structurally refreshable Lean-derived
    source-to-Spec receipt hashes from each raw source item.  Strict
    correspondence validation owns those hashes and their retained mappings.
    Consequently a changed source note, target, condition, binding,
    disposition, or any new map metadata still requires a fresh raw audit by
    default.
    """

    if not isinstance(value, Mapping):
        return value
    # A policy receipt is needed only if the item can feed the current raw
    # audit surface.  Per-item coverage digests keep their stricter status
    # pin, so a deep-mode or otherwise selected item cannot inherit evidence
    # after a route-changing status edit.
    selected_item_keys = _source_map_cache_selected_item_keys(value)
    projected: dict[str, object] = {}
    for raw_key, raw_value in value.items():
        key = str(raw_key)
        # Source/repeat scope, panel cardinality, and model preferences are
        # independently validated and bound by closeout source assurance.
        # Selected item fields and the explicit coverage mode already determine
        # this raw audit surface.
        if key == "closeout_review_policy":
            continue
        # The parser treats a missing mode as exactly this documented default.
        # Canonicalize only the exact spelling here, so adding the required
        # explicit closeout declaration does not rerun an otherwise identical
        # raw audit. Whitespace variants, invalid modes, and every nondefault
        # mode remain byte/semantic cache inputs.
        if (
            key == "source_coverage_mode"
            and raw_value == DEFAULT_SOURCE_COVERAGE_MODE
        ):
            continue
        if key == _SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD:
            inventory_projection = _source_named_result_inventory_review_cache_projection(
                raw_value
            )
            # A receipt with no declared environment classification does not
            # feed the raw source-record generator.  Treating its empty
            # projection as a value would make adding or refreshing purely
            # closeout bookkeeping invalidate otherwise identical raw work.
            # Keep this narrow: any retained classification remains an exact
            # semantic cache input.
            if inventory_projection:
                projected[key] = inventory_projection
            continue
        if key != "items" or not isinstance(raw_value, Mapping):
            projected[key] = _source_map_cache_value_projection(raw_value)
            continue
        items: dict[str, object] = {}
        for raw_item_key, raw_item in raw_value.items():
            item_key = str(raw_item_key)
            if not isinstance(raw_item, Mapping):
                items[item_key] = _source_map_cache_value_projection(raw_item)
                continue
            raw_item_projection = source_record_source_item_projection(raw_item)
            assert isinstance(raw_item_projection, Mapping)
            item_projection: dict[str, object] = {}
            for raw_field, raw_field_value in raw_item_projection.items():
                field = str(raw_field)
                # The cache exception is for the schema's exact direct field,
                # not a case/whitespace-normalized lookalike. Unknown fields
                # remain semantic inputs and therefore fail closed.
                if field in _SOURCE_ITEM_ADMINISTRATIVE_METADATA_FIELDS:
                    continue
                if field == SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD:
                    item_projection[field] = (
                        _source_prose_definition_reconciliation_semantic_projection(
                            raw_field_value
                        )
                    )
                elif field == SOURCE_STANDARD_TERM_INTERPRETATION_FIELD:
                    item_projection[field] = (
                        _source_standard_term_interpretation_semantic_projection(
                            raw_field_value
                        )
                    )
                else:
                    item_projection[field] = _source_map_cache_value_projection(
                        raw_field_value
                    )
            status_policy = source_item_direct_status_policy_projection(raw_item)
            if (
                status_policy is not None
                and selected_item_keys is not None
                and item_key not in selected_item_keys
            ):
                # This item is absent from the current generator's selected
                # source surface. Its route-policy transition is preserved in
                # the map and validated whenever that mode later selects it,
                # but it cannot invalidate this unrelated aggregate receipt.
                status_policy = None
            if status_policy is None:
                # Preserve the exact schema-5 projection for every status whose
                # removal leaves routing/scope behavior unchanged. This is what
                # keeps ordinary existing raw audits reusable.
                items[item_key] = item_projection
            else:
                # Keep the synthetic receipt outside the raw source-item shape
                # so an unknown user field cannot collide with it. This wrapper
                # is emitted only for the status-sensitive subset above.
                items[item_key] = {
                    "source_item": item_projection,
                    "direct_source_status_policy": status_policy,
                }
        projected[key] = items
    return projected


def source_map_cache_semantic_sha256(value: object) -> str:
    """Return the narrow semantic map receipt used only for raw-cache reuse."""

    if not isinstance(value, Mapping):
        return ""
    encoded = json.dumps(
        {
            "schema": SOURCE_MAP_CACHE_SEMANTIC_DIGEST_SCHEMA,
            "formalization_coverage_protocol_sha256": (
                formalization_coverage_protocol_digest()
            ),
            "source_map": source_map_cache_semantic_projection(value),
        },
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def legacy_source_map_cache_semantic_sha256(value: object) -> str:
    """Reconstruct the pre-split map receipt for current-only compatibility.

    This helper is not a normal cache identity.  It lets a caller recognize an
    otherwise-current legacy receipt during the one-time migration to scoped
    coverage policy.  Because it uses the exact current whole-protocol digest,
    any intervening protocol edit makes the compatibility identity differ and
    therefore fails closed.
    """

    if not isinstance(value, Mapping):
        return ""
    encoded = json.dumps(
        {
            "schema": LEGACY_SOURCE_MAP_CACHE_SEMANTIC_DIGEST_SCHEMA,
            "formalization_protocol_sha256": formalization_protocol_digest(),
            "source_map": source_map_cache_semantic_projection(value),
        },
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _source_item_direct_presentation_text(item: dict[str, Any]) -> str:
    """Return fields that directly describe the item, excluding context quotes."""

    return "\n".join(
        str(item.get(field) or "").strip()
        for field in _PRESENTATION_TEXT_FIELDS
        if str(item.get(field) or "").strip()
    )


def source_named_result_environment_kinds_from_map(
    map_payload: object,
) -> dict[str, str]:
    """Return usable custom TeX result environments from the source-pinned receipt.

    This is a deliberately narrow bridge between the source-only named-result
    inventory and ordinary coverage selection.  A map key or Lean route can
    never make an item eligible.  Invalid receipt entries are omitted here,
    leaving the named-result receipt validator to report their precise error;
    ordinary coverage therefore fails closed instead of treating arbitrary
    prose as a theorem-like source statement.
    """

    if not isinstance(map_payload, Mapping):
        return {}
    review = map_payload.get("source_named_result_inventory_review")
    if not isinstance(review, Mapping):
        return {}
    raw_kinds = review.get("environment_kinds")
    if not isinstance(raw_kinds, Mapping):
        return {}

    kinds: dict[str, str] = {}
    for raw_environment, raw_kind in raw_kinds.items():
        if not isinstance(raw_environment, str) or not isinstance(raw_kind, str):
            continue
        environment = raw_environment.strip().lower()
        kind = raw_kind.strip().lower()
        if (
            _TEX_ENVIRONMENT_NAME_RE.fullmatch(environment)
            and kind in NAMED_THEORETICAL_SOURCE_KINDS
        ):
            kinds[environment] = kind
    return kinds


def _source_item_anchor_opens_declared_named_environment(
    item: dict[str, Any], declared_environment_kinds: Mapping[str, str] | None
) -> bool:
    """Whether an item has a self-pinned custom TeX result opening.

    Receipt metadata only classifies a source environment; it does not itself
    identify a source-map item.  The item must use the same canonical source
    kind and retain a structurally valid, self-hashed anchor whose first source
    token is that exact ``\\begin{...}``.  Full source-anchor validation later
    verifies the path, range, and canonical artifact bytes.
    """

    if not declared_environment_kinds:
        return False
    source_kind = str(item.get("source_kind") or "").strip().lower()
    if source_kind not in NAMED_THEORETICAL_SOURCE_KINDS:
        return False
    raw_anchors = item.get("source_anchor_evidence")
    if not isinstance(raw_anchors, list):
        return False
    for raw_anchor in raw_anchors:
        if not isinstance(raw_anchor, Mapping):
            continue
        path = raw_anchor.get("path")
        line_start = raw_anchor.get("line_start")
        line_end = raw_anchor.get("line_end")
        quoted_text = raw_anchor.get("quoted_text")
        quoted_text_sha256 = raw_anchor.get("quoted_text_sha256")
        if (
            not isinstance(path, str)
            or not path.strip()
            or not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or not isinstance(line_end, int)
            or isinstance(line_end, bool)
            or line_start < 1
            or line_end < line_start
            or not isinstance(quoted_text, str)
            or not isinstance(quoted_text_sha256, str)
        ):
            continue
        normalized_quote = quoted_text.replace("\r\n", "\n").replace("\r", "\n")
        if (
            not normalized_quote
            or not _SHA256_RE.fullmatch(quoted_text_sha256.strip())
        ):
            continue
        if hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest() != quoted_text_sha256.strip().lower():
            continue
        opening = _TEX_BEGIN_ENVIRONMENT_RE.match(normalized_quote.lstrip())
        if opening is None:
            continue
        environment = opening.group("environment").strip().lower()
        if declared_environment_kinds.get(environment) == source_kind:
            return True
    return False


def _source_item_has_named_heading(item: dict[str, Any]) -> bool:
    """Detect a source-labelled result from the item's own presentation text.

    Anchor excerpts often deliberately include prerequisite context.  Treating
    every header in those broad excerpts as the item subject would overfit to
    how one paper happened to chunk its transcript.  The independent
    source-file named-result index performs source-line reconciliation for
    anchor-only headings; this local classifier stays limited to the map's
    direct source presentation.
    """

    return bool(
        _NAMED_THEORETICAL_HEADING_RE.search(
            _source_item_direct_presentation_text(item)
        )
    )


def _source_item_anchor_begins_named_heading(item: dict[str, Any]) -> bool:
    """Return whether a pinned anchor itself opens with a named source result."""

    return any(
        _NAMED_THEORETICAL_HEADING_RE.match(anchor.lstrip())
        for anchor in _valid_source_anchor_texts(item)
    )


def _valid_source_anchor_texts(item: dict[str, Any]) -> list[str]:
    """Return structurally valid, self-hashed source-anchor quotes only.

    Full artifact verification belongs to the source-anchor integrity lane.  At
    scope-selection time, requiring a path, line range, quote, and matching
    SHA-256 still prevents a curator-provided source kind or a free-form
    support excerpt from manufacturing a named-theory presentation.
    """

    raw_anchors = item.get("source_anchor_evidence")
    if not isinstance(raw_anchors, list):
        return []
    valid_quotes: list[str] = []
    for raw_anchor in raw_anchors:
        if not isinstance(raw_anchor, Mapping):
            continue
        path = raw_anchor.get("path")
        line_start = raw_anchor.get("line_start")
        line_end = raw_anchor.get("line_end")
        quoted_text = raw_anchor.get("quoted_text")
        quoted_text_sha256 = raw_anchor.get("quoted_text_sha256")
        if (
            not isinstance(path, str)
            or not path.strip()
            or not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or not isinstance(line_end, int)
            or isinstance(line_end, bool)
            or line_start < 1
            or line_end < line_start
            or not isinstance(quoted_text, str)
            or not isinstance(quoted_text_sha256, str)
        ):
            continue
        normalized_quote = quoted_text.replace("\r\n", "\n").replace("\r", "\n")
        if not normalized_quote or not _SHA256_RE.fullmatch(quoted_text_sha256.strip()):
            continue
        if (
            hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
            != quoted_text_sha256.strip().lower()
        ):
            continue
        valid_quotes.append(normalized_quote)
    return valid_quotes


def _source_kind_matches_named_presentation(
    source_kind: str, presentation_kind: str
) -> bool:
    """Whether a visible result title can support this source presentation kind."""

    if source_kind == "predicate_vocabulary":
        return presentation_kind == "definition"
    if source_kind in {"formula", "equation", "algorithmic_formula"}:
        return presentation_kind in {"formula", "equation"}
    return source_kind == presentation_kind


def _source_text_has_matching_unnumbered_heading(
    source_text: str, source_kind: str
) -> bool:
    """Recognize a conventional source heading without a numeric label.

    The source-only index intentionally requires a label for ordinary text
    headings so prose cross-references do not become results.  A source map may
    nevertheless quote a conventional heading such as ``Theorem:`` or
    ``Definition (Model)``.  Those are still visible presentations, but only
    when the title itself agrees with the declared source kind.
    """

    titles = _SOURCE_KIND_VISIBLE_TITLES.get(source_kind, ())
    if not titles:
        return False
    title_pattern = "|".join(re.escape(title) for title in titles)
    return bool(
        re.search(
            rf"(?im)^\s*(?:\\(?:noindent|paragraph)\b\s*)?"
            rf"(?:\\(?:textbf|textit|emph)\s*\{{\s*)?"
            rf"(?:{title_pattern})\b\s*(?=[:~\-(])",
            source_text,
        )
    )


def _source_item_directly_presents_named_kind(
    item: dict[str, Any],
    source_kind: str,
    declared_environment_kinds: Mapping[str, str] | None,
) -> bool:
    """Check direct source text without using map keys or Lean routes."""

    source_text = _source_item_direct_presentation_text(item)
    if not source_text:
        return False
    try:
        presentations = extract_named_result_presentations(
            source_text,
            source_format="auto",
            environment_kinds=declared_environment_kinds,
        )
    except ValueError:
        return False
    return bool(
        any(
            _source_kind_matches_named_presentation(source_kind, presentation.kind)
            for presentation in presentations
        )
        or _source_text_has_matching_unnumbered_heading(source_text, source_kind)
    )


def _source_item_anchor_opens_named_kind(
    item: dict[str, Any],
    source_kind: str,
    declared_environment_kinds: Mapping[str, str] | None,
) -> bool:
    """Check a byte-pinned source anchor that begins its own named result."""

    for anchor_text in _valid_source_anchor_texts(item):
        first_content_line = next(
            (
                line_number
                for line_number, line in enumerate(anchor_text.split("\n"), start=1)
                if line.strip() and not line.lstrip().startswith("%")
            ),
            None,
        )
        if first_content_line is None:
            continue
        try:
            presentations = extract_named_result_presentations(
                anchor_text,
                source_format="tex",
                environment_kinds=declared_environment_kinds,
            )
        except ValueError:
            continue
        if any(
            presentation.line_start == first_content_line
            and _source_kind_matches_named_presentation(
                source_kind, presentation.kind
            )
            for presentation in presentations
        ):
            return True
        first_line_text = anchor_text.split("\n")[first_content_line - 1]
        if _source_text_has_matching_unnumbered_heading(
            first_line_text, source_kind
        ):
            return True
    return False


def _source_item_opens_ordinary_named_presentation(
    item: dict[str, Any],
    declared_environment_kinds: Mapping[str, str] | None,
) -> bool:
    """Detect a visibly ordinary result independently of its declared kind.

    This is the fail-closed side of the normal/deep boundary.  A map row that
    calls itself an equation or algorithm must not suppress source text that
    actually opens a theorem, lemma, definition, or another normal-scope
    presentation.  Conversely, a genuinely labelled equation or algorithm
    remains deep-only because its parsed presentation kind is not in the
    ordinary protocol set.
    """

    ordinary_kinds = set(_NORMAL_COVERAGE_PROTOCOL["included_source_kinds"])

    def opens_ordinary(source_text: str, *, source_format: str) -> bool:
        if not source_text:
            return False
        try:
            presentations = extract_named_result_presentations(
                source_text,
                source_format=source_format,
                environment_kinds=declared_environment_kinds,
            )
        except ValueError:
            presentations = []
        if any(presentation.kind in ordinary_kinds for presentation in presentations):
            return True
        return any(
            _source_text_has_matching_unnumbered_heading(source_text, kind)
            for kind in ordinary_kinds
        )

    direct_presentation = _source_item_direct_presentation_text(item)
    if opens_ordinary(direct_presentation, source_format="auto"):
        return True
    source_kind = str(item.get("source_kind") or "").strip().lower()
    if (
        source_kind in NORMAL_SCOPE_EXCLUDED_STANDALONE_SOURCE_KINDS
        and direct_presentation
    ):
        # Broad anchors often include a downstream theorem that proves or uses
        # this display. Once the item's own visible text presents a non-result
        # display, that contextual theorem cannot reclassify the item. A direct
        # theorem/lemma/definition presentation already returned true above;
        # anchor-only recovery remains available for legacy rows with no direct
        # presentation text at all.
        return False
    for anchor_text in _valid_source_anchor_texts(item):
        first_content_line = next(
            (
                line
                for line in anchor_text.split("\n")
                if line.strip() and not line.lstrip().startswith("%")
            ),
            "",
        )
        if opens_ordinary(first_content_line, source_format="tex"):
            return True
    return False


def _normalized_prose_definition_text(value: object) -> str:
    """Normalize a literal source clause without interpreting identifiers."""

    return " ".join(str(value or "").replace("\r\n", "\n").replace("\r", "\n").split())


def _prose_definition_source_core_projection(
    record: Mapping[str, object],
) -> dict[str, object]:
    """Return exact source content before scope/reviewer classification."""

    anchor = record.get("source_anchor")
    anchor_projection = (
        {
            field: anchor.get(field)
            for field in (
                "path",
                "line_start",
                "line_end",
                "quoted_text",
                "quoted_text_sha256",
            )
        }
        if isinstance(anchor, Mapping)
        else anchor
    )
    return {
        "schema": record.get("schema"),
        "presentation_kind": record.get("presentation_kind"),
        "defined_entity_kind": record.get("defined_entity_kind"),
        "defined_object": record.get("defined_object"),
        "definitional_clause": record.get("definitional_clause"),
        "source_anchor": anchor_projection,
    }


def source_prose_definition_clause_sha256(record: object) -> str:
    """Hash the exact definition-shaped source presentation before judgment."""

    if not isinstance(record, Mapping):
        return ""
    encoded = json.dumps(
        _prose_definition_source_core_projection(record),
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _prose_definition_presentation_projection(
    record: Mapping[str, object],
) -> dict[str, object]:
    """Return semantic selection identity without reviewer credentials."""

    return {
        **_prose_definition_source_core_projection(record),
        "scope_disposition": record.get("scope_disposition"),
        "canonical_presentation_sha256": record.get(
            "canonical_presentation_sha256"
        ),
        "repetition_judgment": record.get("repetition_judgment"),
        "repetition_judgment_source_sha256": record.get(
            "repetition_judgment_source_sha256"
        ),
        "scope_judgment": record.get("scope_judgment"),
        "scope_judgment_source_sha256": record.get(
            "scope_judgment_source_sha256"
        ),
        SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD: record.get(
            SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD
        ),
    }


def _prose_definition_presentation_audit_projection(
    record: Mapping[str, object],
) -> dict[str, object]:
    """Return the complete ledger record, including review credentials."""

    return {
        **_prose_definition_presentation_projection(record),
        "scope_reason": record.get("scope_reason"),
        "semantic_basis": record.get("semantic_basis"),
        "validator": record.get("validator"),
        "validator_type": record.get("validator_type"),
        "validated_at": record.get("validated_at"),
    }


def source_prose_definition_presentation_sha256(record: object) -> str:
    """Hash a prose definition without map keys, Lean names, or route metadata."""

    if not isinstance(record, Mapping):
        return ""
    encoded = json.dumps(
        _prose_definition_presentation_projection(record),
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def source_prose_definition_presentations_sha256(records: object) -> str:
    """Hash an independently extracted prose-definition inventory."""

    if not isinstance(records, list):
        return ""
    projections = [
        _prose_definition_presentation_audit_projection(record)
        for record in records
        if isinstance(record, Mapping)
    ]
    if len(projections) != len(records):
        return ""
    projections.sort(
        key=lambda record: json.dumps(
            record, ensure_ascii=True, sort_keys=True, separators=(",", ":")
        )
    )
    encoded = json.dumps(
        projections,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def source_item_statement_sha256(item: object) -> str:
    """Hash the exact current source-map statement for a semantic binding."""

    if not isinstance(item, Mapping):
        return ""
    statement = _normalized_prose_definition_text(item.get("statement"))
    if not statement:
        return ""
    return hashlib.sha256(statement.encode("utf-8")).hexdigest()


def source_prose_definition_statement_sha256(item: object) -> str:
    """Compatibility name for the source-item statement semantic pin."""

    return source_item_statement_sha256(item)


def source_prose_definition_presentation_errors(record: object) -> list[str]:
    """Validate one source-only prose-definition extraction record.

    The record is deliberately literal.  Its exact source clause and defined
    object are evidence; a source-map kind, row name, or Lean declaration is
    not.  Current artifact bytes are checked separately by the folder-aware
    reconciliation lane.
    """

    if not isinstance(record, Mapping):
        return ["prose definition presentation must be an object"]
    errors: list[str] = []
    allowed_fields = {
        "schema",
        "presentation_kind",
        "defined_entity_kind",
        "defined_object",
        "definitional_clause",
        "scope_disposition",
        "scope_reason",
        "canonical_presentation_sha256",
        "repetition_judgment",
        "repetition_judgment_source_sha256",
        "scope_judgment",
        "scope_judgment_source_sha256",
        SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD,
        "semantic_basis",
        "validator",
        "validator_type",
        "validated_at",
        "source_anchor",
    }
    unexpected = sorted(str(field) for field in record if str(field) not in allowed_fields)
    if unexpected:
        errors.append(
            "prose definition presentation has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if record.get("schema") != SOURCE_PROSE_DEFINITION_PRESENTATION_SCHEMA:
        errors.append(
            "prose definition presentation schema must be "
            f"{SOURCE_PROSE_DEFINITION_PRESENTATION_SCHEMA}"
        )
    if record.get("presentation_kind") != "definition":
        errors.append("prose definition presentation_kind must be `definition`")
    scope_disposition = str(record.get("scope_disposition") or "").strip().lower()
    if scope_disposition not in SOURCE_PROSE_DEFINITION_SCOPE_DISPOSITIONS:
        errors.append(
            "prose definition scope_disposition must be one of: "
            + ", ".join(sorted(SOURCE_PROSE_DEFINITION_SCOPE_DISPOSITIONS))
        )
    scope_reason = str(record.get("scope_reason") or "").strip()
    shared_review_fields = {
        "validator",
        "validator_type",
        "validated_at",
    }
    repetition_fields = {
        "canonical_presentation_sha256",
        "repetition_judgment",
        "repetition_judgment_source_sha256",
        "semantic_basis",
    }
    exclusion_fields = {
        "scope_reason",
        "scope_judgment",
        "scope_judgment_source_sha256",
        SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD,
    }
    present_repetition_fields = (repetition_fields | shared_review_fields).intersection(
        record
    )
    present_exclusion_fields = (exclusion_fields | shared_review_fields).intersection(
        record
    )
    clause_digest = source_prose_definition_clause_sha256(record)
    if scope_disposition == SOURCE_PROSE_DEFINITION_REPEATED_SCOPE:
        canonical_digest = str(
            record.get("canonical_presentation_sha256") or ""
        ).strip().lower()
        if not _SHA256_RE.fullmatch(canonical_digest):
            errors.append(
                "a repeated prose definition requires canonical_presentation_sha256"
            )
        if (
            record.get("repetition_judgment")
            != SOURCE_PROSE_DEFINITION_REPETITION_JUDGMENT
        ):
            errors.append(
                "a repeated prose definition requires repetition_judgment "
                f"`{SOURCE_PROSE_DEFINITION_REPETITION_JUDGMENT}`"
            )
        if (
            str(record.get("repetition_judgment_source_sha256") or "")
            .strip()
            .lower()
            != clause_digest
        ):
            errors.append(
                "a repeated prose definition repetition_judgment_source_sha256 "
                "does not match its exact current source presentation"
            )
        if len(str(record.get("semantic_basis") or "").strip()) < 20:
            errors.append(
                "a repeated prose definition requires a substantive semantic_basis"
            )
        if not str(record.get("validator") or "").strip():
            errors.append("a repeated prose definition requires a validator")
        validator_type = str(record.get("validator_type") or "").strip().lower()
        if validator_type not in SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES:
            errors.append(
                "a repeated prose definition validator_type must be one of: "
                + ", ".join(sorted(SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES))
            )
        if not _ISO_LIKE_TIMESTAMP_RE.fullmatch(
            str(record.get("validated_at") or "").strip()
        ):
            errors.append(
                "a repeated prose definition validated_at must be an ISO-like UTC timestamp"
            )
        if exclusion_fields.intersection(record):
            errors.append(
                "a repeated prose definition cannot carry normal-scope exclusion fields"
            )
    elif scope_disposition in SOURCE_PROSE_DEFINITION_EXCLUDED_SCOPE_DISPOSITIONS:
        if len(scope_reason) < 20:
            errors.append(
                "a prose definition excluded from normal scope requires a substantive "
                "source-only scope_reason"
            )
        if record.get("scope_judgment") != SOURCE_PROSE_DEFINITION_EXCLUSION_JUDGMENT:
            errors.append(
                "a prose definition excluded from normal scope requires scope_judgment "
                f"`{SOURCE_PROSE_DEFINITION_EXCLUSION_JUDGMENT}`"
            )
        if (
            str(record.get("scope_judgment_source_sha256") or "").strip().lower()
            != clause_digest
        ):
            errors.append(
                "an excluded prose definition scope_judgment_source_sha256 does not "
                "match its exact current source presentation"
            )
        if not str(record.get("validator") or "").strip():
            errors.append("an excluded prose definition requires a validator")
        validator_type = str(record.get("validator_type") or "").strip().lower()
        if validator_type not in SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES:
            errors.append(
                "an excluded prose definition validator_type must be one of: "
                + ", ".join(sorted(SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES))
            )
        if not _ISO_LIKE_TIMESTAMP_RE.fullmatch(
            str(record.get("validated_at") or "").strip()
        ):
            errors.append(
                "an excluded prose definition validated_at must be an ISO-like UTC timestamp"
            )
        approval = record.get(SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_FIELD)
        if scope_disposition == "deep_only_definition":
            if not isinstance(approval, Mapping):
                errors.append(
                    "deep_only_definition requires explicit normal_scope_exclusion_approval"
                )
            else:
                allowed_approval_fields = {
                    "schema",
                    "approval_kind",
                    "approval_reference",
                    "approved_at",
                }
                unexpected_approval_fields = sorted(
                    str(field)
                    for field in approval
                    if str(field) not in allowed_approval_fields
                )
                if unexpected_approval_fields:
                    errors.append(
                        "normal_scope_exclusion_approval has unsupported field(s): "
                        + ", ".join(unexpected_approval_fields)
                    )
                if (
                    approval.get("schema")
                    != SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_SCHEMA
                ):
                    errors.append(
                        "normal_scope_exclusion_approval.schema must be "
                        f"{SOURCE_PROSE_DEFINITION_EXCLUSION_APPROVAL_SCHEMA}"
                    )
                if approval.get("approval_kind") != "explicit_user_instruction":
                    errors.append(
                        "normal_scope_exclusion_approval.approval_kind must be "
                        "`explicit_user_instruction`"
                    )
                if len(str(approval.get("approval_reference") or "").strip()) < 20:
                    errors.append(
                        "normal_scope_exclusion_approval.approval_reference must be substantive"
                    )
                if not _ISO_LIKE_TIMESTAMP_RE.fullmatch(
                    str(approval.get("approved_at") or "").strip()
                ):
                    errors.append(
                        "normal_scope_exclusion_approval.approved_at must be an ISO-like UTC timestamp"
                    )
        elif approval is not None:
            errors.append(
                "normal_scope_exclusion_approval is reserved for deep_only_definition"
            )
        if repetition_fields.intersection(record):
            errors.append(
                "an excluded prose definition cannot carry repeated-presentation fields"
            )
    elif present_repetition_fields or present_exclusion_fields:
        errors.append(
            "a canonical normal prose definition cannot carry repetition or exclusion "
            "judgment fields"
        )
    entity_kind = str(record.get("defined_entity_kind") or "").strip()
    if entity_kind not in SOURCE_PROSE_DEFINITION_ENTITY_KINDS:
        errors.append(
            "prose definition defined_entity_kind must be one of: "
            + ", ".join(sorted(SOURCE_PROSE_DEFINITION_ENTITY_KINDS))
        )
    defined_object = _normalized_prose_definition_text(record.get("defined_object"))
    clause = _normalized_prose_definition_text(record.get("definitional_clause"))
    if not defined_object:
        errors.append("prose definition defined_object is required")
    if len(clause) < 12:
        errors.append("prose definition definitional_clause must be a substantive literal source clause")
    elif defined_object and defined_object not in clause:
        errors.append("prose definition definitional_clause must literally contain defined_object")

    anchor = record.get("source_anchor")
    if not isinstance(anchor, Mapping):
        errors.append("prose definition source_anchor must be an object")
        return errors
    allowed_anchor_fields = {
        "path",
        "line_start",
        "line_end",
        "quoted_text",
        "quoted_text_sha256",
    }
    unexpected_anchor = sorted(
        str(field) for field in anchor if str(field) not in allowed_anchor_fields
    )
    if unexpected_anchor:
        errors.append(
            "prose definition source_anchor has unsupported field(s): "
            + ", ".join(unexpected_anchor)
        )
    path = anchor.get("path")
    line_start = anchor.get("line_start")
    line_end = anchor.get("line_end")
    quote = anchor.get("quoted_text")
    quote_digest = anchor.get("quoted_text_sha256")
    if not isinstance(path, str) or not path.strip():
        errors.append("prose definition source_anchor.path is required")
    if (
        not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
        or line_start < 1
        or line_end < line_start
    ):
        errors.append("prose definition source_anchor requires valid inclusive line bounds")
    if not isinstance(quote, str) or not quote:
        errors.append("prose definition source_anchor.quoted_text is required")
    else:
        normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
        if (
            isinstance(line_start, int)
            and not isinstance(line_start, bool)
            and isinstance(line_end, int)
            and not isinstance(line_end, bool)
            and line_end >= line_start
            and normalized_quote.count("\n") + 1 != line_end - line_start + 1
        ):
            errors.append("prose definition source_anchor line bounds do not match quoted_text")
        if clause and clause not in _normalized_prose_definition_text(normalized_quote):
            errors.append("prose definition definitional_clause is not literal text from source_anchor")
        if (
            not isinstance(quote_digest, str)
            or not _SHA256_RE.fullmatch(quote_digest.strip())
            or hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
            != quote_digest.strip().lower()
        ):
            errors.append("prose definition source_anchor quoted_text_sha256 is invalid")
    return errors


def source_prose_definition_reconciliation_errors(item: object) -> list[str]:
    """Validate an item's opaque binding to one source-only definition record."""

    if not isinstance(item, Mapping):
        return []
    reconciliation = item.get(SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD)
    if reconciliation is None:
        return []
    if not isinstance(reconciliation, Mapping):
        return [f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD} must be an object"]
    errors: list[str] = []
    allowed_fields = {
        "schema",
        "relation",
        "presentation_sha256",
        "source_item_statement_sha256",
        "judgment",
        "semantic_basis",
        "validator",
        "validator_type",
        "validated_at",
    }
    unexpected = sorted(
        str(field) for field in reconciliation if str(field) not in allowed_fields
    )
    if unexpected:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if reconciliation.get("schema") != SOURCE_PROSE_DEFINITION_RECONCILIATION_SCHEMA:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.schema must be "
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_SCHEMA}"
        )
    if reconciliation.get("relation") != SOURCE_PROSE_DEFINITION_RECONCILIATION_RELATION:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.relation must be "
            f"`{SOURCE_PROSE_DEFINITION_RECONCILIATION_RELATION}`"
        )
    digest = str(reconciliation.get("presentation_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(digest):
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.presentation_sha256 is required"
        )
    statement_digest = source_item_statement_sha256(item)
    recorded_statement_digest = str(
        reconciliation.get("source_item_statement_sha256") or ""
    ).strip().lower()
    if not statement_digest:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD} requires a nonempty "
            "source-map statement"
        )
    elif recorded_statement_digest != statement_digest:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}."
            "source_item_statement_sha256 does not match the current source-map statement"
        )
    if (
        reconciliation.get("judgment")
        != SOURCE_PROSE_DEFINITION_RECONCILIATION_JUDGMENT
    ):
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.judgment must be "
            f"`{SOURCE_PROSE_DEFINITION_RECONCILIATION_JUDGMENT}`"
        )
    basis = str(reconciliation.get("semantic_basis") or "").strip()
    if len(basis) < 20:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.semantic_basis must be substantive"
        )
    validator = str(reconciliation.get("validator") or "").strip()
    if not validator:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.validator is required"
        )
    validator_type = str(reconciliation.get("validator_type") or "").strip().lower()
    if validator_type not in SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES:
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.validator_type must be one of: "
            + ", ".join(sorted(SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES))
        )
    validated_at = str(reconciliation.get("validated_at") or "").strip()
    if not _ISO_LIKE_TIMESTAMP_RE.fullmatch(validated_at):
        errors.append(
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}.validated_at must be an ISO-like UTC timestamp"
        )
    return errors


def _source_standard_term_use_anchor_errors(
    anchor: object, *, source_term: str
) -> list[str]:
    """Validate the literal, byte-pinned source occurrence of one term."""

    if not isinstance(anchor, Mapping):
        return ["source_term_use_anchor must be an object"]
    errors: list[str] = []
    allowed_fields = {
        "path",
        "line_start",
        "line_end",
        "quoted_text",
        "quoted_text_sha256",
    }
    unexpected = sorted(str(field) for field in anchor if str(field) not in allowed_fields)
    if unexpected:
        errors.append(
            "source_term_use_anchor has unsupported field(s): "
            + ", ".join(unexpected)
        )
    path = anchor.get("path")
    line_start = anchor.get("line_start")
    line_end = anchor.get("line_end")
    quote = anchor.get("quoted_text")
    quote_digest = anchor.get("quoted_text_sha256")
    if not isinstance(path, str) or not _normalized_exact_source_path(path):
        errors.append("source_term_use_anchor.path must be a safe relative source path")
    if (
        not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
        or line_start < 1
        or line_end < line_start
    ):
        errors.append("source_term_use_anchor requires valid inclusive line bounds")
    if not isinstance(quote, str) or not quote:
        errors.append("source_term_use_anchor.quoted_text is required")
        return errors
    normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
    if (
        isinstance(line_start, int)
        and not isinstance(line_start, bool)
        and isinstance(line_end, int)
        and not isinstance(line_end, bool)
        and line_end >= line_start
        and normalized_quote.count("\n") + 1 != line_end - line_start + 1
    ):
        errors.append("source_term_use_anchor line bounds do not match quoted_text")
    if (
        not isinstance(quote_digest, str)
        or not _SHA256_RE.fullmatch(quote_digest.strip())
        or hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
        != quote_digest.strip().lower()
    ):
        errors.append("source_term_use_anchor.quoted_text_sha256 is invalid")
    if source_term and source_term not in normalized_quote:
        errors.append("source_term_use_anchor.quoted_text must literally contain source_term")
    return errors


def source_standard_term_interpretation_errors(
    item: object,
    *,
    source_text: str | None = None,
    source_path: str | None = None,
    inventory_validator: str | None = None,
) -> list[str]:
    """Validate an external-standard-term interpretation on one source row.

    This relation is deliberately narrower than prose-definition
    reconciliation. It records that the source *uses* a standard mathematical
    term without supplying its definition; it never turns a route, a map key,
    or a Lean declaration spelling into evidence for that conclusion.
    """

    if not isinstance(item, Mapping):
        return []
    if SOURCE_STANDARD_TERM_INTERPRETATION_FIELD not in item:
        return []
    mutual_exclusivity_errors: list[str] = []
    if SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD in item:
        mutual_exclusivity_errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD} cannot coexist with "
            f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}"
        )
    interpretation = item.get(SOURCE_STANDARD_TERM_INTERPRETATION_FIELD)
    if not isinstance(interpretation, Mapping):
        return [
            *mutual_exclusivity_errors,
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD} must be an object",
        ]

    errors = mutual_exclusivity_errors
    allowed_fields = {
        "schema",
        "relation",
        "source_term",
        "source_provided_definition",
        "source_term_use_anchor",
        "source_item_statement_sha256",
        "standard_interpretation",
        "judgment",
        "semantic_basis",
        "validator",
        "validator_type",
        "validated_at",
    }
    unexpected = sorted(
        str(field) for field in interpretation if str(field) not in allowed_fields
    )
    if unexpected:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if (
        interpretation.get("schema")
        != SOURCE_STANDARD_TERM_INTERPRETATION_SCHEMA
        or isinstance(interpretation.get("schema"), bool)
    ):
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.schema must be "
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_SCHEMA}"
        )
    if (
        interpretation.get("relation")
        != SOURCE_STANDARD_TERM_INTERPRETATION_RELATION
    ):
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.relation must be "
            f"`{SOURCE_STANDARD_TERM_INTERPRETATION_RELATION}`"
        )
    raw_term = interpretation.get("source_term")
    source_term = raw_term.strip() if isinstance(raw_term, str) else ""
    if not source_term or raw_term != source_term:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.source_term must be a "
            "nonempty literal without leading or trailing whitespace"
        )
    if interpretation.get("source_provided_definition") is not False:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.source_provided_definition "
            "must be false"
        )
    anchor = interpretation.get("source_term_use_anchor")
    errors.extend(
        f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.{error}"
        for error in _source_standard_term_use_anchor_errors(
            anchor, source_term=source_term
        )
    )
    statement_digest = source_item_statement_sha256(item)
    recorded_statement_digest = str(
        interpretation.get("source_item_statement_sha256") or ""
    ).strip().lower()
    if not statement_digest:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD} requires a nonempty "
            "source-map statement"
        )
    elif recorded_statement_digest != statement_digest:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}."
            "source_item_statement_sha256 does not match the current source-map statement"
        )
    statement = item.get("statement")
    if isinstance(statement, str) and source_term and source_term not in statement:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.source_term must literally "
            "occur in the current source-map statement"
        )
    standard_interpretation = interpretation.get("standard_interpretation")
    if (
        not isinstance(standard_interpretation, str)
        or len(standard_interpretation.strip()) < 20
    ):
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.standard_interpretation "
            "must be substantive"
        )
    if (
        interpretation.get("judgment")
        != SOURCE_STANDARD_TERM_INTERPRETATION_JUDGMENT
    ):
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.judgment must be "
            f"`{SOURCE_STANDARD_TERM_INTERPRETATION_JUDGMENT}`"
        )
    semantic_basis = interpretation.get("semantic_basis")
    if not isinstance(semantic_basis, str) or len(semantic_basis.strip()) < 20:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.semantic_basis must be substantive"
        )
    validator = str(interpretation.get("validator") or "").strip()
    if not validator:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.validator is required"
        )
    validator_type = str(interpretation.get("validator_type") or "").strip().lower()
    if validator_type not in SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES:
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.validator_type must be one of: "
            + ", ".join(sorted(SOURCE_PROSE_DEFINITION_VALIDATOR_TYPES))
        )
    if not _ISO_LIKE_TIMESTAMP_RE.fullmatch(
        str(interpretation.get("validated_at") or "").strip()
    ):
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.validated_at must be an ISO-like UTC timestamp"
        )
    if inventory_validator is not None:
        if not inventory_validator:
            errors.append(
                f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD} requires a readable "
                "independent source-inventory validator"
            )
        elif validator == inventory_validator:
            errors.append(
                f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.validator must be "
                "independent from the source inventory extractor"
            )

    if (source_text is None) != (source_path is None):
        errors.append(
            f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD} current-source validation "
            "requires both source_text and source_path"
        )
    elif source_text is not None and source_path is not None:
        term_span = _current_source_anchor_span(
            anchor, source_text=source_text, source_path=source_path
        )
        if term_span is None:
            errors.append(
                f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.source_term_use_anchor "
                "is not the exact current source slice"
            )
        elif not _item_has_current_anchor_containing_span(
            item, term_span, source_text=source_text, source_path=source_path
        ):
            errors.append(
                f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.source_term_use_anchor "
                "is not contained in this item's exact current source_anchor_evidence"
            )
        current_item_quotes = []
        raw_item_anchors = item.get("source_anchor_evidence")
        if isinstance(raw_item_anchors, list):
            for raw_item_anchor in raw_item_anchors:
                if (
                    _current_source_anchor_span(
                        raw_item_anchor,
                        source_text=source_text,
                        source_path=source_path,
                    )
                    is not None
                    and isinstance(raw_item_anchor, Mapping)
                    and isinstance(raw_item_anchor.get("quoted_text"), str)
                ):
                    current_item_quotes.append(raw_item_anchor["quoted_text"])
        if source_term and not any(source_term in quote for quote in current_item_quotes):
            errors.append(
                f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}.source_term must literally "
                "occur in this item's exact current source_anchor_evidence"
            )
    return sorted(set(errors))


def source_map_structural_errors(
    raw_items: object,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
) -> list[str]:
    """Return source-map shape/presentation errors before scope projection.

    Ordinary coverage intentionally excludes captions and prose.  It must not
    exclude malformed inventory entries, unknown presentation categories, or a
    source theorem recast as a non-claim.  This validator is run over the raw
    map rather than the normalized inventory, which otherwise has to discard
    unreadable rows to build prompts safely.
    """

    if not isinstance(raw_items, dict):
        return ["source map `items` must be an object"]
    errors: list[str] = []
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key or "").strip()
        prefix = f"items.{key}" if key else "items.<empty>"
        if not key:
            errors.append("source map item key must be nonempty")
        if not isinstance(raw_item, dict):
            errors.append(f"{prefix}: source inventory item is not an object")
            continue
        errors.extend(
            f"{prefix}: {error}"
            for error in source_item_scope_classification_errors(
                raw_item,
                declared_environment_kinds=declared_environment_kinds,
            )
        )
        errors.extend(
            f"{prefix}: {error}"
            for error in source_prose_definition_reconciliation_errors(raw_item)
        )
        errors.extend(
            f"{prefix}: {error}"
            for error in source_standard_term_interpretation_errors(raw_item)
        )
    errors.extend(source_presentation_aliases(raw_items)[1])
    return sorted(set(errors))


def source_coverage_mode_from_map(
    map_payload: object,
) -> tuple[str, str]:
    """Return the configured source-coverage mode and any configuration error.

    Missing configuration is intentionally backwards compatible and efficient:
    it selects the ordinary named-theory surface.  An invalid explicit value is
    reported to callers while retaining that conservative default; callers must
    fail their closeout gate on the returned error rather than widening or
    silently disabling review.
    """

    if not isinstance(map_payload, dict):
        return DEFAULT_SOURCE_COVERAGE_MODE, ""
    raw_mode = map_payload.get("source_coverage_mode")
    if raw_mode is None:
        return DEFAULT_SOURCE_COVERAGE_MODE, ""
    if not isinstance(raw_mode, str) or not raw_mode.strip():
        return (
            DEFAULT_SOURCE_COVERAGE_MODE,
            "paper_statement_map.json source_coverage_mode must be a nonempty string",
        )
    mode = raw_mode.strip()
    if mode not in VALID_SOURCE_COVERAGE_MODES:
        return (
            DEFAULT_SOURCE_COVERAGE_MODE,
            "paper_statement_map.json source_coverage_mode must be one of "
            + ", ".join(sorted(VALID_SOURCE_COVERAGE_MODES)),
        )
    return mode, ""


def source_coverage_mode_is_explicit(map_payload: object) -> bool:
    """Return whether a map deliberately records a valid coverage mode.

    Missing mode remains readable as the ordinary default for legacy discovery,
    but a paper claiming a closeout must migrate to an explicit source-scope
    decision.  That distinction avoids both a silent scope expansion and a
    breaking change for draft/source-exploration tools.
    """

    if not isinstance(map_payload, dict):
        return False
    raw_mode = map_payload.get("source_coverage_mode")
    return isinstance(raw_mode, str) and raw_mode.strip() in VALID_SOURCE_COVERAGE_MODES


def source_coverage_mode_migration_error(
    map_payload: object, *, require_explicit: bool
) -> str:
    """Return a closeout-only explicit-mode migration error, if appropriate."""

    _mode, error = source_coverage_mode_from_map(map_payload)
    if error:
        return error
    if require_explicit and not source_coverage_mode_is_explicit(map_payload):
        return (
            "paper_statement_map.json must explicitly set source_coverage_mode "
            "before a source-coverage closeout"
        )
    return ""


def source_coverage_modes_compatible(
    recorded_mode: object, current_mode: object
) -> bool:
    """Return whether prior coverage scope is at least as strong as current.

    Deep all-prose evidence contains the ordinary named-theory subset.  A
    transition from deep to named may therefore retain per-item judgments when
    their source semantic and elaborated Lean signature pins are current.  The
    reverse transition always needs review of newly in-scope prose.
    """

    recorded = str(recorded_mode or "").strip()
    current = str(current_mode or "").strip()
    return recorded == current or (
        recorded == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        and current == NAMED_THEORETICAL_STATEMENTS
    )


def deep_source_coverage_attestation_error(map_payload: object, mode: str) -> str:
    """Return the required deep-mode inventory-completeness error, if any.

    A normal named-theory inventory is complete when all named theoretical
    statements have been mapped.  A deep all-prose inventory cannot establish
    that from its JSON items alone, so it requires a source-pinned explicit
    attestation that the full paper was screened.
    """

    if mode != DEEP_PAPER_WITH_ALL_PROSE_CLAIMS:
        return ""
    if not isinstance(map_payload, dict):
        return "deep source coverage requires a readable paper_statement_map.json"
    attestation = map_payload.get("source_prose_inventory_review")
    if not isinstance(attestation, dict):
        return (
            "deep source coverage requires source_prose_inventory_review with "
            "a source-pinned complete: true attestation"
        )
    if attestation.get("complete") is not True:
        return "deep source coverage requires source_prose_inventory_review.complete: true"
    for field in ("validator", "validated_at", "method"):
        if not isinstance(attestation.get(field), str) or not attestation[field].strip():
            return f"deep source coverage requires source_prose_inventory_review.{field}"
    expected_digest = str(map_payload.get("source_artifact_sha256") or "").strip().lower()
    recorded_digest = str(attestation.get("source_artifact_sha256") or "").strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", expected_digest):
        return "deep source coverage requires a canonical source_artifact_sha256"
    if recorded_digest != expected_digest:
        return (
            "deep source coverage requires source_prose_inventory_review "
            "to pin the current source_artifact_sha256"
        )
    return ""


def source_named_presentation_in_coverage_scope(
    presentation_kind: object, mode: str
) -> bool:
    """Whether one independently discovered named presentation is in scope.

    This applies the ordinary/deep policy to source-index results, rather than
    to source-map keys or a map item's declared kind. Unclassified named
    presentations intentionally remain in scope: they must be reported and
    classified before closeout instead of disappearing behind the normal-mode
    exclusion for known standalone displays.
    """

    kind = str(presentation_kind or "").strip().lower()
    if not kind:
        return False
    if mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS:
        return True
    return kind not in NORMAL_SCOPE_EXCLUDED_STANDALONE_SOURCE_KINDS


def source_item_has_explicit_nonordinary_obligation(item: object) -> bool:
    """Whether an explicit correction or source-scope exception stays selected.

    This retention lane is deliberately independent of source-result matching.
    It preserves source-facing dispositions such as corrected targets and
    user-approved exclusions without allowing a map key, declared source kind,
    or Lean route to create ordinary theorem coverage.
    """

    if not isinstance(item, Mapping):
        return False
    if (
        str(item.get("coverage_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
    ):
        return True
    if (
        str(item.get("source_kind") or "").strip().lower() == "open_problem"
        and str(item.get("source_scope_classification") or "").strip().lower()
        == SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
    ):
        return True
    return (
        item.get("corrected_target") is not None
        or item.get(USER_APPROVED_SCOPE_EXCLUSION_KEY) is not None
    )


def source_item_has_explicit_corrected_obligation(item: object) -> bool:
    """Whether an out-of-scope presentation still owns a corrected proof target.

    Corrected targets remain proof obligations even when the archival source
    presentation is not independently selected by ordinary named-theory
    coverage.  User-approved exclusions are deliberately not included here:
    their approval and source pins remain auditable, but they do not acquire a
    theorem proof merely by being retained in the source inventory.
    """

    if not isinstance(item, Mapping):
        return False
    return (
        str(item.get("coverage_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
        or str(item.get("source_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
        or item.get("corrected_target") is not None
    )


def _source_index_presentation_kinds(
    map_payload: Mapping[str, object],
) -> tuple[object | None, object | None]:
    """Return receipt-owned source classifications without consulting map rows."""

    review = map_payload.get("source_named_result_inventory_review")
    if not isinstance(review, Mapping):
        return None, None
    return review.get("environment_kinds"), review.get("heading_kinds")


def _source_index_candidate_dispositions(
    map_payload: Mapping[str, object],
) -> object | None:
    """Return the reviewed candidate ledger, or ``None`` for legacy intake."""

    review = map_payload.get("source_named_result_inventory_review")
    if not isinstance(review, Mapping) or "candidate_presentations" not in review:
        return None
    return review.get("candidate_presentations")


def _current_canonical_text_source(
    folder: Path,
    map_payload: Mapping[str, object],
    *,
    repository_root: Path | None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> tuple[str, str, str] | None:
    """Read a current text/TeX artifact only when its canonical pin verifies.

    A source-map row is never allowed to select itself from an old quote or a
    different file.  This helper mirrors the repository/paper-relative path
    policy used by the evidence validator, but returns no candidate on any
    ambiguity so the semantic selection lane fails closed.
    """

    # A scanned-PDF companion does not create a second candidate source.  Its
    # byte-pinned text transcript is the map's canonical artifact, and the
    # visual scans/page map are validated before source-only discovery is
    # allowed to parse that text.
    if source_text_companion_validation_issues(
        folder,
        map_payload,
        repository_root=repository_root,
        require_source_bytes=True,
        file_bytes_override=file_bytes_override,
    ):
        return None
    # Archive-backed sources may expose a deterministic current text surface,
    # but only after the pinned archive proves every member that generated it.
    # Without that provenance, an extracted local TeX copy is not a source
    # input for ordinary named-result selection.
    if source_archive_surface_validation_issues(
        folder,
        map_payload,
        repository_root=repository_root,
        require_source_bytes=True,
        file_bytes_override=file_bytes_override,
    ):
        return None
    raw_path = map_payload.get("source_artifact_path")
    raw_digest = map_payload.get("source_artifact_sha256")
    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    if not isinstance(raw_digest, str) or not _SHA256_RE.fullmatch(raw_digest.strip()):
        return None
    declared_path = raw_path.strip()
    relative_path = Path(declared_path)
    if relative_path.is_absolute() or relative_path.suffix.lower() not in {
        ".tex",
        ".txt",
        ".md",
    }:
        return None
    if relative_path.parts[:1] == ("papers",):
        if repository_root is None:
            return None
        anchor = repository_root
    else:
        anchor = folder
    try:
        paper_root = folder.resolve()
        artifact_path = (anchor / relative_path).resolve()
        artifact_path.relative_to(paper_root)
        if file_bytes_override is None:
            raw_bytes = artifact_path.read_bytes()
        else:
            if artifact_path not in file_bytes_override:
                return None
            raw_bytes = file_bytes_override[artifact_path]
            if not isinstance(raw_bytes, bytes):
                return None
    except (OSError, RuntimeError, ValueError):
        return None
    if hashlib.sha256(raw_bytes).hexdigest() != raw_digest.strip().lower():
        return None
    try:
        source_text = raw_bytes.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")
    except UnicodeDecodeError:
        return None
    source_format = "tex" if artifact_path.suffix.lower() == ".tex" else "text"
    return source_text, declared_path, source_format


def current_canonical_text_source(
    folder: Path,
    map_payload: Mapping[str, object],
    *,
    repository_root: Path | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> tuple[str, str, str] | None:
    """Return the canonical source text through the shared strict resolver.

    Writer-side intake preparation and reader-side evidence validation must not
    implement different artifact/path rules.  This narrow public wrapper lets
    both consume the existing companion/archive-aware resolver without
    exposing map-row, Lean-route, or audit-gate behavior.
    """

    return _current_canonical_text_source(
        folder,
        map_payload,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )


def _normalized_exact_source_path(value: object) -> str:
    raw = str(value or "").replace("\\", "/").strip()
    while raw.startswith("./"):
        raw = raw[2:]
    if (
        not raw
        or raw.startswith("/")
        or re.match(r"^[A-Za-z]:/", raw)
        or ".." in raw.split("/")
    ):
        return ""
    normalized = posixpath.normpath(raw)
    if normalized in {"", ".", ".."} or normalized.startswith("../"):
        return ""
    return normalized


def _current_source_anchor_span(
    anchor: object, *, source_text: str, source_path: str
) -> tuple[int, int] | None:
    """Return an anchor's span only when it is the exact current source slice."""

    if not isinstance(anchor, Mapping):
        return None
    path = anchor.get("path")
    line_start = anchor.get("line_start")
    line_end = anchor.get("line_end")
    quote = anchor.get("quoted_text")
    digest = anchor.get("quoted_text_sha256")
    if (
        not isinstance(path, str)
        or _normalized_exact_source_path(path)
        != _normalized_exact_source_path(source_path)
        or not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
        or line_start < 1
        or line_end < line_start
        or not isinstance(quote, str)
        or not quote
        or not isinstance(digest, str)
        or not _SHA256_RE.fullmatch(digest.strip())
    ):
        return None
    normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
    if (
        hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
        != digest.strip().lower()
    ):
        return None
    lines = source_text.split("\n")
    if source_text.endswith("\n"):
        lines.pop()
    if line_end > len(lines):
        return None
    if normalized_quote != "\n".join(lines[line_start - 1 : line_end]):
        return None
    return line_start, line_end


def _item_has_current_anchor_containing_span(
    item: Mapping[str, object],
    span: tuple[int, int],
    *,
    source_text: str,
    source_path: str,
) -> bool:
    anchors = item.get("source_anchor_evidence")
    if not isinstance(anchors, list):
        return False
    return any(
        (anchor_span := _current_source_anchor_span(
            anchor, source_text=source_text, source_path=source_path
        ))
        is not None
        and anchor_span[0] <= span[0]
        and span[1] <= anchor_span[1]
        for anchor in anchors
    )


def _source_standard_term_interpretation_bindings(
    raw_items: Mapping[object, object],
    *,
    source_text: str,
    source_path: str,
    inventory_validator: str,
) -> tuple[set[str], list[str]]:
    """Return vocabulary rows with a valid external-standard-term relation.

    The relation is an exception only to the prose-definition inventory's
    requirement that a vocabulary row reconcile to a source-provided
    definition. It is not a general source-coverage shortcut: only a
    definition/predicate-vocabulary row, with a current literal source use and
    an independent semantic review, can receive this route.
    """

    accepted_item_ids: set[str] = set()
    errors: list[str] = []
    for raw_item_id, raw_item in raw_items.items():
        item_id = str(raw_item_id).strip()
        if not item_id or not isinstance(raw_item, Mapping):
            continue
        if SOURCE_STANDARD_TERM_INTERPRETATION_FIELD not in raw_item:
            continue
        prefix = f"items.{item_id}.{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD}"
        item_errors = source_standard_term_interpretation_errors(
            raw_item,
            source_text=source_text,
            source_path=source_path,
            inventory_validator=inventory_validator,
        )
        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        if source_kind not in SOURCE_VOCABULARY_KINDS:
            item_errors.append(
                "standard-term interpretation may exempt only a source_kind "
                "definition or predicate_vocabulary row"
            )
        if raw_item.get("claim_bearing") is False:
            item_errors.append(
                "a standard-term vocabulary row cannot be non-claim-bearing"
            )
        if raw_item.get(SOURCE_PRESENTATION_ALIAS_FIELD) is not None:
            item_errors.append(
                "a presentation alias cannot own a standard-term interpretation"
            )
        if item_errors:
            errors.extend(f"{prefix}: {error}" for error in item_errors)
            continue
        accepted_item_ids.add(item_id)
    return accepted_item_ids, sorted(set(errors))


def _source_prose_definition_reconciliation(
    folder: Path,
    map_payload: object,
    *,
    repository_root: Path | None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> tuple[set[str], list[str]]:
    """Reconcile source-only prose definitions to opaque source-map items.

    This lane is opt-in through the existing independent named-presentation
    receipt.  Once enabled, every extracted presentation and every item binding
    must be one-to-one and current.  No source-map key, Lean route, or declared
    source kind is evidence that the definition exists; the kind is checked
    only after the exact source presentation has selected an item.
    """

    if not isinstance(map_payload, Mapping):
        return set(), []
    raw_items_for_standard_term_check = map_payload.get("items")
    uses_standard_term_interpretation = isinstance(
        raw_items_for_standard_term_check, Mapping
    ) and any(
        isinstance(item, Mapping)
        and SOURCE_STANDARD_TERM_INTERPRETATION_FIELD in item
        for item in raw_items_for_standard_term_check.values()
    )
    review = map_payload.get(_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD)
    if not isinstance(review, Mapping):
        if uses_standard_term_interpretation:
            return set(), [
                f"{SOURCE_STANDARD_TERM_INTERPRETATION_FIELD} requires "
                f"{_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD} so the "
                "source-provided-definition claim can be independently checked"
            ]
        return set(), []
    if SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD not in review:
        return set(), [
            f"{_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD}."
            f"{SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD} must be an explicit "
            "source-only list (empty when no prose definitions were found)"
        ]
    raw_presentations = review.get(SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD)
    errors: list[str] = []
    if not isinstance(raw_presentations, list):
        return set(), [
            f"{_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD}."
            f"{SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD} must be a list"
        ]
    if review.get("complete") is not True:
        errors.append(
            "prose-definition inventory requires the source-only receipt to be complete"
        )
    inventory_validator = str(review.get("validator") or "").strip()
    recorded_source_digest = str(
        review.get("source_artifact_sha256") or ""
    ).strip().lower()
    current_source_digest = str(
        map_payload.get("source_artifact_sha256") or ""
    ).strip().lower()
    if (
        not _SHA256_RE.fullmatch(recorded_source_digest)
        or recorded_source_digest != current_source_digest
    ):
        errors.append("prose-definition inventory does not pin the current source artifact")
    current_source = _current_canonical_text_source(
        folder,
        map_payload,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    if current_source is None:
        errors.append("prose-definition inventory cannot read the exact current source artifact")
        return set(), sorted(set(errors))
    source_text, source_path, _source_format = current_source

    current_digest = source_prose_definition_presentations_sha256(raw_presentations)
    recorded_digest = str(
        review.get(SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD) or ""
    ).strip().lower()
    if not current_digest or recorded_digest != current_digest:
        errors.append(
            f"{_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD}."
            f"{SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD} does not match "
            "the source-only prose-definition inventory"
        )

    presentations_by_digest: dict[str, Mapping[str, object]] = {}
    presentation_spans: dict[str, tuple[int, int]] = {}
    for index, raw_presentation in enumerate(raw_presentations):
        prefix = (
            f"{_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD}."
            f"{SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD}[{index}]"
        )
        presentation_errors = source_prose_definition_presentation_errors(
            raw_presentation
        )
        if (
            isinstance(raw_presentation, Mapping)
            and str(raw_presentation.get("scope_disposition") or "").strip().lower()
            in {
                SOURCE_PROSE_DEFINITION_REPEATED_SCOPE,
                *SOURCE_PROSE_DEFINITION_EXCLUDED_SCOPE_DISPOSITIONS,
            }
            and inventory_validator
            and str(raw_presentation.get("validator") or "").strip()
            == inventory_validator
        ):
            presentation_errors.append(
                "scope/restatement judgment validator must be independent from "
                "the source inventory extractor"
            )
        errors.extend(f"{prefix}: {error}" for error in presentation_errors)
        if presentation_errors or not isinstance(raw_presentation, Mapping):
            continue
        digest = source_prose_definition_presentation_sha256(raw_presentation)
        if digest in presentations_by_digest:
            errors.append(
                f"{prefix}: duplicate prose-definition presentation identity"
            )
            continue
        span = _current_source_anchor_span(
            raw_presentation.get("source_anchor"),
            source_text=source_text,
            source_path=source_path,
        )
        if span is None:
            errors.append(
                f"{prefix}: source_anchor is not the exact current source slice"
            )
            continue
        presentations_by_digest[digest] = raw_presentation
        presentation_spans[digest] = span

    for digest, presentation in presentations_by_digest.items():
        if (
            str(presentation.get("scope_disposition") or "").strip().lower()
            != SOURCE_PROSE_DEFINITION_REPEATED_SCOPE
        ):
            continue
        canonical_digest = str(
            presentation.get("canonical_presentation_sha256") or ""
        ).strip().lower()
        canonical = presentations_by_digest.get(canonical_digest)
        if canonical_digest == digest:
            errors.append(
                "a repeated prose definition cannot designate itself as canonical"
            )
        elif canonical is None:
            errors.append(
                "a repeated prose definition does not designate a presentation in "
                "the current complete ledger"
            )
        elif (
            str(canonical.get("scope_disposition") or "").strip().lower()
            != SOURCE_PROSE_DEFINITION_NORMAL_SCOPE
        ):
            errors.append(
                "a repeated prose definition must designate one canonical normal-scope "
                "definition, not another alias or excluded presentation"
            )

    raw_items = map_payload.get("items")
    if not isinstance(raw_items, Mapping):
        errors.append("prose-definition inventory requires a source-map items object")
        return set(), sorted(set(errors))
    standard_term_item_ids, standard_term_errors = (
        _source_standard_term_interpretation_bindings(
            raw_items,
            source_text=source_text,
            source_path=source_path,
            inventory_validator=inventory_validator,
        )
    )
    errors.extend(standard_term_errors)
    item_ids_by_digest: dict[str, list[str]] = {}
    reconciled_item_ids: set[str] = set()
    for raw_item_id, raw_item in raw_items.items():
        item_id = str(raw_item_id).strip()
        if not item_id or not isinstance(raw_item, Mapping):
            continue
        reconciliation = raw_item.get(SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD)
        if reconciliation is None:
            continue
        prefix = f"items.{item_id}.{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD}"
        reconciliation_errors = source_prose_definition_reconciliation_errors(
            raw_item
        )
        errors.extend(f"{prefix}: {error}" for error in reconciliation_errors)
        if reconciliation_errors or not isinstance(reconciliation, Mapping):
            continue
        if (
            inventory_validator
            and str(reconciliation.get("validator") or "").strip()
            == inventory_validator
        ):
            errors.append(
                f"{prefix}: semantic-equivalence validator must be independent "
                "from the source inventory extractor"
            )
            continue
        digest = str(reconciliation.get("presentation_sha256") or "").strip().lower()
        presentation = presentations_by_digest.get(digest)
        span = presentation_spans.get(digest)
        if presentation is None or span is None:
            errors.append(
                f"{prefix}: presentation_sha256 is not in the current source-only inventory"
            )
            continue
        if (
            str(presentation.get("scope_disposition") or "").strip().lower()
            != SOURCE_PROSE_DEFINITION_NORMAL_SCOPE
        ):
            errors.append(
                f"{prefix}: an excluded prose-definition presentation cannot own "
                "a normal-scope source-map binding"
            )
            continue
        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        if source_kind not in SOURCE_VOCABULARY_KINDS:
            errors.append(
                f"{prefix}: exact prose-definition presentation is attached to "
                "an item not classified as definition/predicate_vocabulary"
            )
        if raw_item.get("claim_bearing") is False:
            errors.append(
                f"{prefix}: a source-presented definition cannot be non-claim-bearing"
            )
        if raw_item.get(SOURCE_PRESENTATION_ALIAS_FIELD) is not None:
            errors.append(f"{prefix}: a presentation alias cannot own a prose definition")
        if not _item_has_current_anchor_containing_span(
            raw_item,
            span,
            source_text=source_text,
            source_path=source_path,
        ):
            errors.append(
                f"{prefix}: the exact definition span is not contained in this "
                "item's current source_anchor_evidence"
            )
        item_ids_by_digest.setdefault(digest, []).append(item_id)
        reconciled_item_ids.add(item_id)

    for digest, presentation in presentations_by_digest.items():
        if (
            str(presentation.get("scope_disposition") or "").strip().lower()
            != SOURCE_PROSE_DEFINITION_NORMAL_SCOPE
        ):
            continue
        matched_items = item_ids_by_digest.get(digest, [])
        if len(matched_items) != 1:
            defined_object = str(presentation.get("defined_object") or "").strip()
            errors.append(
                "source-only prose definition `"
                + defined_object
                + "` must reconcile to exactly one source-map item; found "
                + str(len(matched_items))
            )

    # Once a paper opts into this lane, a direct source-definition row that is
    # not already visible as a conventional Definition heading may not evade
    # it through a curator-set source_kind. Support-only external vocabulary is
    # the narrow non-endpoint exception already defined by the route policy.
    # A valid standard-term interpretation is the only other exception: it is
    # source-pinned to a literal use and independently reviewed precisely
    # because the source does not define the term in its own prose.
    for raw_item_id, raw_item in raw_items.items():
        item_id = str(raw_item_id).strip()
        if not item_id or not isinstance(raw_item, dict):
            continue
        # A source-presentation alias has already been reconciled to its
        # canonical definition/result.  It is provenance for a repeated
        # visible presentation, not an independently prose-defined
        # vocabulary item, so it must not enter this one-to-one binding lane.
        if raw_item.get(SOURCE_PRESENTATION_ALIAS_FIELD) is not None:
            continue
        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        if source_kind not in SOURCE_VOCABULARY_KINDS:
            continue
        if source_item_effective_route_policy(raw_item)[
            "external_support_only_vocabulary"
        ]:
            continue
        if source_item_is_named_theoretical_statement(raw_item):
            continue
        if (
            item_id not in reconciled_item_ids
            and item_id not in standard_term_item_ids
        ):
            errors.append(
                f"items.{item_id}: prose-presented source definition lacks a "
                f"{SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD} binding"
            )

    if errors:
        return set(), sorted(set(errors))
    return reconciled_item_ids | standard_term_item_ids, []


def source_prose_definition_inventory_errors(
    folder: Path,
    map_payload: object,
    *,
    repository_root: Path | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[str]:
    """Return fail-closed source-only prose-definition reconciliation errors."""

    _item_ids, errors = source_vocabulary_definition_binding_item_ids(
        folder,
        map_payload,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    return errors


def source_prose_definition_alias_pairs(
    folder: Path,
    map_payload: object,
    *,
    repository_root: Path | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> dict[str, str]:
    """Bind repeated prose aliases through the current source-only inventory.

    Prose definitions need no numbered heading.  A map alias is supported only
    when its exact source span belongs to an independently reviewed repetition
    whose canonical presentation owns the named map target's normal binding.
    This recognizes source provenance, not a Lean semantic judgment.
    """

    if not isinstance(map_payload, Mapping):
        return {}
    if source_prose_definition_inventory_errors(
        folder, map_payload, repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    ):
        return {}
    aliases, errors = source_presentation_aliases(map_payload.get("items"))
    if errors or not aliases:
        return {}
    current_source = _current_canonical_text_source(
        folder, map_payload, repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    if current_source is None:
        return {}
    source_text, source_path, _source_format = current_source
    review = map_payload.get(_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD)
    if not isinstance(review, Mapping):
        return {}
    records = review.get(SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD, [])
    items = map_payload["items"]
    supported: dict[str, str] = {}
    for alias, canonical in aliases.items():
        binding = items[canonical].get(SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD)
        if not isinstance(binding, Mapping):
            continue
        matches = []
        for record in records:
            if record.get("scope_disposition") != SOURCE_PROSE_DEFINITION_REPEATED_SCOPE:
                continue
            if record.get("canonical_presentation_sha256") != binding.get("presentation_sha256"):
                continue
            span = _current_source_anchor_span(
                record.get("source_anchor"), source_text=source_text,
                source_path=source_path,
            )
            if span is not None and _item_has_current_anchor_containing_span(
                items[alias], span, source_text=source_text, source_path=source_path,
            ):
                matches.append(record)
        if len(matches) == 1:
            supported[alias] = canonical
    return supported


def source_vocabulary_definition_binding_item_ids(
    folder: Path,
    map_payload: object,
    *,
    repository_root: Path | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> tuple[set[str], list[str]]:
    """Return source-validated prose-definition or standard-term bindings.

    This is a source-domain selector, not a Lean-route selector.  An item is
    returned only after the existing complete inventory, exact current source
    anchor, independent reconciliation/standard-term review, vocabulary-kind,
    non-alias, and claim-bearing checks all pass.  Callers may subsequently
    use the opaque item identity with an explicit source-map route, but a map
    key, declaration spelling, or route alone cannot enter this lane.
    """

    return _source_prose_definition_reconciliation(
        folder,
        map_payload,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )


def source_prose_definition_replaced_named_presentation_spans(
    folder: Path,
    map_payload: object,
    presentations: object,
    *,
    repository_root: Path | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> set[tuple[int, int]]:
    """Return named Definition spans genuinely replaced by prose components.

    A prose-definition ledger refines only a named ``definition`` presentation
    that contains (or is contained by) that ledger's independently pinned
    source span.  It must not make an unrelated conventional ``Definition n``
    disappear merely because another definition is introduced in prose
    elsewhere in the paper.  This decision uses only current source bytes and
    the source-only ledger, never a map key or Lean route.
    """

    if not isinstance(map_payload, Mapping) or not isinstance(presentations, list):
        return set()
    _item_ids, errors = source_vocabulary_definition_binding_item_ids(
        folder,
        map_payload,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    if errors:
        return set()
    current_source = _current_canonical_text_source(
        folder,
        map_payload,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    if current_source is None:
        return set()
    source_text, source_path, _source_format = current_source
    review = map_payload.get(_SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD)
    if not isinstance(review, Mapping):
        return set()
    raw_definitions = review.get(SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD)
    if not isinstance(raw_definitions, list):
        return set()
    component_spans: set[tuple[int, int]] = set()
    for raw_definition in raw_definitions:
        if not isinstance(raw_definition, Mapping):
            continue
        if (
            str(raw_definition.get("scope_disposition") or "").strip().lower()
            != SOURCE_PROSE_DEFINITION_NORMAL_SCOPE
        ):
            continue
        span = _current_source_anchor_span(
            raw_definition.get("source_anchor"),
            source_text=source_text,
            source_path=source_path,
        )
        if span is not None:
            component_spans.add(span)
    if not component_spans:
        return set()

    replaced: set[tuple[int, int]] = set()
    for presentation in presentations:
        kind = str(getattr(presentation, "kind", "")).strip().lower()
        line_start = getattr(presentation, "line_start", None)
        line_end = getattr(presentation, "line_end", None)
        if (
            kind != "definition"
            or not isinstance(line_start, int)
            or not isinstance(line_end, int)
        ):
            continue
        if any(
            (component_start <= line_start and line_end <= component_end)
            or (line_start <= component_start and component_end <= line_end)
            for component_start, component_end in component_spans
        ):
            replaced.add((line_start, line_end))
    return replaced


def source_index_byte_pinned_anchor_item_ids(
    folder: Path,
    map_payload: object,
    mode: str,
    *,
    repository_root: Path | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> set[str]:
    """Select map rows by current source index and exact byte-pinned anchors.

    This is intentionally stricter than the legacy map-row selector.  It uses
    only the current canonical text/TeX artifact, source-pinned presentation
    extraction, and anchors whose verified source span covers exactly one
    in-scope presentation.  Map keys are returned only as opaque identifiers;
    no key, ``source_kind``, statement prose, or Lean routing field decides
    whether a row matches.  Invalid artifacts, invalid receipt classifications,
    and one anchor/item covering multiple results all select nothing.
    """

    if not isinstance(map_payload, Mapping):
        return set()
    raw_items = map_payload.get("items")
    if not isinstance(raw_items, Mapping):
        return set()
    current_source = _current_canonical_text_source(
        folder,
        map_payload,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    if current_source is None:
        return set()
    source_text, source_path, source_format = current_source
    environment_kinds, heading_kinds = _source_index_presentation_kinds(map_payload)
    try:
        presentation_inventory = reviewed_source_presentation_inventory(
            source_text,
            source_path=source_path,
            source_format=source_format,
            environment_kinds=environment_kinds,
            heading_kinds=heading_kinds,
            candidate_dispositions=_source_index_candidate_dispositions(map_payload),
        )
        presentations = list(presentation_inventory.classified)
    except (TypeError, ValueError):
        return set()
    # Preserve the legacy named-presentation path unless a paper deliberately
    # supplies the source-only component ledger.  That ledger is an opt-in
    # refinement for source files that put more than one definition clause in
    # one physical presentation; it must not make ordinary theorem-only maps
    # acquire a new validation dependency.
    raw_inventory_review = map_payload.get(
        _SOURCE_NAMED_RESULT_INVENTORY_REVIEW_FIELD
    )
    has_prose_definition_ledger = bool(
        isinstance(raw_inventory_review, Mapping)
        and isinstance(
            raw_inventory_review.get(SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD),
            list,
        )
    )
    if has_prose_definition_ledger:
        prose_definition_ids, prose_definition_errors = (
            source_vocabulary_definition_binding_item_ids(
                folder,
                map_payload,
                repository_root=repository_root,
                file_bytes_override=file_bytes_override,
            )
        )
    else:
        prose_definition_ids, prose_definition_errors = set(), []
    # A prose-definition component supersedes only the actual named Definition
    # span it refines.  Other numbered definitions remain normal source claims.
    replaced_definition_spans = source_prose_definition_replaced_named_presentation_spans(
        folder,
        map_payload,
        presentations,
        repository_root=repository_root,
        file_bytes_override=file_bytes_override,
    )
    in_scope_presentations = [
        presentation
        for presentation in presentations
        if source_named_presentation_in_coverage_scope(presentation.kind, mode)
        and not (
            presentation.kind == "definition"
            and (presentation.line_start, presentation.line_end)
            in replaced_definition_spans
        )
    ]
    items: dict[str, object] = {}
    for raw_key, raw_item in raw_items.items():
        item_id = str(raw_key).strip()
        if not item_id or not isinstance(raw_item, Mapping) or item_id in items:
            return set()
        # Reconciliation receives the anchor field alone. In particular, a
        # broad source_location or any map classification/navigation metadata
        # cannot influence this strict selector even incidentally. The optional
        # source-only core record is retained because it is itself exact
        # current source evidence and deliberately replaces broad support/proof
        # anchors for this one selection lane.
        items[item_id] = {
            "source_anchor_evidence": raw_item.get("source_anchor_evidence")
        }
        if SOURCE_PRESENTATION_RECONCILIATION_FIELD in raw_item:
            items[item_id][SOURCE_PRESENTATION_RECONCILIATION_FIELD] = raw_item.get(
                SOURCE_PRESENTATION_RECONCILIATION_FIELD
            )
    reconciliations = reconcile_named_result_presentations(
        in_scope_presentations,
        items,
        source_text=source_text,
        source_path=source_path,
    )
    presentations_by_item: dict[str, set[tuple[str, str, int, int, str]]] = {}
    for reconciliation in reconciliations:
        presentation = reconciliation.presentation
        identity = (
            presentation.kind,
            presentation.label,
            presentation.line_start,
            presentation.line_end,
            presentation.presentation,
        )
        for match in reconciliation.matches:
            if any(
                evidence.startswith("source_anchor_evidence[")
                or evidence == SOURCE_PRESENTATION_RECONCILIATION_FIELD
                for evidence in match.evidence
            ):
                presentations_by_item.setdefault(match.item_id, set()).add(identity)
    selected_item_ids = {
        item_id
        for item_id, matched_presentations in presentations_by_item.items()
        if len(matched_presentations) == 1
    }
    if not prose_definition_errors:
        selected_item_ids.update(prose_definition_ids)
    return selected_item_ids


_SOURCE_RESULT_PRESENTATION_KINDS = frozenset(
    {"theorem", "proposition", "lemma", "corollary", "claim", "runtime_claim"}
)


def _is_explicit_nonclaim_semantic_prerequisite(
    item: object,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
) -> bool:
    """Recognize a typed model/definition route without hiding a result.

    A source definition, model, algorithm, assumption, or condition may be a
    material prerequisite for a selected result without being a second human
    source-claim card.  The source map records that deliberately with a
    role-typed declaration route and ``claim_bearing: false``.  This is not a
    curator escape hatch for a theorem: a directly presented result heading
    still stays on the ordinary result surface and fails closed if marked
    nonclaim.
    """

    if not isinstance(item, Mapping):
        return False
    if item.get("claim_bearing") is not False:
        return False
    if str(item.get("inventory_role") or "").strip() != "source_semantic_declaration":
        return False
    roots = item.get("lean_declarations")
    if (
        not isinstance(roots, list)
        or not roots
        or any(not isinstance(root, str) or not root.strip() for root in roots)
    ):
        return False
    source_text = _source_item_direct_presentation_text(item)
    if not source_text:
        return False
    # A curator cannot relabel a directly printed theorem as a model merely by
    # changing source_kind. This source-only guard recognizes the result
    # presentation before the prerequisite route can exclude it.
    if _source_item_opens_ordinary_named_presentation(
        dict(item), declared_environment_kinds
    ):
        return False
    try:
        presentations = extract_named_result_presentations(
            source_text,
            source_format="auto",
            environment_kinds=declared_environment_kinds,
        )
    except ValueError:
        return False
    return not any(
        presentation.kind in _SOURCE_RESULT_PRESENTATION_KINDS
        for presentation in presentations
    )


def source_item_is_named_theoretical_statement(
    item: object,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
) -> bool:
    """Whether a source item belongs to ordinary named-theory coverage.

    ``source_kind`` records the source-presentation category, but cannot create
    an ordinary-scope obligation by itself.  A named kind needs its own visible
    heading or a self-hashed anchor that opens the corresponding source result.
    A legacy inventory without that field gets a source-text-only fallback; map
    keys, aliases, and Lean routes are deliberately excluded from both paths.
    """

    if not isinstance(item, dict):
        return False
    # A repeated presentation has already been source-only reconciled to its
    # canonical theorem/lemma/definition.  It remains in the full inventory
    # (and its own anchor remains byte-pinned), but it is not a second
    # paper-facing mathematical obligation: alias schema forbids it from
    # owning a direct Lean endpoint.  Selecting it here would force an
    # impossible duplicate coverage route and turn a presentation count into
    # a claim count.
    if item.get(SOURCE_PRESENTATION_ALIAS_FIELD) is not None:
        return False
    # The typed direct route makes this source definition/model/algorithm a
    # reviewable prerequisite.  It is not another theorem denominator row.
    # `_is_explicit_nonclaim_semantic_prerequisite` independently rejects a
    # theorem-like presentation, so this cannot suppress a named result.
    if _is_explicit_nonclaim_semantic_prerequisite(
        item,
        declared_environment_kinds=declared_environment_kinds,
    ):
        return False
    # A prose definition that has passed the source-only reconciliation is a
    # visible source presentation even when the text extractor has no literal
    # ``Definition n`` heading.  Treating it as context solely because its
    # formula is introduced in prose would let a migration hide a definition
    # that the source inventory independently identified.  The reconciliation
    # validator checks the source presentation and byte-pinned relation; no
    # Lean route or map key is used here.
    if (
        item.get(SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD) is not None
        and not source_prose_definition_reconciliation_errors(item)
    ):
        return True
    source_kind = str(item.get("source_kind") or "").strip().lower()
    # A named conjecture/open question is source-visible but is not an
    # ordinary theorem-proof obligation.  Its dedicated source-inventory lane
    # requires claim_bearing: false plus an explicit source-declared-open
    # disposition.  Reclassifying the same heading here as ordinary theory
    # would make those two validators contradictory.
    if source_kind in NAMED_OPEN_SOURCE_KINDS:
        return False
    if source_kind and not source_named_presentation_in_coverage_scope(
        source_kind, NAMED_THEORETICAL_STATEMENTS
    ):
        return _source_item_opens_ordinary_named_presentation(
            item, declared_environment_kinds
        )
    if _source_item_anchor_opens_declared_named_environment(
        item, declared_environment_kinds
    ):
        return True
    if source_kind in _NAMED_THEORETICAL_ALWAYS_SOURCE_KINDS:
        return bool(
            _source_item_directly_presents_named_kind(
                item, source_kind, declared_environment_kinds
            )
            or _source_item_anchor_opens_named_kind(
                item, source_kind, declared_environment_kinds
            )
        )
    if source_kind in {"claim", "runtime_claim"}:
        return bool(
            _source_item_directly_presents_named_kind(
                item, source_kind, declared_environment_kinds
            )
            or _source_item_anchor_opens_named_kind(
                item, source_kind, declared_environment_kinds
            )
        )
    if source_kind in {"formula", "equation", "algorithmic_formula"}:
        source_text = "\n".join(
            [
                _source_item_direct_presentation_text(item),
                *_valid_source_anchor_texts(item),
            ]
        )
        return bool(
            _source_item_directly_presents_named_kind(
                item, source_kind, declared_environment_kinds
            )
            or _source_item_anchor_opens_named_kind(
                item, source_kind, declared_environment_kinds
            )
            or _NAMED_OPERATIVE_PRESENTATION_RE.search(source_text)
            or _NAMED_LABELLED_ITEM_PREFIX_RE.search(
                _source_item_direct_presentation_text(item)
            )
        )
    source_text = "\n".join(
        [
            _source_item_direct_presentation_text(item),
            *_valid_source_anchor_texts(item),
        ]
    )
    if source_kind in _LABEL_REQUIRED_NAMED_SOURCE_KINDS:
        if (
            _NAMED_OPERATIVE_PRESENTATION_RE.search(source_text)
            or _NAMED_LABELLED_ITEM_PREFIX_RE.search(
                _source_item_direct_presentation_text(item)
            )
        ):
            return True
        return False
    # A nonnamed/unknown source_kind cannot suppress a source-labelled result.
    # The heading check keeps ordinary cross-references such as "by Theorem 2"
    # from turning a model-description item into a new theorem obligation.
    return bool(
        _source_item_has_named_heading(item)
        or (
            not source_kind
            and _NAMED_THEORETICAL_PRESENTATION_RE.search(source_text)
        )
    )


def source_item_scope_classification_errors(
    item: object,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
) -> list[str]:
    """Return source-presentation errors that must not be filtered away.

    This is a small structural anti-smuggling gate.  It does not infer a Lean
    route from any name; it catches only conflicts between a source item's
    declared presentation fields and its own visible source text.
    """

    if not isinstance(item, dict):
        return ["source inventory item is not an object"]
    source_kind = str(item.get("source_kind") or "").strip().lower()
    errors: list[str] = []
    if source_kind and source_kind not in KNOWN_SOURCE_PRESENTATION_KINDS:
        errors.append(f"unknown source_kind `{source_kind}`")
    if "source_kind" in item and not isinstance(item.get("source_kind"), str):
        errors.append("source_kind must be a nonempty string when present")
    if "claim_bearing" in item and not isinstance(item.get("claim_bearing"), bool):
        errors.append("claim_bearing must be Boolean when present")
    if source_kind in NAMED_OPEN_SOURCE_KINDS and item.get("claim_bearing") is not False:
        errors.append(
            "a named open-problem source item must set claim_bearing: false and use an explicit source-declared-open disposition"
        )
    # Use the same normal-scope predicate for selection and anti-smuggling.
    # In particular, a visibly numbered proof equation or algorithm remains a
    # deep-only display; its heading cannot independently turn claim_bearing:
    # false into an error.  Conversely, a theorem/lemma/definition disguised
    # as a deep-only row is still selected by its source presentation and
    # therefore fails below.
    ordinary_named_presentation = source_item_is_named_theoretical_statement(
        item, declared_environment_kinds=declared_environment_kinds
    )
    if ordinary_named_presentation and source_kind in (
        DEEP_ONLY_SOURCE_KINDS | NORMAL_SCOPE_EXCLUDED_STANDALONE_SOURCE_KINDS
    ):
        errors.append(
            f"source_kind `{source_kind}` conflicts with a named theoretical source presentation"
        )
    if ordinary_named_presentation and item.get("claim_bearing") is False:
        errors.append(
            "a named theoretical source statement cannot set claim_bearing: false"
        )
    return errors


def source_presentation_aliases(
    raw_items: object,
) -> tuple[dict[str, str], list[str]]:
    """Return valid repeated-presentation aliases and fail closed on malformed ones.

    Some sources restate a named theorem verbatim at the start of a proof
    appendix.  Both visible presentations must remain byte-pinned inventory
    entries, but only the canonical presentation may own a direct Lean route.
    This relation is source-only metadata: the map keys locate the two pinned
    presentations, while the required semantic basis records the independent
    comparison of their hypotheses, scope, and conclusion.
    """

    if not isinstance(raw_items, dict):
        return {}, ["source map `items` must be an object for presentation aliases"]

    aliases: dict[str, str] = {}
    errors: list[str] = []
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_item, dict):
            continue
        relation = raw_item.get(SOURCE_PRESENTATION_ALIAS_FIELD)
        if relation is None:
            continue
        error_count_before = len(errors)
        prefix = f"items.{key}.{SOURCE_PRESENTATION_ALIAS_FIELD}"
        if not isinstance(relation, dict):
            errors.append(f"{prefix} must be an object")
            continue
        if relation.get("schema") != SOURCE_PRESENTATION_ALIAS_SCHEMA:
            errors.append(
                f"{prefix}.schema must be {SOURCE_PRESENTATION_ALIAS_SCHEMA}"
            )
        if relation.get("relation") != SOURCE_PRESENTATION_ALIAS_RELATION:
            errors.append(
                f"{prefix}.relation must be `{SOURCE_PRESENTATION_ALIAS_RELATION}`"
            )
        label_relation = relation.get(SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD)
        if label_relation is None:
            label_relation = SOURCE_PRESENTATION_ALIAS_SAME_VISIBLE_LABEL
        if (
            not isinstance(label_relation, str)
            or label_relation not in VALID_SOURCE_PRESENTATION_ALIAS_LABEL_RELATIONS
        ):
            errors.append(
                f"{prefix}.{SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD} must be one of "
                + ", ".join(sorted(VALID_SOURCE_PRESENTATION_ALIAS_LABEL_RELATIONS))
            )
        elif (
            label_relation
            == SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT
            and not isinstance(
                relation.get(SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD),
                dict,
            )
        ):
            errors.append(
                f"{prefix}.{SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD} "
                "must be a byte-pinned source relation object for a renumbered restatement"
            )
        canonical = str(relation.get("canonical_source_item") or "").strip()
        if not canonical:
            errors.append(f"{prefix}.canonical_source_item is required")
            continue
        if canonical == key:
            errors.append(f"{prefix}.canonical_source_item cannot refer to itself")
            continue
        canonical_item = raw_items.get(canonical)
        if not isinstance(canonical_item, dict):
            errors.append(
                f"{prefix}.canonical_source_item `{canonical}` is not a source-map item"
            )
            continue
        if canonical_item.get(SOURCE_PRESENTATION_ALIAS_FIELD) is not None:
            errors.append(
                f"{prefix}.canonical_source_item `{canonical}` cannot itself be a presentation alias"
            )
            continue
        alias_kind = str(raw_item.get("source_kind") or "").strip().lower()
        canonical_kind = str(canonical_item.get("source_kind") or "").strip().lower()
        if not alias_kind or alias_kind != canonical_kind:
            errors.append(
                f"{prefix} must preserve the canonical source_kind `{canonical_kind or 'missing'}`"
            )
        for field in ("semantic_basis", "validator"):
            if not isinstance(relation.get(field), str) or not relation[field].strip():
                errors.append(f"{prefix}.{field} is required")
        validated_at = str(relation.get("validated_at") or "").strip()
        if not _ISO_LIKE_TIMESTAMP_RE.fullmatch(validated_at):
            errors.append(f"{prefix}.validated_at must be an ISO-like UTC timestamp")
        for route_field in _DIRECT_SOURCE_ROUTE_FIELDS:
            if raw_item.get(route_field) not in (None, []):
                errors.append(
                    f"{prefix} alias item must not own direct `{route_field}` routes"
                )
        if raw_item.get("semantic_contract") is not None:
            errors.append(
                f"{prefix} alias item must not own a semantic_contract direct route"
            )
        if not str(raw_item.get("source_location") or "").strip():
            errors.append(f"items.{key}.source_location is required for a presentation alias")
        if not str(canonical_item.get("source_location") or "").strip():
            errors.append(
                f"items.{canonical}.source_location is required for a presentation-alias canonical item"
            )
        if len(errors) == error_count_before:
            aliases[key] = canonical
    return aliases, sorted(set(errors))


def source_map_uses_conditional_antecedent_subpart_selection(
    map_payload: object,
    *,
    source_texts: tuple[str, ...] = (),
) -> bool:
    """Whether current source material exercises conditional-subpart selection.

    Only the ordinary named-theory surface can be affected.  The predicate
    consults printed presentation text and self-hashed source-anchor excerpts,
    plus a caller-supplied canonical source artifact when available; it never
    relies on source-map identifiers or Lean declarations.
    """

    if not isinstance(map_payload, Mapping):
        return False
    mode, mode_error = source_coverage_mode_from_map(map_payload)
    if mode_error or mode != NAMED_THEORETICAL_STATEMENTS:
        return False
    raw_items = map_payload.get("items")
    if not isinstance(raw_items, Mapping):
        return False
    _environment_kinds, raw_heading_kinds = _source_index_presentation_kinds(
        map_payload
    )
    heading_kinds = (
        raw_heading_kinds if isinstance(raw_heading_kinds, Mapping) else None
    )
    candidate_texts = list(source_texts)
    for raw_item in raw_items.values():
        if not isinstance(raw_item, dict):
            continue
        direct_text = _source_item_direct_presentation_text(raw_item)
        if direct_text:
            candidate_texts.append(direct_text)
        candidate_texts.extend(_valid_source_anchor_texts(raw_item))
    return any(
        source_text_uses_conditional_antecedent_subpart_selection(
            source_text,
            heading_kinds=heading_kinds,
        )
        for source_text in candidate_texts
        if isinstance(source_text, str) and source_text.strip()
    )


def source_item_in_coverage_scope(
    item: object,
    mode: str,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
) -> bool:
    """Return whether one source item is in the configured audit surface."""

    if mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS:
        return isinstance(item, dict)
    return source_item_is_named_theoretical_statement(
        item, declared_environment_kinds=declared_environment_kinds
    )


def filter_source_inventory_for_coverage(
    inventory: dict[str, dict[str, Any]],
    mode: str,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
) -> dict[str, dict[str, Any]]:
    """Return the source-inventory subset selected by the configured mode."""

    return {
        key: item
        for key, item in inventory.items()
        if source_item_in_coverage_scope(
            item,
            mode,
            declared_environment_kinds=declared_environment_kinds,
        )
    }


def filter_source_map_items_for_coverage(
    raw_items: object,
    mode: str,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
) -> dict[str, dict[str, Any]]:
    """Return selected raw source-map items without using their map keys."""

    if not isinstance(raw_items, dict):
        return {}
    return {
        str(key): item
        for key, item in raw_items.items()
        if str(key).strip()
        and isinstance(item, dict)
        and source_item_in_coverage_scope(
            item,
            mode,
            declared_environment_kinds=declared_environment_kinds,
        )
    }


def filter_source_map_items_for_proof_obligations(
    raw_items: object,
    mode: str,
    *,
    declared_environment_kinds: Mapping[str, str] | None = None,
    additional_selected_item_ids: set[str] | frozenset[str] = frozenset(),
) -> dict[str, dict[str, Any]]:
    """Return items that may own direct proof or theorem-realization credit.

    This starts from the same source-presentation selector as coverage.  A
    caller may add item identifiers independently recovered from the current
    byte-pinned source index; those identifiers are routing handles only and
    cannot be inferred from map keys or Lean declaration names.  Corrected
    targets remain explicit proof obligations.  A user-approved exclusion,
    by contrast, remains visible to its dedicated approval/source validators
    but does not become a proof target merely because the full inventory keeps
    it.  An excluded item may retain corrected-target provenance without
    receiving proof credit.  Its dedicated exclusion and correction validators
    still verify the approval, source pins, retained target, and absence of
    active proof routes.

    Repeated-presentation aliases are intentionally left to the consumer.
    Ordinary selection already omits them, while deep-mode and v11 consumers
    may need different levels of source-pin validation before allowing an
    alias to inherit its canonical presentation's proof.
    """

    if not isinstance(raw_items, dict):
        return {}
    selected = filter_source_map_items_for_coverage(
        raw_items,
        mode,
        declared_environment_kinds=declared_environment_kinds,
    )
    for raw_key in additional_selected_item_ids:
        key = str(raw_key).strip()
        raw_item = raw_items.get(key)
        if key and isinstance(raw_item, dict):
            selected[key] = raw_item
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_item, dict):
            continue
        if raw_item.get(USER_APPROVED_SCOPE_EXCLUSION_KEY) is not None:
            selected.pop(key, None)
        elif source_item_has_explicit_corrected_obligation(raw_item):
            selected[key] = raw_item
    return selected


def source_item_coverage_sha256(item: object, mode: str) -> str:
    """Return a source-only, per-item freshness key for coverage reuse.

    This intentionally excludes source-map keys, aliases, and Lean declaration
    identifiers or source locators.  The separate elaborated row-signature
    pins bind the reviewed Lean statement, and current byte-anchor validation
    binds the source quote.  Consequently, changing an unrelated source item,
    moving a map key or line range, or renaming a Lean declaration without
    changing its checked type does not reopen this item's semantic judgment.
    """

    if not isinstance(item, dict):
        return ""
    # Apply the routing projection to the complete item rather than a fixed
    # allowlist.  New source-semantic metadata must invalidate a prior item
    # judgment by default; only explicit navigation/route fields are omitted.
    source_fields = _source_semantic_projection(item, direct_source_item=True)
    # Scope chooses which items are reviewed; it does not alter the source
    # item's mathematical content.  Omitting it here permits a deep review to
    # supply current evidence for the named-theory subset after a deliberate
    # deep-to-normal transition.  The aggregate sidecar still records mode and
    # detects additions/removals.
    del mode
    payload: dict[str, object] = {
        "schema": SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        "source_item": source_fields,
    }
    status_policy = source_item_direct_status_policy_projection(item)
    if status_policy is not None:
        # A current item-level judgment cannot survive a direct status edit
        # that changes its route/quarantine/scope semantics. Neutral wording
        # still produces exactly the established schema-5 digest above.
        payload["direct_source_status_policy"] = status_policy
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), default=str)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _historical_source_item_semantic_projection(
    item: object,
    *,
    retain_direct_administrative_metadata: bool = False,
) -> tuple[dict[str, object] | None, str]:
    """Reconstruct a literal historical corrected-target item representation.

    This helper is used only by the real schema-4/5/6 historical digest
    readers below and in the final holistic assurance reader. The current
    source identity continues to use ``corrected_target_record_projection``.
    """

    if not isinstance(item, dict):
        return None, "source item must be an object"
    candidate = dict(item)
    if "corrected_target" in item:
        historical_target, error = corrected_target_historical_record_projection(
            item["corrected_target"]
        )
        if error:
            return None, error
        candidate["corrected_target"] = historical_target
    projected = _source_semantic_projection(
        candidate,
        direct_source_item=True,
        retain_direct_administrative_metadata=retain_direct_administrative_metadata,
        project_corrected_target_authority=False,
    )
    if not isinstance(projected, dict):  # pragma: no cover - fixed by input check.
        return None, "historical source-item projection is malformed"
    return projected, ""


def legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion(
    item: object, mode: str
) -> str:
    """Reproduce schema 5 while the proof-defect links were duplicated here.

    Every other current projection rule remains exact.  In particular, source
    text, corrected targets, route-changing status policy, and unknown metadata
    still change this identity.  The separate fidelity validator must approve
    the current cross-references before a paper can close.
    """

    if not isinstance(item, dict):
        return ""
    source_fields, historical_error = _historical_source_item_semantic_projection(
        item
    )
    if historical_error or source_fields is None:
        return ""
    if "source_defect_ids" in item:
        source_fields["source_defect_ids"] = _source_semantic_projection(
            item["source_defect_ids"]
        )
    del mode
    payload: dict[str, object] = {
        "schema": PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        "source_item": source_fields,
    }
    status_policy = source_item_direct_status_policy_projection(item)
    if status_policy is not None:
        payload["direct_source_status_policy"] = status_policy
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), default=str)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def legacy_source_item_coverage_sha256_before_navigation_key_exclusion(
    item: object, mode: str
) -> str:
    """Reproduce the key-bearing variant of the preceding schema 5 identity.

    Schema 5 accidentally retained dashboard ``source_item_key`` navigation in
    normalized inventory rows even though its contract excluded map keys. A
    current schema-5 judgment may migrate only when this exact historical
    digest matches the current source item under its still-current key. Once
    rewritten by current tooling, schema 5 is key-free and arbitrary future
    renames need no bridge.
    """

    if not isinstance(item, dict):
        return ""
    source_fields, historical_error = _historical_source_item_semantic_projection(
        item
    )
    if historical_error or source_fields is None:
        return ""
    if "source_defect_ids" in item:
        source_fields["source_defect_ids"] = _source_semantic_projection(
            item["source_defect_ids"]
        )
    if isinstance(source_fields, dict) and "source_item_key" in item:
        source_fields["source_item_key"] = _source_semantic_projection(
            item["source_item_key"]
        )
    del mode
    payload: dict[str, object] = {
        "schema": PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        "source_item": source_fields,
    }
    status_policy = source_item_direct_status_policy_projection(item)
    if status_policy is not None:
        payload["direct_source_status_policy"] = status_policy
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), default=str)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def source_item_coverage_receipt_matches(
    item: object,
    mode: str,
    *,
    digest_schema: object,
    digest: object,
    legacy_navigation_key: str | None = None,
) -> bool:
    """Validate a current or exactly migratable per-item coverage identity."""

    recorded = str(digest or "").strip().lower()
    if not _SHA256_RE.fullmatch(recorded) or not isinstance(item, dict):
        return False
    if digest_schema == SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA:
        return recorded == source_item_coverage_sha256(item, mode)
    if digest_schema != PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA:
        return False
    if recorded == legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion(
        item, mode
    ):
        return True
    candidate = dict(item)
    if legacy_navigation_key is not None:
        candidate["source_item_key"] = legacy_navigation_key
    return recorded == legacy_source_item_coverage_sha256_before_navigation_key_exclusion(
        candidate, mode
    )


def source_item_coverage_receipt_shape_is_reusable(
    *, digest_schema: object, digest: object
) -> bool:
    """Recognize a supported per-item receipt shape without granting credit."""

    return (
        digest_schema
        in {
            SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
            PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        }
        and _SHA256_RE.fullmatch(str(digest or "").strip().lower()) is not None
    )


def legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
    item: object, mode: str
) -> str:
    """Reproduce the immediately preceding per-item digest projection.

    This is deliberately *not* a normal reuse key.  It exists only so a
    separately authenticated administrative-projection rebind can prove that
    a stored schema-2 source identity differs from the current identity solely
    because direct ``source_status`` bookkeeping stopped being semantic input.
    Nested ``source_status`` remains semantic and is therefore retained here
    and in the current projection.
    """

    if not isinstance(item, dict):
        return ""
    source_fields, historical_error = _historical_source_item_semantic_projection(
        item,
        retain_direct_administrative_metadata=True,
    )
    if historical_error or source_fields is None:
        return ""
    del mode
    encoded = json.dumps(
        {
            "schema": LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
            "source_item": source_fields,
        },
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    )
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
    item: object, mode: str
) -> str:
    """Reproduce the schema-4 direct-status-excluded semantic identity.

    This is the immediately preceding projection for raw audits that had
    already removed direct ``source_status`` bookkeeping before the digest
    schema itself was versioned to 5.  It is not an ordinary freshness key:
    the only supported consumer is a separately authenticated exact
    schema-4-to-schema-5 association transport receipt.
    """

    if not isinstance(item, dict):
        return ""
    source_fields, historical_error = _historical_source_item_semantic_projection(
        item
    )
    if historical_error or source_fields is None:
        return ""
    del mode
    encoded = json.dumps(
        {
            "schema": LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
            "source_item": source_fields,
        },
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    )
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()
