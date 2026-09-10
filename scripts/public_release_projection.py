#!/usr/bin/env python3
"""Create deterministic public-safe projections of reviewed release artifacts.

This module is deliberately a bounded projection, not a general-purpose
redactor.  It knows how to remove private audit provisioning fields and how to
neutralize private audit provenance while preserving the small, explicitly
approved set of contributor workflow guides.  It preserves source URLs, hashes,
line spans, and verbatim source excerpts.  If an unsafe value occurs outside
one of those explicit rules, the projection fails instead of silently
publishing a best-effort result.

The release guard is expected to invoke :func:`project_bytes` against the
reviewed private blob and compare its result with the candidate blob.  This
file intentionally has no repository or Git dependency so that the guard can
use the same deterministic transformation under isolation.
"""

from __future__ import annotations

import argparse
from html import unescape as html_unescape
import hashlib
import json
import re
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence
from urllib.parse import unquote

try:
    from corrected_target_identity import (
        CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD,
        CORRECTED_TARGET_RECORD_SHA256_FIELD,
        CORRECTED_TARGET_REVIEW_SHA256_FIELD,
        corrected_target_approval_excerpt_material,
        corrected_target_original_artifact_path_error,
        corrected_target_record_digest,
        corrected_target_review_digest,
    )
except ModuleNotFoundError:  # Module-style import.
    from scripts.corrected_target_identity import (
        CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD,
        CORRECTED_TARGET_RECORD_SHA256_FIELD,
        CORRECTED_TARGET_REVIEW_SHA256_FIELD,
        corrected_target_approval_excerpt_material,
        corrected_target_original_artifact_path_error,
        corrected_target_record_digest,
        corrected_target_review_digest,
    )


PUBLIC_PROJECTION_GENERATOR = "python3 scripts/public_release_projection.py"
PUBLICATION_LOCATOR = "cited publication"
PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD = "publication_source_display_projection"
PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA = 1
PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST = (
    "audit/public_source_display_projection.json"
)
PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD = "publication_corrected_target_projection"
PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA = 1
PUBLIC_WITHHELD_APPROVAL_REFERENCE = (
    "The underlying approval record is withheld from this public projection."
)

# These are deliberately public contributor instructions.  They explain how
# to use ignored local caches, resumable handoffs, and the private/public
# release boundary, but contain neither source artifacts nor session exports.
# Keep this a path allowlist: other session-derived or local-workflow material
# must still pass the ordinary public projection and guard checks.
PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS = frozenset(
    {
        "skills/econcs-session-insights/SKILL.md",
        "skills/econcs-formalizer/SKILL.md",
        "skills/econcs-formalizer/references/audit-and-closeout.md",
        "skills/econcs-formalizer/references/final-closure-receipt.md",
        "skills/econcs-formalizer/references/formalization-architecture.md",
        "skills/econcs-formalizer/references/formalization-handbook.md",
        "skills/econcs-formalizer/references/human-facing-artifacts.md",
        "skills/econcs-formalizer/references/intake-and-source-surface.md",
        "skills/econcs-formalizer/references/post-formalization-closeout.md",
        "skills/econcs-formalizer/references/proof-algorithms-complexity.md",
        "skills/econcs-formalizer/references/proof-algorithms-online.md",
        "skills/econcs-formalizer/references/proof-foundations-math.md",
        "skills/econcs-formalizer/references/proof-foundations-optimization.md",
        "skills/econcs-formalizer/references/proof-foundations-probability.md",
        "skills/econcs-formalizer/references/proof-markets-social-choice.md",
        "skills/econcs-formalizer/references/proof-mechanism-design.md",
        "skills/econcs-formalizer/references/proof-recommender-systems.md",
        "skills/econcs-formalizer/references/proof-strategies.md",
        "skills/econcs-formalizer/references/public-private-sync.md",
        "skills/econcs-formalizer/references/release-and-sync.md",
        "skills/econcs-formalizer/references/shared-library-development.md",
        "skills/econcs-formalizer/templates/FORMALIZATION_PLAN.md",
        "skills/econcs-prover/SKILL.md",
        "skills/econcs-prover/references/proving-workflow-provenance.md",
        "skills/econcs-shared-worktree/SKILL.md",
        "skills/lean-community-conventions/SKILL.md",
        "skills/lean-community-conventions/references/econcs-adoption-plan.md",
        "docs/AGENT_FORMALIZATION_WORKFLOW.md",
        "docs/ARCHITECTURE.md",
        "docs/FORMALIZATION_AUDIT_PROCEDURE_OVERVIEW.tex",
        "docs/NEW_CONTRIBUTOR_WORKFLOW.md",
        "docs/INDEPENDENT_AUDIT_GUIDE.md",
        "docs/PRIVATE_DEVELOPMENT_WORKFLOW.md",
        "docs/PUBLIC_RELEASE_CHECKLIST.md",
        "docs/PUBLIC_REPOSITORY_WORKFLOW.md",
        "docs/REVIEW_DASHBOARD.md",
        "docs/REPOSITORY_LAUNCH_PLAN.md",
        "docs/PAPER_STATUS.md",
        "docs/STATUS.md",
        "docs/VALIDATION_MODEL.md",
        "docs/contributing/README.md",
        "config/formalization_engine_revisions.json",
    }
)

# This one sentence is public contributor guidance on the generated landing
# page.  It names the recommended private-first workflow, but contains no
# private repository locator, source artifact, or session record.  Keep the
# exception literal and path-bound: other private-workflow wording on the site
# still receives ordinary projection and hygiene checks.
_PUBLIC_SITE_PRIVATE_WORKFLOW_GUIDANCE = (
    "New paper formalizations should start in a private workflow and be\n"
    "            proposed to enter the library through a pull request when ready."
)
_PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL = "__APPROVED_PUBLIC_WORKFLOW_GUIDANCE__"
PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE = (
    "General lessons from private workflow examples are incorporated into the\n"
    "  public skills; the underlying wiki and feedback history remain private."
)


class ProjectionError(ValueError):
    """Raised when an artifact cannot be projected safely and deterministically."""


# These values are private implementation/provisioning details, rather than
# public mathematical provenance.  Source hashes and line spans are retained.
_DROP_FIELDS = frozenset(
    {
        "canonical_source_audit",
        "draft_fingerprint",
        "extracted_tex_path",
        "local_build_pdf",
        "signature_cache",
        "source_archive_surface",
        "source_artifact_path",
        "source_artifact_provisioning",
        "source_text_file",
        "source_text_companion",
        "source_transcript",
        "text_extraction",
        "companion_html_path",
    }
)

# The public name describes the same review surface without publishing the
# remediation history that created it.
_KEY_RENAMES = {
    # These records are strict private source-audit schemas: their anchors
    # intentionally require a locally readable byte-pinned path.  Public
    # release maps instead carry a display-only copy with publication
    # locators, while the original key remains absent so public renderers do
    # not mistake it for locally re-verifiable audit evidence.
    "source_definition_partition": "publication_source_definition_partition",
    "source_standard_term_interpretation": "publication_standard_term_interpretation",
    "repair_handoff": "scope_note",
    "remediation_note": "review_note",
    "remediation_scope": "review_scope",
    "source_fidelity_remediation": "source_fidelity_review",
}

# A raw quotation is allowed in a public projection only when it remains part
# of a source-bound record.  In particular, a free ``quoted_text`` string must
# not become a blanket escape hatch for arbitrary local workflow content.
_EXCERPT_FIELDS = frozenset({"quoted_text", "source_excerpt", "source_quote"})

# Anchor handling is deliberately field-name based.  Source-map item IDs are
# arbitrary semantic identifiers and may themselves end in ``_anchor``; they
# must never acquire source-excerpt privileges or bypass the normal recursive
# projection merely because of that suffix.
_ANCHOR_FIELDS = frozenset(
    {
        "core_anchor",
        "corrected_clause_anchor",
        "source_anchor",
        "source_restatement_evidence",
        "source_term_use_anchor",
    }
)

_CONTROLLED_TEXT_FIELDS = frozenset(
    {
        "aliases",
        "artifact_kind",
        "artifact_excerpt",
        "artifact_path",
        "archival_source_locator",
        "affected_source_locators",
        "generated_from",
        "curator",
        "llm_judge_prompt",
        "method",
        "policy",
        "presentation_label",
        "provenance",
        "reference",
        "reason",
        "rationale",
        "rule",
        "source_evidence",
        "source_inventory_policy",
        "source_kind_validator",
        "source_location",
        "source_location_policy",
        "source_location_validator",
        "source_locator",
        "source_note",
        "source_curator",
        "source_text",
        "source_pdf",
        "source_tex",
        "journal_source_transcript",
        "source_stage",
        "source_version",
        "semantic_basis",
        "semantic_match",
        "source_expression",
        "source_support_scope",
        "text_layer_status",
        "title",
        "validator",
        "statement",
        "printed_source_locations",
        "canonical_source_path",
        "source_label",
        "grouping_reason",
    }
)

_LOCAL_ABSOLUTE_PATH_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])/(?:tmp|home)(?=$|/)(?:/[^\s,;:()\[\]{}]+)*"
)
_AUDIT_SOURCE_PATH_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:[A-Za-z0-9_.-]+/)*\.audit_source(?:/[^\s,;:()\[\]{}]+)*"
)
_PRIVATE_EXTRACTION_RE = re.compile(
    r"\bprivate\s+(?:text|source)(?:[-\s]+)?extraction\b", re.IGNORECASE
)
_PRIVATE_SOURCE_TEXT_RE = re.compile(r"\bprivate\s+source\.txt\b", re.IGNORECASE)
_REMEDIATION_HANDOFF_RE = re.compile(r"\bremediation\s+handoff\b", re.IGNORECASE)
_UNRESOLVED_HANDOFF_RE = re.compile(
    r"\bunresolved\s+mathematical\s+handoff\b", re.IGNORECASE
)
_SOURCE_FIDELITY_REMEDIATION_RE = re.compile(
    r"\bsource[-\s]+fidelity\s+remediation\b", re.IGNORECASE
)
_SOURCE_FIRST_REMEDIATION_RE = re.compile(
    r"\bsource[-\s]+first(?:\s+[A-Za-z0-9_-]+){0,4}\s+remediation\b",
    re.IGNORECASE,
)
_CODEX_REMEDIATION_RE = re.compile(
    r"\bcodex\b[^\n]{0,160}?\bremediation\b", re.IGNORECASE
)
_OLDER_TRACKED_EXTRACTION_SENTENCE_RE = re.compile(
    r"\b(?:the\s+)?older\s+tracked(?:\s+text)?\s+extraction\b[^.]*\.",
    re.IGNORECASE,
)
_LOCAL_PDF_CACHE_RE = re.compile(r"\blocal\s+PDF\s+cache\b", re.IGNORECASE)
_PAPER_NOTES_RE = re.compile(r"\bPAPER_NOTES\.md\b", re.IGNORECASE)
_SOURCE_FILENAME_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:[A-Za-z0-9_.-]+/)*"
    r"[A-Za-z0-9_.-]+\.(?:txt|tex|pdf|html|tar(?:\.gz)?)(?::\d+(?:-\d+)?)?"
    r"(?![A-Za-z0-9_-])",
    re.IGNORECASE,
)
# Text artifacts contain ordinary repository-relative ``.tex``, ``.pdf``, and
# ``.html`` links (for example a DependencyDAG input or ``site/index.html``).
# Those are public navigation, not source-cache provenance.  Only a
# source-named filename or a conventional source-cache directory is neutralized
# when it occurs in free prose.  JSON source-locator fields deliberately retain
# the broader ``_SOURCE_FILENAME_RE`` check above because their schema supplies
# the missing semantic context.
_TEXT_SOURCE_TRANSCRIPT_LOCATOR_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:"
    r"(?:sources?|source_tex|source_archive(?:_surface)?|citation_source)/"
    r"[A-Za-z0-9_./-]+\.(?:txt|tex|pdf|html|tar(?:\.gz)?)"
    r"|source(?:[-_][A-Za-z0-9_.-]+)?\.(?:txt|tex|pdf|html|tar(?:\.gz)?)"
    r")(?:\:\d+(?:-\d+)?)?(?![A-Za-z0-9_-])",
    re.IGNORECASE,
)
# A transcript filename is a local lookup surface unless it occurs inside a
# verified raw source quote.  Keep this intentionally broader than the legacy
# ``source.txt`` spelling: paper-specific extracted filenames are just as
# unavailable in a public checkout.
_PRIVATE_TRANSCRIPT_LOCATOR_RE = _SOURCE_FILENAME_RE
_LOCAL_SOURCE_ARTIFACT_RE = re.compile(
    r"(?<![A-Za-z0-9_.-])(?:"
    r"(?:[A-Za-z0-9_.-]+/)*"
    r"|\.scratch/\$PAPER/)"
    r"source\.(?:pdf|tar(?:\.gz)?)(?![A-Za-z0-9_-])",
    re.IGNORECASE,
)


def _publication_locator_for_transcript(match: re.Match[str]) -> str:
    """Replace an unavailable filename while retaining its displayed span."""

    span = re.search(r":\d+(?:-\d+)?$", match.group(0))
    return PUBLICATION_LOCATOR + (span.group(0) if span else "")
_REMEDIATION_CLOSED_RE = re.compile(r"\bremediation_closed\b", re.IGNORECASE)
_PUBLIC_HTTP_URL_RE = re.compile(r"https?://[^\s<>()\[\]{}]+", re.IGNORECASE)
_PRIVATE_URL_FRAGMENT_RE = re.compile(
    r"(?:econcslib-private|private-artifacts|\.audit_source|\.review_traces)",
    re.IGNORECASE,
)


def _decoded_url_for_policy(url: str) -> str:
    """Decode URL escapes before checking for an internal publication route."""

    decoded = url
    # A bounded loop catches ordinary and double-encoded route fragments
    # without treating an arbitrary encoded document as executable input.
    for _ in range(3):
        next_decoded = html_unescape(unquote(decoded))
        if next_decoded == decoded:
            break
        decoded = next_decoded
    return decoded


def _decoded_text_for_policy(value: str) -> str:
    """Decode inert URL/text encodings before applying boundary policy."""

    decoded = value
    for _ in range(3):
        next_decoded = html_unescape(unquote(decoded))
        if next_decoded == decoded:
            break
        decoded = next_decoded
    return decoded
_PRIVATE_ARTIFACT_ROUTE_RE = re.compile(r"/(?:private-artifacts)(?:/|$)", re.IGNORECASE)
_PRIVATE_WORKFLOW_REFERENCE_RE = re.compile(
    r"\b(?:trusted\s+)?private\s+(?:origin(?:/main)?|source(?:\s+(?:review|commit|artifact|text))?|"
    r"checkout|workspace|workflow|repository(?:\s+context)?|collaboration\s+space|"
    r"(?:proof\s+body|intake|closeout|handoff)|Git\s+objects|by-default|by\s+sorry|"
    r"paper(?:\s+(?:folder|thread|development))?|"
    r"(?:plans?|approvals?|planning|history|incubator|target-setting\s+phase))\b",
    re.IGNORECASE,
)
_REVIEW_TRACE_RE = re.compile(r"(?:^|[\s`])\.review_traces(?:/[^\s`]+)?", re.IGNORECASE)
_SCRATCH_WORKFLOW_RE = re.compile(r"(?:^|[\s`])\.scratch(?:/[^\s`]+)?", re.IGNORECASE)
_SOURCE_CACHE_RE = re.compile(r"\bsource\s+cache\b", re.IGNORECASE)

_SENSITIVE_VALUE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("a local /tmp or /home path", _LOCAL_ABSOLUTE_PATH_RE),
    ("a .audit_source path", _AUDIT_SOURCE_PATH_RE),
    ("a non-public source artifact locator", _LOCAL_SOURCE_ARTIFACT_RE),
    ("private source-extraction wording", _PRIVATE_EXTRACTION_RE),
    ("private source-text wording", _PRIVATE_SOURCE_TEXT_RE),
    ("remediation-handoff wording", _REMEDIATION_HANDOFF_RE),
    ("unresolved-handoff wording", _UNRESOLVED_HANDOFF_RE),
    ("source-fidelity-remediation wording", _SOURCE_FIDELITY_REMEDIATION_RE),
    ("source-first-remediation wording", _SOURCE_FIRST_REMEDIATION_RE),
    ("Codex remediation workflow wording", _CODEX_REMEDIATION_RE),
    ("a local PDF cache reference", _LOCAL_PDF_CACHE_RE),
    ("a local source-cache reference", _SOURCE_CACHE_RE),
    ("a PAPER_NOTES.md workflow reference", _PAPER_NOTES_RE),
    ("a remediation-closed workflow value", _REMEDIATION_CLOSED_RE),
    ("a private artifact route", _PRIVATE_ARTIFACT_ROUTE_RE),
    ("a private workflow reference", _PRIVATE_WORKFLOW_REFERENCE_RE),
    ("a local review-trace path", _REVIEW_TRACE_RE),
    ("a local scratch-workflow path", _SCRATCH_WORKFLOW_RE),
)

_SOURCE_LOCATOR_JSON_KEYS = frozenset(
    {
        "affected_source_locators",
        "archival_source_locator",
        "artifact_path",
        "companion_html_path",
        "extracted_tex_path",
        "generated_from",
        "non_target_source_inventory",
        "printed_source_locations",
        "semantic_basis",
        "semantic_match",
        "source_anchor",
        "source_anchor_evidence",
        "source_anchors",
        "source_evidence",
        "source_expression",
        "source_location",
        "source_locator",
        "source_pdf",
        "source_restatement_evidence",
        "source_stage",
        "source_support_scope",
        "source_term_use_anchor",
        "source_text",
        "statement",
    }
)

_WORKFLOW_KEY_RE = re.compile(r"(?:^|_)(?:handoff|remediation)(?:_|$)", re.IGNORECASE)
# Lean comments can carry the same private transcript locators as generated
# review prose.  A public projection only rewrites those locators; it leaves
# Lean syntax and mathematical content byte-for-byte unchanged otherwise.
_TEXT_SUFFIXES = frozenset({".html", ".lean", ".md", ".tex", ".txt"})
def _relative_path(value: str) -> PurePosixPath:
    if not isinstance(value, str) or not value.strip():
        raise ProjectionError("projection path must be a nonempty repository-relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or str(path) in {"", "."}:
        raise ProjectionError(f"projection path is unsafe: {value!r}")
    return path


def _json_pointer(parts: Sequence[str | int]) -> str:
    if not parts:
        return ""
    escaped = (str(part).replace("~", "~0").replace("/", "~1") for part in parts)
    return "/" + "/".join(escaped)


def _is_excerpt_field(field: str | None) -> bool:
    return field in _EXCERPT_FIELDS if field is not None else False


def _approved_raw_path(path: PurePosixPath) -> bool:
    """Return whether an explicitly approved public surface remains exact."""

    parts = path.parts
    if len(parts) >= 4 and parts[0] == "papers" and parts[2] == "source" and path.suffix == ".tex":
        return True
    return str(path) in PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS


def _mask_public_http_urls(value: str) -> str:
    """Hide public URLs while evaluating local-path hygiene patterns.

    A legitimate official URL can contain a route such as ``/source/main.tex``
    or a hostname beginning with ``home``.  Those are public web locations,
    not local audit transcript paths.
    """

    return _PUBLIC_HTTP_URL_RE.sub("PUBLIC_HTTP_URL", value)


def _unsafe_public_url_issue(value: str) -> str | None:
    """Reject URLs that themselves disclose a non-public repository surface.

    URL masking is necessary for legitimate public URLs such as
    ``https://homes.cs.washington.edu/...`` or an official arXiv ``/source/``
    route.  It must happen *after* this narrow check, however: otherwise a URL
    naming the development repository or an internal artifact route would be
    hidden from every hygiene pattern.
    """

    for match in _PUBLIC_HTTP_URL_RE.finditer(value):
        url = match.group(0)
        if _PRIVATE_URL_FRAGMENT_RE.search(_decoded_url_for_policy(url)):
            return "a private repository or artifact URL"
    return None


def source_excerpt_field_is_bound(container: Mapping[str, Any], field: str) -> bool:
    """Whether one scalar raw-source field has a verifiable record shape.

    This is intentionally structural rather than an audit substitute.  It
    prevents a generic JSON field named ``quoted_text`` from suppressing the
    public-boundary scan, while retaining user-approved official arXiv/PDF
    excerpts recorded with their hash and source location.  The strict private
    source-byte validators continue to establish whether the quotation is
    actually sliced from the pinned source artifact.
    """

    quote = container.get(field)
    digest = container.get(f"{field}_sha256")
    if not isinstance(quote, str) or not isinstance(digest, str):
        return False
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        return False
    if hashlib.sha256(quote.encode("utf-8")).hexdigest() != digest:
        return False

    has_line_span = all(
        isinstance(container.get(key), int)
        for key in ("line_start", "line_end")
    )
    has_byte_span = all(
        isinstance(container.get(key), int)
        for key in ("byte_start", "byte_end")
    )
    if has_line_span and container["line_start"] > container["line_end"]:
        return False
    if has_byte_span and container["byte_start"] > container["byte_end"]:
        return False
    has_locator = any(
        isinstance(container.get(key), str) and container[key].strip()
        for key in ("path", "publication_locator", "source_location", "source_locator")
    )
    if field == "quoted_text":
        return has_locator and (has_line_span or has_byte_span)
    if field in {"source_excerpt", "source_quote"}:
        return has_locator
    return False


def source_excerpt_safety_issue(value: str) -> str | None:
    """Reject development-local disclosure even inside a verbatim source quote.

    A valid digest plus a source-anchor-shaped JSON object makes a quote a
    *candidate* source record, not permission to publish arbitrary local
    provenance.  Ordinary mathematical text and source-transcript terminology
    remain verbatim, but a workstation path, an internal repository URL, or an
    audit cache name is never an acceptable public excerpt.
    """

    policy_value = _decoded_text_for_policy(value)
    url_issue = _unsafe_public_url_issue(policy_value)
    if url_issue is not None:
        return url_issue
    for label, pattern in (
        ("a local /tmp or /home path", _LOCAL_ABSOLUTE_PATH_RE),
        ("a .audit_source path", _AUDIT_SOURCE_PATH_RE),
        ("a private artifact route", _PRIVATE_ARTIFACT_ROUTE_RE),
        ("a local review-trace path", _REVIEW_TRACE_RE),
        ("a local scratch-workflow path", _SCRATCH_WORKFLOW_RE),
    ):
        if pattern.search(_mask_public_http_urls(policy_value)):
            return label
    return None


def _contains_local_path(value: object) -> bool:
    return isinstance(value, str) and bool(
        _LOCAL_ABSOLUTE_PATH_RE.search(value) or _AUDIT_SOURCE_PATH_RE.search(value)
    )


def _project_public_workflow_text(value: str) -> str:
    """Replace development-only operational wording in public-facing prose.

    The private repository retains the detailed operations manual.  Public
    readers need the mathematical/audit protocol and a concise release policy,
    not internal repository roles, cache paths, or handoff locations.  Keep
    this list intentionally literal so new private workflow terminology fails
    the hygiene assertion below instead of being silently rewritten.
    """

    replacements = (
        ("private-to-public preparation", "public-release preparation"),
        ("private/public export", "release export"),
        ("private/public", "development/release"),
        ("EconCSLib-private", "the development repository"),
        ("private source review", "source review at the authoritative record"),
        ("trusted private origin/main ref", "recorded source-provenance ref"),
        ("trusted private origin/main", "recorded source-provenance ref"),
        ("private source surfaces", "source-provenance surfaces"),
        ("private source surface", "source-provenance surface"),
        ("private checkout", "authoritative audit checkout"),
        ("private workflow", "development workflow"),
        ("private repository context", "non-public repository context"),
        ("private repository", "development repository"),
        ("private collaboration space", "non-public collaboration space"),
        ("private proof body", "temporary proof body"),
        ("private by sorry body", "temporary by sorry body"),
        ("private intake", "pre-closeout intake"),
        ("private closeout", "non-public closeout"),
        ("private handoff", "internal handoff"),
        ("private Git objects", "source-repository Git objects"),
        ("private-by-default", "non-public-by-default"),
        ("private draft", "unpublished draft"),
        ("private workspace", "working workspace"),
        ("Private workspace", "Working workspace"),
        ("private paper folders", "development paper folders"),
        ("Private paper folders", "Development paper folders"),
        ("private paper development", "focused paper development"),
        ("private paper-development branches", "focused paper-development branches"),
        ("private paper intake", "paper intake"),
        ("private paper thread", "focused paper thread"),
        ("private target-setting phase", "pre-closeout target-setting phase"),
        ("private plans or handoffs", "internal planning records"),
        ("private planning/handoff", "internal planning records"),
        ("private planning", "internal planning"),
        ("private approvals", "approval records"),
        ("private development history", "unreviewed development history"),
        ("private development", "development"),
        ("private status", "development status"),
        ("private branch", "development branch"),
        ("private source commits", "source-provenance commits"),
        ("private source commit", "source-provenance commit"),
        ("private source artifacts", "source artifacts not included in the release"),
        ("private source artifact", "source artifact not included in the release"),
        ("private source PDFs/text caches", "source PDFs/text caches not included in the release"),
        ("private incubator", "development workspace"),
        ("private sibling imports", "sibling imports"),
        ("Keep those private by default.", "Keep those out of public release artifacts by default."),
        ("remain private until explicit human approval", "remain non-public until explicit human approval"),
    )
    result = value
    for before, after in replacements:
        result = result.replace(before, after)

    # These names designate local, reviewer-owned implementation storage.  A
    # public guide may describe the role without exposing an untracked path.
    result = re.sub(
        r"`?papers/<(?:PaperRoot|PaperName)>/\.review_traces/[^`\s]+`?",
        "reviewer-owned review record",
        result,
    )
    result = result.replace(".review_traces", "reviewer-owned review storage")
    result = re.sub(r"`?\.scratch(?:/[^`\s]+)?`?", "an untracked working area", result)
    return result


def _neutralize_text(value: str) -> str:
    """Rewrite only the known workflow phrases into paper-facing language."""

    urls: list[str] = []

    def hide_url(match: re.Match[str]) -> str:
        urls.append(match.group(0))
        return f"__PUBLIC_HTTP_URL_{len(urls) - 1}__"

    result = _PUBLIC_HTTP_URL_RE.sub(hide_url, value)
    result = _LOCAL_ABSOLUTE_PATH_RE.sub("publication text", result)
    result = _AUDIT_SOURCE_PATH_RE.sub("publication text", result)
    result = _PRIVATE_EXTRACTION_RE.sub("publication source record", result)
    result = _PRIVATE_SOURCE_TEXT_RE.sub("checked source text", result)
    result = _REMEDIATION_HANDOFF_RE.sub("source-review record", result)
    result = _UNRESOLVED_HANDOFF_RE.sub("remaining mathematical issue", result)
    result = _SOURCE_FIDELITY_REMEDIATION_RE.sub("source-fidelity review", result)
    result = _SOURCE_FIRST_REMEDIATION_RE.sub("source verification", result)
    result = _CODEX_REMEDIATION_RE.sub("source-verification record", result)
    result = _REMEDIATION_CLOSED_RE.sub("review_complete", result)
    result = _LOCAL_PDF_CACHE_RE.sub("publication record", result)
    result = _PAPER_NOTES_RE.sub("source-review record", result)
    result = _LOCAL_SOURCE_ARTIFACT_RE.sub(PUBLICATION_LOCATOR, result)
    result = _TEXT_SOURCE_TRANSCRIPT_LOCATOR_RE.sub(
        _publication_locator_for_transcript, result
    )
    result = _OLDER_TRACKED_EXTRACTION_SENTENCE_RE.sub(
        "The cited publication is the source reference for these anchors.", result
    )
    for index, url in enumerate(urls):
        result = result.replace(f"__PUBLIC_HTTP_URL_{index}__", url)
    return _project_public_workflow_text(result)


def _project_source_evidence(value: str) -> str:
    """Keep the mathematical inventory clause while discarding local source workflow."""

    if not any(pattern.search(value) for _, pattern in _SENSITIVE_VALUE_PATTERNS):
        return value
    marker = "Source inventory item:"
    if marker in value:
        inventory = value.split(marker, 1)[1].strip()
        return f"Publication source evidence. {marker} {inventory}"
    marker = "Source anchor:"
    if marker in value:
        anchor = _neutralize_text(value.split(marker, 1)[1].strip())
        return f"Publication source evidence. {marker} {anchor}"
    return _SOURCE_FILENAME_RE.sub(
        _publication_locator_for_transcript, _neutralize_text(value)
    )


def _project_controlled_text(field: str, value: str) -> str:
    if field == "source_evidence":
        return _project_source_evidence(value)
    if field == "source_location_validator":
        return "source-location verification"
    if field == "source_kind_validator":
        return "source-kind verification"
    if field == "source_curator":
        return "source curation record"
    if field == "generated_from":
        return "source-verification protocol"
    if field == "remediation_note":
        return "Source locations and excerpts are verified against the cited publication."
    if field in {
        "source_text",
        "source_pdf",
        "source_tex",
        "journal_source_transcript",
    } and _SOURCE_FILENAME_RE.fullmatch(
        value.strip()
    ):
        # Status sidecars historically stored a local transcript filename in
        # this field.  The citation and digest remain elsewhere; a local file
        # name is not meaningful to a public reader.
        return "cited publication record"
    result = _neutralize_text(value)
    if field == "source_version" and any(
        token in value.lower() for token in ("audit", "extraction", "tracked")
    ):
        # The source URL and digest are retained separately.  Internal
        # extraction history is not public provenance and should not be a
        # reader-facing part of the review record.
        return "cited publication source record"
    if field in {"source_location", "source_locator", "affected_source_locators"}:
        result = _SOURCE_FILENAME_RE.sub(_publication_locator_for_transcript, result)
    if field == "validator" and "codex" in result.lower() and "remediation" in value.lower():
        return "source-verification record"
    return result


def _project_anchor(value: object, *, pointer: Sequence[str | int]) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise ProjectionError(f"source anchor at {_json_pointer(pointer)} must be an object")
    result: dict[str, Any] = {}
    had_path = False
    for key, child in value.items():
        if not isinstance(key, str):
            raise ProjectionError(f"source anchor at {_json_pointer(pointer)} has a non-string key")
        if key == "path":
            if not isinstance(child, str) or not child.strip():
                raise ProjectionError(f"source anchor path at {_json_pointer(pointer)} must be a nonempty string")
            had_path = True
            continue
        if key in _EXCERPT_FIELDS and isinstance(child, str):
            if not source_excerpt_field_is_bound(value, key):
                raise ProjectionError(
                    f"source excerpt at {_json_pointer((*pointer, key))} is not a bound source record"
                )
            result[key] = child
        else:
            result[key] = _project_value(child, field=key, pointer=(*pointer, key))
    if had_path:
        result["publication_locator"] = PUBLICATION_LOCATOR
    return result


def _project_source_text_companion(
    value: object, *, pointer: Sequence[str | int]
) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise ProjectionError(
            f"source_text_companion at {_json_pointer(pointer)} must be an object"
        )

    def visit(current: object, current_pointer: Sequence[str | int]) -> object:
        if isinstance(current, Mapping):
            result: dict[str, Any] = {}
            for key, child in current.items():
                if not isinstance(key, str):
                    raise ProjectionError(
                        f"source_text_companion at {_json_pointer(current_pointer)} has a non-string key"
                    )
                if key == "path":
                    if not isinstance(child, str) or not child.strip():
                        raise ProjectionError(
                            f"source_text_companion path at {_json_pointer((*current_pointer, key))} "
                            "must be a nonempty string"
                        )
                    continue
                result[key] = visit(child, (*current_pointer, key))
            return result
        if isinstance(current, list):
            return [visit(child, (*current_pointer, index)) for index, child in enumerate(current)]
        if isinstance(current, str):
            return _project_controlled_text("method", current)
        return current

    projected = visit(value, pointer)
    assert isinstance(projected, dict)
    return projected


def _project_source_locator_inventory(
    value: object, *, pointer: Sequence[str | int]
) -> Any:
    """Project a descriptive source-inventory index without local filenames."""

    if isinstance(value, Mapping):
        result: dict[str, Any] = {}
        for key, child in value.items():
            if not isinstance(key, str):
                raise ProjectionError(
                    f"source inventory at {_json_pointer(pointer)} has a non-string key"
                )
            result[key] = _project_source_locator_inventory(
                child, pointer=(*pointer, key)
            )
        return result
    if isinstance(value, list):
        return [
            _project_source_locator_inventory(child, pointer=(*pointer, index))
            for index, child in enumerate(value)
        ]
    if isinstance(value, str):
        return _project_controlled_text("source_location", value)
    return _project_value(value, field="source_location", pointer=pointer)


def _project_mapping(value: Mapping[str, Any], *, pointer: Sequence[str | int]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, child in value.items():
        if not isinstance(key, str):
            raise ProjectionError(f"object at {_json_pointer(pointer)} has a non-string key")
        if key in _DROP_FIELDS:
            continue
        if _WORKFLOW_KEY_RE.search(key) and key not in _KEY_RENAMES:
            raise ProjectionError(
                f"unrecognized private-workflow key at {_json_pointer((*pointer, key))}"
            )
        public_key = _KEY_RENAMES.get(key, key)
        if public_key in result:
            raise ProjectionError(
                f"projection would collide at {_json_pointer((*pointer, public_key))}"
            )
        child_pointer = (*pointer, key)
        if key == "approval_reference":
            if not isinstance(child, str) or not child.strip():
                raise ProjectionError(f"malformed approval reference at {_json_pointer(child_pointer)}")
            projected = PUBLIC_WITHHELD_APPROVAL_REFERENCE
        elif key == "approval" and pointer and pointer[-1] == "deep_support_repair":
            if not isinstance(child, Mapping):
                raise ProjectionError(f"malformed repair approval at {_json_pointer(child_pointer)}")
            projected = {
                "publication_record": PUBLIC_WITHHELD_APPROVAL_REFERENCE,
                "private_record_sha256": hashlib.sha256(
                    json.dumps(child, sort_keys=True, separators=(",", ":")).encode("utf-8")
                ).hexdigest(),
            }
        elif key in _EXCERPT_FIELDS and isinstance(child, str):
            if not source_excerpt_field_is_bound(value, key):
                raise ProjectionError(
                    f"source excerpt at {_json_pointer(child_pointer)} is not a bound source record"
                )
            projected = child
        elif key in _ANCHOR_FIELDS:
            # Most audit schemas use an object with a byte-pinned path, but a
            # few older human-status records retain a compact string locator.
            # Both are publicable as a paper locator; only the object form has
            # a private path field to remove.
            if isinstance(child, Mapping):
                projected = _project_anchor(child, pointer=child_pointer)
            elif isinstance(child, str):
                projected = _project_controlled_text("source_location", child)
            else:
                raise ProjectionError(
                    f"source anchor at {_json_pointer(child_pointer)} must be an object or string"
                )
        elif key in {"source_anchor_evidence", "semantic_source_anchor_evidence"}:
            if not isinstance(child, list):
                raise ProjectionError(
                    f"source anchor evidence at {_json_pointer(child_pointer)} must be a list"
                )
            projected = [
                _project_anchor(anchor, pointer=(*child_pointer, index))
                for index, anchor in enumerate(child)
            ]
        elif key == "source_text_companion":
            projected = _project_source_text_companion(child, pointer=child_pointer)
        elif key == "non_target_source_inventory":
            projected = _project_source_locator_inventory(child, pointer=child_pointer)
        elif key == "paper_dir" and _contains_local_path(child):
            # A repository-relative paper id is harmless, but an absolute
            # working-directory receipt has no public provenance value.
            continue
        elif key in {"source_archive", "source_archive_path", "base_archive_path"} and isinstance(
            child, str
        ):
            # A retained archive checksum remains useful, but the private
            # checkout filename that once held it is not a public navigation
            # target.  This small schema family is deliberately explicit so
            # unknown free-form JSON remains fail-closed below.
            projected = _neutralize_text(child)
        elif (
            key == "path"
            and isinstance(child, str)
            and any(
                component
                in {
                    "base_archive",
                    "source_archive",
                    "source_artifact_identity",
                    "source_artifact_identities",
                    "source_artifact",
                    "source_pdf_artifact",
                    "cited_source_artifacts",
                }
                for component in pointer
                if isinstance(component, str)
            )
        ):
            # Some legacy receipts place the archive locator in a small
            # ``{path, sha256}`` object rather than in a named ``*_path``
            # field.  The hash remains; this replaces only the unavailable
            # private archive filename.
            projected = PUBLICATION_LOCATOR
        elif (
            (key == "path" or key.endswith("_path"))
            and isinstance(child, str)
            and _contains_local_path(child)
        ):
            # Nested receipt schemas retain a handful of source-identity
            # records outside the canonical anchor object.  Their byte hash,
            # line spans, and source URL remain public; the machine-local
            # lookup path becomes a neutral publication locator.
            projected = PUBLICATION_LOCATOR
        else:
            projected = _project_value(child, field=key, pointer=child_pointer)
        result[public_key] = projected
    return result


def _project_value(
    value: object, *, field: str | None, pointer: Sequence[str | int]
) -> Any:
    if isinstance(value, Mapping):
        return _project_mapping(value, pointer=pointer)
    if isinstance(value, list):
        return [
            _project_value(item, field=field, pointer=(*pointer, index))
            for index, item in enumerate(value)
        ]
    if isinstance(value, str):
        if _is_excerpt_field(field):
            # Scalar source excerpts are permitted only through the enclosing
            # mapping branch above, where their hash and locator shape are
            # checked.  A bare field name is not enough to bypass hygiene.
            raise ProjectionError(
                f"source excerpt at {_json_pointer(pointer)} must be a bound source record"
            )
        if (
            field in _CONTROLLED_TEXT_FIELDS
            and _PRIVATE_TRANSCRIPT_LOCATOR_RE.search(value)
        ):
            # Older free-form fields sometimes contain transcript filenames.
            # Keep their mathematical explanation while replacing the local
            # navigation detail with a publication-facing locator.
            if field in {"source_tex", "journal_source_transcript"}:
                return _project_controlled_text(field, value)
            return _project_controlled_text("source_location", value)
        if field == "kind" and _REMEDIATION_CLOSED_RE.fullmatch(value):
            return "review_complete"
        if field in _CONTROLLED_TEXT_FIELDS or field == "remediation_note":
            return _project_controlled_text(field, value)
        return value
    if value is None or isinstance(value, (bool, int, float)):
        return value
    raise ProjectionError(f"unsupported JSON value at {_json_pointer(pointer)}")


def _sensitive_value_issue(value: str) -> str | None:
    policy_value = _decoded_text_for_policy(value)
    url_issue = _unsafe_public_url_issue(policy_value)
    if url_issue is not None:
        return url_issue
    scan_value = _mask_public_http_urls(policy_value)
    for label, pattern in _SENSITIVE_VALUE_PATTERNS:
        if pattern.search(scan_value):
            return label
    return None


def _json_route_has_source_locator(pointer: Sequence[str | int]) -> bool:
    """Whether a JSON leaf has an explicitly source-locator-shaped route."""

    return any(
        isinstance(component, str) and component in _SOURCE_LOCATOR_JSON_KEYS
        for component in pointer
    )


def _text_safety_issue(value: str) -> str | None:
    """Check reader-facing prose without treating ordinary file links as sources.

    Source-locator JSON fields have a schema role, so a generic ``.txt`` or
    ``.tex`` filename there is suspicious.  Markdown/TeX/HTML prose instead
    routinely links to public repository artifacts with those suffixes.  The
    text projector has already rewritten source-named cache locators; retain
    every other normal documentation link.
    """

    policy_value = _decoded_text_for_policy(value)
    url_issue = _unsafe_public_url_issue(policy_value)
    if url_issue is not None:
        return url_issue
    scan_value = _mask_public_http_urls(policy_value)
    for label, pattern in _SENSITIVE_VALUE_PATTERNS:
        if label == "a non-public source transcript locator":
            continue
        if pattern.search(scan_value):
            return label
    return None


def _assert_public_safe_json(
    value: object,
    *,
    relative_path: str,
    pointer: Sequence[str | int] = (),
    source_excerpt: bool = False,
) -> None:
    if isinstance(value, Mapping):
        bound_excerpt_fields = {
            key
            for key in _EXCERPT_FIELDS
            if source_excerpt_field_is_bound(value, key)
            and public_source_excerpt_route_is_permitted(
                relative_path, (*pointer, key)
            )
        }
        for key, child in value.items():
            if not isinstance(key, str):
                raise ProjectionError(f"object at {_json_pointer(pointer)} has a non-string key")
            if _WORKFLOW_KEY_RE.search(key):
                raise ProjectionError(
                    f"unsafe workflow key in public projection: {relative_path}{_json_pointer((*pointer, key))}"
                )
            _assert_public_safe_json(
                child,
                relative_path=relative_path,
                pointer=(*pointer, key),
                # Source excerpts are scalar raw evidence.  Do not let an
                # arbitrary nested object inherit a blanket exemption merely
                # because it sits below a field named `quoted_text`.
                source_excerpt=(
                    source_excerpt
                    or (key in bound_excerpt_fields and isinstance(child, str))
                ),
            )
        return
    if isinstance(value, list):
        for index, child in enumerate(value):
            _assert_public_safe_json(
                child,
                relative_path=relative_path,
                pointer=(*pointer, index),
                source_excerpt=source_excerpt,
            )
        return
    if isinstance(value, str):
        issue = (
            source_excerpt_safety_issue(value)
            if source_excerpt
            else _sensitive_value_issue(value)
        )
        if (
            issue is None
            and not source_excerpt
            and _json_route_has_source_locator(pointer)
            and _PRIVATE_TRANSCRIPT_LOCATOR_RE.search(value)
        ):
            issue = "a non-public source transcript locator"
        if issue is not None:
            raise ProjectionError(
                f"unsafe {issue} in public projection: {relative_path}{_json_pointer(pointer)}"
            )


def _is_paper_statement_map_path(path: PurePosixPath) -> bool:
    parts = path.parts
    return (
        len(parts) == 4
        and parts[0] == "papers"
        and parts[2] == "audit"
        and parts[3] == "paper_statement_map.json"
    )


def _canonical_paper_relative_path(value: object) -> bool:
    """Whether one private approval locator has an unambiguous relative form."""

    if not isinstance(value, str) or not value or value != value.strip() or "\\" in value:
        return False
    components = value.split("/")
    if any(component in {"", ".", ".."} for component in components):
        return False
    path = PurePosixPath(value)
    return not path.is_absolute() and path.as_posix() == value


def _normalized_text_sha256(value: object) -> str:
    normalized = re.sub(r"\s+", " ", str(value or "").strip())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def _prepare_public_corrected_target_projection(
    payload: object, *, relative_path: str
) -> tuple[object, dict[str, tuple[str, str, str]]]:
    """Remove private approval records only after validating their identities.

    The public map retains the exact mathematical statement, its stable review
    digest, and the opaque digest of the full private correction record.  The
    exact private blob and deterministic transformation are authenticated by
    the release guard's ``private_projection`` provenance check.
    """

    if not isinstance(payload, Mapping):
        return payload, {}
    if PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD in payload:
        raise ProjectionError(
            f"{relative_path} private source map already declares "
            f"{PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD}"
        )
    items = payload.get("items")
    if not isinstance(items, Mapping):
        return payload, {}

    projected_items: dict[str, Any] = dict(items)
    retained: dict[str, tuple[str, str, str]] = {}
    for item_id, item in items.items():
        if not isinstance(item_id, str):
            raise ProjectionError(f"{relative_path} source-map items has a non-string key")
        if not isinstance(item, Mapping) or "corrected_target" not in item:
            continue
        pointer = ("items", item_id, "corrected_target")
        target = item.get("corrected_target")
        if not isinstance(target, Mapping):
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} must be an object"
            )
        if target.get("schema") != 1:
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} must use schema 1"
            )
        if target.get("archival_equivalence_claimed") is not False:
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} must declare "
                "archival_equivalence_claimed=false"
            )
        statement = target.get("statement")
        if not isinstance(statement, str) or not statement.strip():
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} has no statement"
            )

        raw_record_digest = target.get(CORRECTED_TARGET_RECORD_SHA256_FIELD)
        raw_review_digest = target.get(CORRECTED_TARGET_REVIEW_SHA256_FIELD)
        record_digest = str(raw_record_digest or "").strip().lower()
        review_digest = str(raw_review_digest or "").strip().lower()
        if (
            raw_record_digest != record_digest
            or not re.fullmatch(r"[0-9a-f]{64}", record_digest)
            or record_digest != corrected_target_record_digest(target)
        ):
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} has a stale or malformed "
                f"{CORRECTED_TARGET_RECORD_SHA256_FIELD}"
            )
        if (
            raw_review_digest != review_digest
            or not re.fullmatch(r"[0-9a-f]{64}", review_digest)
            or review_digest != corrected_target_review_digest(target)
        ):
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} has a stale or malformed "
                f"{CORRECTED_TARGET_REVIEW_SHA256_FIELD}"
            )

        approval = target.get("approval")
        if (
            not isinstance(approval, Mapping)
            or not isinstance(approval.get("artifact_excerpt"), str)
            or corrected_target_approval_excerpt_material(approval) is None
        ):
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} has malformed private "
                "approval excerpt authority"
            )
        if not _canonical_paper_relative_path(approval.get("artifact_path")):
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} has a noncanonical "
                "private approval artifact_path"
            )
        original_path_error = corrected_target_original_artifact_path_error(approval)
        if original_path_error:
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} has invalid "
                f"{CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD}: {original_path_error}"
            )
        if str(
            approval.get("target_statement_sha256") or ""
        ).strip().lower() != _normalized_text_sha256(statement):
            raise ProjectionError(
                f"corrected target at {_json_pointer(pointer)} has a stale or malformed "
                "approval target_statement_sha256"
            )

        public_target = dict(target)
        public_target.pop("approval")
        public_item = dict(item)
        public_item["corrected_target"] = public_target
        projected_items[item_id] = public_item
        retained[item_id] = (statement, record_digest, review_digest)

    if not retained:
        return payload, {}
    projected_payload = dict(payload)
    projected_payload["items"] = projected_items
    projected_payload[PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD] = {
        "schema": PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
        "approval_material_included": False,
    }
    return projected_payload, retained


def _assert_corrected_target_projection_preserved(
    projected: object,
    retained: Mapping[str, tuple[str, str, str]],
    *,
    relative_path: str,
) -> None:
    """Require the generic projection to leave mathematical identities exact."""

    if not retained:
        return
    if not isinstance(projected, Mapping):
        raise ProjectionError(f"{relative_path} projected source map must be an object")
    marker = projected.get(PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD)
    if marker != {
        "schema": PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
        "approval_material_included": False,
    }:
        raise ProjectionError(f"{relative_path} corrected-target projection marker changed")
    items = projected.get("items")
    if not isinstance(items, Mapping):
        raise ProjectionError(f"{relative_path} projected source-map items must be an object")
    for item_id, (statement, record_digest, review_digest) in retained.items():
        item = items.get(item_id)
        target = item.get("corrected_target") if isinstance(item, Mapping) else None
        if not isinstance(target, Mapping) or "approval" in target:
            raise ProjectionError(
                f"{relative_path} projected corrected target {item_id!r} retained approval material"
            )
        if target.get("statement") != statement:
            raise ProjectionError(
                f"{relative_path} public projection would change corrected target statement "
                f"for {item_id!r}"
            )
        if target.get(CORRECTED_TARGET_RECORD_SHA256_FIELD) != record_digest:
            raise ProjectionError(
                f"{relative_path} public projection would change corrected target record "
                f"identity for {item_id!r}"
            )
        if target.get(CORRECTED_TARGET_REVIEW_SHA256_FIELD) != review_digest:
            raise ProjectionError(
                f"{relative_path} public projection would change corrected target review "
                f"identity for {item_id!r}"
            )


def public_source_excerpt_route_is_permitted(
    relative_path: str, pointer: Sequence[str | int]
) -> bool:
    """Whether a scalar excerpt occupies a canonical public source-record slot.

    A matching digest and a made-up publication locator are only self-consistent
    metadata; they are not evidence that arbitrary text came from a paper.
    The release guard separately validates these slots against the byte-pinned
    private source/manifest.  This narrower route rule prevents an unrelated
    JSON field from using ``quoted_text`` as a content-scan bypass.
    """

    path = _relative_path(relative_path)
    parts = path.parts
    # Source records occur both in the canonical map/display manifest and in
    # paper-local audit sidecars.  The latter may retain a byte-pinned
    # verbatim excerpt as evidence, so restricting the route to just the map
    # would incorrectly reject permitted official-source material.  A bare
    # ``quoted_text`` elsewhere in an audit file remains untrusted.
    is_public_source_record = (
        len(parts) == 4
        and parts[0] == "papers"
        and parts[2] == "audit"
        and path.suffix.lower() == ".json"
    )
    if not is_public_source_record:
        return False
    return any(
        isinstance(component, str)
        and (
            component in _ANCHOR_FIELDS
            or component in {
                "source_anchor_evidence",
                "semantic_source_anchor_evidence",
                "source_anchors",
            }
        )
        for component in pointer[:-1]
    )


def project_json_payload(
    payload: object,
    *,
    relative_path: str,
    include_source_display_marker: bool = False,
) -> object:
    """Project one parsed JSON payload and reject any unrecognized unsafe value."""

    path = _relative_path(relative_path)
    retained_corrected_targets: dict[str, tuple[str, str, str]] = {}
    projection_input = payload
    if _is_paper_statement_map_path(path):
        projection_input, retained_corrected_targets = (
            _prepare_public_corrected_target_projection(
                payload, relative_path=relative_path
            )
        )
    projected = _project_value(projection_input, field=None, pointer=())
    if (
        len(path.parts) == 3
        and path.parts[0] == "papers"
        and path.name == "status.json"
        and isinstance(projected, dict)
        and isinstance(projected.get("artifacts"), dict)
    ):
        # Superseded review surfaces are historical development artifacts;
        # current public evidence is selected by the accepted closure graph.
        projected["artifacts"].pop("legacy_review_surface", None)
    _assert_corrected_target_projection_preserved(
        projected,
        retained_corrected_targets,
        relative_path=relative_path,
    )
    if include_source_display_marker and _is_paper_statement_map_path(path):
        if not isinstance(projected, dict):
            raise ProjectionError(f"{relative_path} source map must be a JSON object")
        if PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD in projected:
            raise ProjectionError(
                f"{relative_path} already declares {PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD}"
            )
        projected[PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD] = {
            "schema": PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
            "manifest": PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST,
            "raw_source_bytes_included": False,
        }
    _assert_public_safe_json(projected, relative_path=relative_path)
    return projected


def _assert_public_safe_text(value: str, *, relative_path: str) -> None:
    path = _relative_path(relative_path)
    scan_value = value
    if str(path) == "site/index.html":
        scan_value = scan_value.replace(
            _PUBLIC_SITE_PRIVATE_WORKFLOW_GUIDANCE,
            _PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
        )
    if str(path) == "README.md":
        scan_value = scan_value.replace(
            PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE,
            _PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
        )
    issue = _text_safety_issue(scan_value)
    if issue is not None:
        raise ProjectionError(f"unsafe {issue} in public projection: {relative_path}")


def project_text(value: str, *, relative_path: str) -> str:
    """Project supported human-facing text without changing approved source files."""

    path = _relative_path(relative_path)
    if _approved_raw_path(path):
        return value
    if path.suffix not in _TEXT_SUFFIXES:
        raise ProjectionError(f"unsupported text artifact for public projection: {relative_path}")
    # Preserve the literal, path-bound landing-page recommendation before the
    # ordinary text projector rewrites generic private-workflow wording.
    protected_value = value
    if str(path) == "site/index.html":
        protected_value = protected_value.replace(
            _PUBLIC_SITE_PRIVATE_WORKFLOW_GUIDANCE,
            _PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
        )
    if str(path) == "README.md":
        protected_value = protected_value.replace(
            PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE,
            _PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
        )
    projected = _neutralize_text(protected_value)
    if path.name == "HUMAN_REVIEW_PACKET.tex" and path.parts[:1] == ("papers",):
        # TeX packets contain verbatim source quotations. Expand only mixed
        # leading indentation, retaining tab-stop alignment and all text.
        projected = re.sub(
            r"^[ \t]* [ \t]*\t[ \t]*",
            lambda match: match.group(0).expandtabs(8),
            projected,
            flags=re.MULTILINE,
        )
    if len(path.parts) == 3 and path.parts[0] == "papers":
        if path.name == "FINAL_VALIDATION_REPORT.md":
            # Current closeouts retain these reviews inside the accepted graph.
            # Their former standalone filenames are not public entrypoints.
            for filename in (
                "v11_raw_source_spec_screening.json",
                "paper_semantic_prerequisites.json",
                "library_semantic_review.json",
                "paper_coverage_llm.json",
                "LEAN_IMPORT_CLOSURE_RECEIPT.json",
                "source_proof_fidelity.json",
                "FOCUSED_BUILD_RECEIPT.json",
                "statement_match_llm.json",
                "assumption_match_llm.json",
                "defect_support_match_llm.json",
            ):
                projected = projected.replace(
                    f"](audit/{filename})", "](FINAL_CLOSURE_RECEIPT.md)"
                )
        elif path.name == "FINAL_CLOSURE_RECEIPT.md":
            graph_path = "audit/obligation_evidence/current_accepted_graph.json"
            declared_pointer = f'pointer = "papers/{path.parts[1]}/{graph_path}"'
            reader_link = f"[Accepted review and proof record]({graph_path})"
            if declared_pointer in projected and reader_link not in projected:
                projected = projected.rstrip() + f"\n\n{reader_link}.\n"
    if str(path) == "site/index.html":
        projected = projected.replace(
            _PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
            _PUBLIC_SITE_PRIVATE_WORKFLOW_GUIDANCE,
        )
    if str(path) == "README.md":
        projected = projected.replace(
            _PUBLIC_SITE_PRIVATE_WORKFLOW_SENTINEL,
            PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE,
        )
    _assert_public_safe_text(projected, relative_path=relative_path)
    return projected


def project_bytes(
    relative_path: str,
    private_bytes: bytes,
    *,
    include_source_display_marker: bool = False,
) -> bytes:
    """Return the canonical public projection for one exact private blob.

    Changed JSON output is serialized canonically (UTF-8, sorted keys,
    two-space indentation, final newline), so a release receipt can bind its
    exact candidate bytes.  A payload that was already public-safe is returned
    byte-for-byte: formatting churn is not a provenance transformation and
    should remain a ``private_blob`` in the release allowlist.  Supported
    textual metadata keeps its source newline convention while applying only
    the bounded phrase substitutions above.  ``include_source_display_marker``
    is deliberately opt-in: only a paper with a separately generated,
    source-byte-validated display manifest may advertise the public display
    surface.
    """

    path = _relative_path(relative_path)
    if _approved_raw_path(path):
        return private_bytes
    try:
        text = private_bytes.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ProjectionError(f"{relative_path} is not UTF-8 text") from error
    if path.suffix == ".json":
        try:
            payload = json.loads(text)
        except json.JSONDecodeError as error:
            raise ProjectionError(f"{relative_path} is not valid JSON: {error}") from error
        projected = project_json_payload(
            payload,
            relative_path=relative_path,
            include_source_display_marker=include_source_display_marker,
        )
        if projected == payload:
            return private_bytes
        return (
            json.dumps(
                projected,
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
                allow_nan=False,
            )
            + "\n"
        ).encode("utf-8")
    return project_text(text, relative_path=relative_path).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path", required=True, help="repository-relative artifact path")
    parser.add_argument("--input", type=Path, required=True, help="private input blob")
    parser.add_argument("--output", type=Path, required=True, help="public projected blob")
    args = parser.parse_args()
    try:
        args.output.write_bytes(project_bytes(args.path, args.input.read_bytes()))
    except (OSError, ProjectionError) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
