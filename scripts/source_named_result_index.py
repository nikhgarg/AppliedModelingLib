#!/usr/bin/env python3
"""Index named theoretical source presentations without Lean-route heuristics.

This module deliberately operates only on canonical UTF-8 text/TeX artifacts.
It does not read files, inspect source-map keys, or inspect Lean declarations.
Callers supply source text and a source-map ``items`` object, then use the
reconciliation result to decide whether every discovered named presentation is
anchored by source location metadata or by an exact byte-pinned quote.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import posixpath
import re
from typing import Any, Iterable, Mapping


NAMED_RESULT_KINDS = frozenset(
    {
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "claim",
        "definition",
        "equation",
        "formula",
        "algorithm",
        "assumption",
        # A named conjecture or open question is source-visible but has an
        # explicit non-proof disposition.  It is never silently ignored just
        # because it cannot receive theorem-proof credit.
        "open_problem",
    }
)

OPEN_NAMED_PRESENTATION_KIND = "open_problem"
UNCLASSIFIED_NAMED_PRESENTATION_KIND = "unclassified"
REVIEW_CANDIDATE_PRESENTATION_KIND_PREFIX = "review_candidate_"
REVIEW_CANDIDATE_NORMAL_DISPOSITION = "material_named_claim"
REVIEW_CANDIDATE_DEEP_DISPOSITION = "deep_audit_material"
REVIEW_CANDIDATE_MECHANICAL_DISCOVERY = "mechanical_labelled_heading"
REVIEW_CANDIDATE_HOLISTIC_DISCOVERY = "holistic_full_text_review"
REVIEW_CANDIDATE_DISCOVERY_BASES = frozenset(
    {
        REVIEW_CANDIDATE_MECHANICAL_DISCOVERY,
        REVIEW_CANDIDATE_HOLISTIC_DISCOVERY,
    }
)
REVIEW_CANDIDATE_DISPOSITIONS = frozenset(
    {
        REVIEW_CANDIDATE_NORMAL_DISPOSITION,
        REVIEW_CANDIDATE_DEEP_DISPOSITION,
    }
)

# A PDF/text extraction can conservatively retain explanatory prose or a proof
# after a visible theorem heading.  A source map may therefore attach a
# separately reviewed, byte-pinned statement core to that heading.  This is a
# source-only reconciliation aid: it cannot name a Lean declaration, choose a
# map key, or replace the ordinary exact-full-span rule for items that do not
# opt in.
SOURCE_PRESENTATION_RECONCILIATION_FIELD = "source_presentation_reconciliation"
SOURCE_PRESENTATION_RECONCILIATION_SCHEMA = 1
SOURCE_PRESENTATION_RECONCILIATION_RELATION = "conservative_text_span_core"
SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD = "core_anchor"
SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS = frozenset(
    {
        "completed_statement_then_explanation",
        "complete_indexed_presentation",
        "interleaved_parallel_columns",
    }
)

# These are visible source titles, not source-map keys or Lean identifiers.
# The second group deliberately remains unclassified until the curator records
# a source-pinned ``environment_kinds``/``heading_kinds`` interpretation.  A
# generic audit must not assume that a paper's local "Property" or "Case"
# environment means the same thing as a theorem in another paper.
_STANDARD_NAMED_TITLE_WORDS = frozenset(
    {
        "theorem",
        "proposition",
        "lemma",
        "corollary",
        "claim",
        "definition",
        "equation",
        "formula",
        "algorithm",
        "assumption",
        "conjecture",
    }
)
_UNCLASSIFIED_NAMED_TITLE_WORDS = frozenset(
    {
        "fact",
        "property",
        "condition",
        "model",
        "desideratum",
        "setup",
        "axiom",
        "postulate",
        "observation",
        "result",
    }
)
_NON_THEORETICAL_TITLE_WORDS = frozenset(
    {
        "example",
        "remark",
        "comment",
        "note",
        "discussion",
    }
)
_REVIEW_CANDIDATE_TITLE_WORDS = frozenset(
    {*_NON_THEORETICAL_TITLE_WORDS, "observation"}
)
_REVIEW_CANDIDATE_VISIBLE_KINDS = frozenset(
    {*_REVIEW_CANDIDATE_TITLE_WORDS, "holistic"}
)
_TEXT_TITLE_PATTERN = "|".join(
    [
        r"open\s+(?:question|problem)",
        # ``Eq. (1)`` is a common source presentation for a numbered equation.
        # Treat it as a visible source title, not as a source-map or Lean name.
        r"eq(?:uation)?\.?",
        *sorted(_STANDARD_NAMED_TITLE_WORDS, key=len, reverse=True),
        *sorted(_UNCLASSIFIED_NAMED_TITLE_WORDS, key=len, reverse=True),
        *sorted(_NON_THEORETICAL_TITLE_WORDS, key=len, reverse=True),
    ]
)
_TEX_ENV_RE = re.compile(
    r"\\(?P<action>begin|end)\s*\{\s*(?P<environment>[A-Za-z@][A-Za-z0-9_@-]*)(?P<star>\*)?\s*\}",
    re.IGNORECASE,
)
_TEX_RESTATABLE_ENVIRONMENT = "restatable"
_TEX_ENVIRONMENT_NAME_RE = re.compile(r"[A-Za-z@][A-Za-z0-9_@-]*\Z")
_TEX_NEW_THEOREM_RE = re.compile(
    r"""
    \\newtheorem\*?\s*
    \{\s*(?P<environment>[A-Za-z@][A-Za-z0-9_@-]*)\s*\}
    (?:\s*\[[^\]]+\])?
    \s*\{\s*(?P<title>[^{}]+)\s*\}
    """,
    re.IGNORECASE | re.VERBOSE,
)
_TEX_LABEL_RE = re.compile(r"\\label\s*\{\s*(?P<label>[^{}\s][^{}]*)\s*\}")
_TEX_CAPTION_RE = re.compile(r"\\caption(?:\[[^\]]*\])?\s*\{(?P<caption>[^{}]+)\}")
_TEX_TAG_RE = re.compile(r"\\tag\*?\s*\{(?P<tag>[^{}]+)\}")
_TEX_ROW_BREAK_RE = re.compile(r"(?<!\\)\\\\(?!\\)")
_TEX_ROW_BREAK_SUFFIX_RE = re.compile(r"\s*(?:\[[^\]]*\])?\s*$")
_TEX_NONNUMBER_RE = re.compile(r"\\(?:notag|nonumber)\b", re.IGNORECASE)
_TEX_UNSUPPORTED_MULTIROW_RE = re.compile(
    r"\\(?:begin|end|intertext|shortintertext|displaybreak|allowdisplaybreaks)\b",
    re.IGNORECASE,
)
_TEX_LEADING_COMMAND_RE = re.compile(
    r"^\s*\\(?:noindent|smallskip|medskip|bigskip|paragraph)\b\s*",
    re.IGNORECASE,
)
_TEX_INLINE_STYLE_RE = re.compile(r"\\(?:textbf|textit|emph)\s*\{")
_TEXT_OCR_SPACED_TITLE_RE = re.compile(
    r"\b(?:T\s+HEOREM|P\s+ROPOSITION|L\s+EMMA|C\s+OROLLARY|"
    r"C\s+LAIM|C\s+ONJECTURE|D\s+EFINITION|A\s+LGORITHM|A\s+SSUMPTION)\b",
    re.IGNORECASE,
)
_TEXT_OCR_SPACED_TITLE_CANONICAL = {
    "theorem": "Theorem",
    "proposition": "Proposition",
    "lemma": "Lemma",
    "corollary": "Corollary",
    "claim": "Claim",
    "conjecture": "Conjecture",
    "definition": "Definition",
    "algorithm": "Algorithm",
    "assumption": "Assumption",
}
_TEXT_OCR_SPACED_HEADING_RE = re.compile(
    r"""
    \b(?P<title>
        T\s+HEOREM|P\s+ROPOSITION|L\s+EMMA|C\s+OROLLARY|
        C\s+LAIM|C\s+ONJECTURE|D\s+EFINITION|A\s+LGORITHM|A\s+SSUMPTION
    )\s+
    (?P<label>
        (?:[A-Za-z]+\.)?\d+(?:\.\d+)*|[A-Za-z]+(?:\.\d+)*
    )
    (?!\.\d)
    (?=\s*(?:[.:)\]\-\N{EN DASH}\N{EM DASH}]|\s+(?-i:[A-Z])))
    """,
    re.IGNORECASE | re.VERBOSE,
)
_TEXT_HEADING_RE = re.compile(
    rf"""
    ^\s*
    (?P<title>{_TEXT_TITLE_PATTERN})\s+
    (?P<label>
        (?:\(\s*(?:[A-Za-z]+\.)?\d+(?:\.\d+)*\s*\)|\d+(?:\.\d+)*|[A-Za-z]+(?:\.\d+)*)
        (?:\s*\(\s*(?:[ivxlcdm]+|[a-z]|\d+)\s*\))?
    )
    (?!\.\d)
    (?:
        (?=\s*(?:$|[.:)\]\-\N{{EN DASH}}\N{{EM DASH}}]))
      # A parenthesized subtitle is part of a visibly titled result even when
      # it begins with mathematical notation or a lowercase word, e.g.
      # ``Definition 1 (gamma-homogeneity)``.  The title/label still have to
      # begin the line, so ordinary inline cross-references remain excluded.
      | (?=\s+\()
      | (?=\s+(?-i:[A-Z]))
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
# Some scanned PDFs visibly head a standalone definition as ``DEFINITION.``
# without a number.  It is a source presentation, unlike an ordinary sentence
# mentioning a definition, only when the all-caps heading begins its own line.
# The extractor below gives this narrow form a bounded first-sentence span; it
# never uses a source-map key, a Lean declaration, or a local paper convention
# to infer that boundary.
_TEXT_UNNUMBERED_DEFINITION_HEADING_RE = re.compile(
    r"^\s*(?P<title>DEFINITION)\s*\.\s*(?=\S|$)"
)
_TEXT_UNNUMBERED_DEFINITION_MAX_LINES = 8
# PDF-to-text extraction can interleave two columns onto one line.  When the
# right column begins a decimal-numbered result and its conclusion starts with
# an uppercase token, recover that presentation without treating ordinary
# lower-case cross-references (for example, "Lemma 9.2 we use below") as a
# heading.  The rule is deliberately limited to decimal labels because a
# bare-number title embedded in prose is too ambiguous to index safely.
_TEXT_EMBEDDED_DECIMAL_HEADING_RE = re.compile(
    rf"""
    \b
    (?P<title>{_TEXT_TITLE_PATTERN})\s+
    (?P<label>(?:(?:[A-Za-z]+\.)?\d+\.\d+(?:\.\d+)*))
    (?!\.\d)
    # A visible source subtitle may intervene between the decimal label and
    # the first sentence, e.g. ``Theorem 1.2 (Informal). If ...``.  Keep the
    # subtitle bounded and on the same line so this remains a conservative
    # two-column heading rule rather than a general prose-reference parser.
    (?:\s*\([^()\n]{{1,80}}\)\s*[.:]?)?
    (?=\s+(?-i:[A-Z]))
    """,
    re.IGNORECASE | re.VERBOSE,
)
_TEXT_SUBPART_MARKER_RE = re.compile(
    r"""
    ^\s*
    \(\s*(?P<label>i|ii|iii|iv|v|vi|vii|viii|ix|x|xi|xii)\s*\)
    """,
    re.IGNORECASE | re.VERBOSE,
)
_PROOF_START_RE = re.compile(r"^\s*(?:proof\.?|\\begin\s*\{\s*proof\*?\s*\})", re.I)
_TEXT_PROOF_NARRATIVE_RE = re.compile(
    r"""
    ^\s*(?:
        proof\s+of\b
      | we\s+(?:now\s+|next\s+|then\s+)?(?:prove|show)\b
      | we\s+spend\b.*\bproving\b
      | we\s+turn\s+to\s+(?:the\s+)?proof\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
# A text/PDF transcript can defer a proof, so proof markers alone cannot stop
# a named result from absorbing a later paper section. Keep this intentionally
# narrow: standalone closing/back-matter titles and visibly numbered/lettered
# title lines are source-presentation boundaries, while ordinary narrative
# prose (including blank lines inside a displayed conclusion) is not guessed
# to be a boundary.
_TEXT_SECTION_BOUNDARY_RE = re.compile(
    r"""
    ^\s*(?:
        (?i:abstract|introduction|background|conclusion(?:s)?|references|
            acknowledg(?:e)?ments|appendix(?:\s+[A-Z])?)
      |
        (?:\d+(?:\.\d+)*|[A-Z])(?:\s*[.:])?\s+
        (?-i:[A-Z])[A-Za-z0-9][A-Za-z0-9 &'(),/\-]{0,100}
    )\s*$
    """,
    re.VERBOSE,
)
# Some PDF transcripts split a visible section header across two lines, for
# example ``2.4`` followed by ``A Preference for Independence``.  That pair
# is a source-presentation boundary, not part of the preceding theorem.
_TEXT_STANDALONE_DECIMAL_SECTION_RE = re.compile(r"^\s*\d+\.\d+(?:\.\d+)*\s*$")
_TEXT_SECTION_TITLE_LINE_RE = re.compile(
    r"^\s*(?-i:[A-Z])[A-Za-z0-9 &'(),/\-]{0,101}\s*$"
)
_TEXT_REFERENCE_CONTINUATION_RE = re.compile(
    r"^\s*[.:)]?\s*(?:thus|therefore|hence|consequently|similarly|moreover|however|indeed)\b",
    re.IGNORECASE,
)
# PDF extraction can wrap the object of a prose reference onto a fresh line,
# making ``Theorem 2: ...`` look like a heading at column zero.  These are
# source-grammar leads whose unfinished sentence expects a referenced result;
# they do not depend on paper-specific labels, map keys, or Lean names.
_TEXT_PRIOR_NAMED_REFERENCE_LEAD_RE = re.compile(
    r"""
    (?:
        \b(?:see|cf\.?|compare(?:\s+with)?|invoke(?:s|d)?|use(?:s|d)?|using|
            appl(?:y|ies|ied)|illustrat(?:e|es|ed)|summari[sz](?:e|es|ed)|
            confirm(?:s|ed)?|support(?:s|ed)?)
      | \b(?:according\s+to|as\s+(?:shown|stated|proved)\s+in|
            follow(?:s|ed)?\s+from|
            (?:defined|described|introduced)\s+(?:above|earlier|before))
      | \b(?:in|from|by)
    )\s*$
    """,
    re.IGNORECASE | re.VERBOSE,
)
# Captions and labelled deep-only presentations are likewise visible source
# boundaries. They are not theorem obligations in ordinary mode, but a result
# span must not silently absorb one after a transcript blank line.
_TEXT_NONRESULT_PRESENTATION_BOUNDARY_RE = re.compile(
    r"""
    ^\s*(?:figure|table|remark|example|caption)\s+
    (?:\(?[A-Za-z]?\d+(?:\.\d+)*\)?|[A-Z])\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
_ROMAN_SUBPART_LABELS = (
    "i",
    "ii",
    "iii",
    "iv",
    "v",
    "vi",
    "vii",
    "viii",
    "ix",
    "x",
    "xi",
    "xii",
)
_SOURCE_LOCATION_RE = re.compile(
    r"(?P<path>[^\s,:]+):(?P<start>[1-9]\d*)(?:-(?P<end>[1-9]\d*))?"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_ISO_LIKE_UTC_TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z$"
)
_SOURCE_STATEMENT_TERMINAL_RE = re.compile(r"[.!?](?:[\]\)}\"']*)\s*$")
_SOURCE_STATEMENT_CONTINUATION_RE = re.compile(
    r"^\s*(?:then|and|or|where|provided(?:\s+that)?|if|for\s+(?:every|all))\b",
    re.IGNORECASE,
)
_SOURCE_HEADING_SEPARATOR_RE = re.compile(
    r"^[\s.:)\]\-\N{EN DASH}\N{EM DASH}]+"
)
_SOURCE_PARENTHETICAL_TITLE_ONLY_RE = re.compile(
    r"^\([^()]*\)[.!?]?(?:[\]\)}\"']*)\s*$"
)

# These are standard AMS/LaTeX display environments.  Their ordinary rendered
# numbers and ``\\label`` keys are cross-reference mechanics, not named
# theoretical source presentations.  They are only indexed when the source
# visibly calls the display a Formula/Equation, for example through a matching
# tag or a source-declared theorem-style title.
_STANDARD_NUMBERED_DISPLAY_ENVIRONMENTS = frozenset(
    {
        "equation",
        "align",
        "alignat",
        "flalign",
        "gather",
        "multline",
    }
)
_STANDARD_MULTIROW_DISPLAY_ENVIRONMENTS = frozenset({"align", "gather"})
_STANDARD_VISIBLE_TITLE_ALIASES = {"eq": "equation", "eqn": "equation"}


@dataclass(frozen=True)
class SourceLineSpan:
    """One source-relative inclusive line span."""

    path: str
    line_start: int
    line_end: int


@dataclass(frozen=True)
class NamedResultPresentation:
    """A named source result discovered from source presentation, not metadata."""

    kind: str
    label: str
    line_start: int
    line_end: int
    presentation: str


@dataclass(frozen=True)
class NamedResultCoverageMatch:
    """One opaque source-map item matched by source-only anchor evidence."""

    item_id: str
    evidence: tuple[str, ...]


@dataclass(frozen=True)
class NamedResultReconciliation:
    """The source-only coverage result for one discovered presentation."""

    presentation: NamedResultPresentation
    matches: tuple[NamedResultCoverageMatch, ...]

    @property
    def covered(self) -> bool:
        return bool(self.matches)


@dataclass(frozen=True)
class ReviewedSourcePresentationInventory:
    """One source-only discovery and reviewed-classification projection."""

    discovered: tuple[NamedResultPresentation, ...]
    candidates: tuple[NamedResultPresentation, ...]
    classified: tuple[NamedResultPresentation, ...]

    @property
    def candidate_sha256(self) -> str:
        return named_result_presentations_sha256(self.candidates)

    @property
    def classified_sha256(self) -> str:
        return named_result_presentations_sha256(self.classified)


def _normalized_source_text(source_text: str) -> str:
    return source_text.replace("\r\n", "\n").replace("\r", "\n")


def _source_lines(source_text: str) -> list[str]:
    normalized = _normalized_source_text(source_text)
    lines = normalized.split("\n")
    if normalized.endswith("\n"):
        lines.pop()
    return lines


def _strip_tex_comment(line: str) -> str:
    """Remove an unescaped TeX comment while preserving ordinary text."""

    for index, character in enumerate(line):
        if character != "%":
            continue
        backslashes = 0
        cursor = index - 1
        while cursor >= 0 and line[cursor] == "\\":
            backslashes += 1
            cursor -= 1
        if backslashes % 2 == 0:
            return line[:index]
    return line


def _skip_tex_whitespace_and_comments(source_text: str, cursor: int) -> int:
    """Advance past TeX spacing and whole-line/comment-tail comments."""

    while cursor < len(source_text):
        while cursor < len(source_text) and source_text[cursor].isspace():
            cursor += 1
        if cursor >= len(source_text) or source_text[cursor] != "%":
            return cursor
        newline = source_text.find("\n", cursor)
        if newline < 0:
            return len(source_text)
        cursor = newline + 1
    return cursor


def _parse_tex_delimited_argument(
    source_text: str,
    cursor: int,
    *,
    opening: str,
    closing: str,
) -> tuple[str, int] | None:
    """Parse one balanced, non-verbatim TeX argument from ``cursor``.

    The source indexer is intentionally not a general TeX parser.  This small
    reader is limited to the standard optional and mandatory arguments which
    immediately follow ``\\begin{restatable}``, while still accepting ordinary
    whitespace, comments, nested groups, and escaped delimiters.
    """

    if cursor >= len(source_text) or source_text[cursor] != opening:
        return None
    depth = 1
    content_start = cursor + 1
    cursor += 1
    while cursor < len(source_text):
        character = source_text[cursor]
        if character == "\\":
            # A command or escaped delimiter cannot close this argument.
            cursor += 2
            continue
        if character == "%":
            newline = source_text.find("\n", cursor)
            if newline < 0:
                return None
            cursor = newline + 1
            continue
        if character == opening:
            depth += 1
        elif character == closing:
            depth -= 1
            if depth == 0:
                return source_text[content_start:cursor], cursor + 1
        cursor += 1
    return None


def _restatable_inner_environment(
    source_text: str, cursor: int
) -> str | None:
    """Read the semantic inner environment of a standard ``restatable``.

    ``thmtools`` writes a result as
    ``\\begin{restatable}[optional title]{theorem}{macroName}``.  The first
    mandatory argument controls the rendered theorem-like result; the second
    names a TeX macro and is deliberately not used by the audit index.
    """

    cursor = _skip_tex_whitespace_and_comments(source_text, cursor)
    if cursor < len(source_text) and source_text[cursor] == "[":
        optional_argument = _parse_tex_delimited_argument(
            source_text, cursor, opening="[", closing="]"
        )
        if optional_argument is None:
            return None
        _optional_title, cursor = optional_argument
        cursor = _skip_tex_whitespace_and_comments(source_text, cursor)

    inner_argument = _parse_tex_delimited_argument(
        source_text, cursor, opening="{", closing="}"
    )
    if inner_argument is None:
        return None
    raw_environment, cursor = inner_argument
    cursor = _skip_tex_whitespace_and_comments(source_text, cursor)
    macro_argument = _parse_tex_delimited_argument(
        source_text, cursor, opening="{", closing="}"
    )
    if macro_argument is None or not macro_argument[0].strip():
        return None

    environment = raw_environment.strip().lower()
    if not _TEX_ENVIRONMENT_NAME_RE.fullmatch(environment):
        return None
    return environment


def _presentation_label(kind: str, label: str, line_start: int) -> str:
    text = label.strip()
    return text or f"{kind}@{line_start}"


def _is_numbered_algorithm_label(label: str) -> bool:
    return bool(re.fullmatch(r"(?:\d+(?:\.\d+)*|[A-Za-z]+\.\d+(?:\.\d+)*)", label))


def _normalized_visible_title(title: str) -> str:
    """Normalize a rendered source presentation title for declaration lookup."""

    cleaned = re.sub(r"\\[A-Za-z@]+\*?", " ", title)
    words = re.findall(r"[A-Za-z]+", cleaned.lower())
    return " ".join(words)


def _visible_title_result_kind(title: str) -> str:
    """Return a canonical kind only for an unambiguous visible source title.

    Local environment names are intentionally irrelevant here.  A generic
    source title such as ``Fact`` or ``Property`` may be a theorem-like claim,
    a model axiom, or an empirical observation depending on the paper.  Those
    titles are discovered below but remain unclassified until the source-pinned
    inventory receipt records a declarative classification.
    """

    normalized = _normalized_visible_title(title)
    if normalized in {"open question", "open problem", "conjecture"}:
        return OPEN_NAMED_PRESENTATION_KIND
    if normalized in _STANDARD_VISIBLE_TITLE_ALIASES:
        return _STANDARD_VISIBLE_TITLE_ALIASES[normalized]
    words = normalized.split()
    for word in words:
        singular = word[:-1] if word.endswith("s") else word
        if singular in NAMED_RESULT_KINDS and singular != OPEN_NAMED_PRESENTATION_KIND:
            return singular
    return ""


def _visible_title_is_non_theoretical(title: str) -> bool:
    """Whether a declared source title is a routine non-theory presentation."""

    normalized = _normalized_visible_title(title)
    words = normalized.split()
    return bool(words and words[0] in _NON_THEORETICAL_TITLE_WORDS)


def _review_candidate_kind(title: str) -> str:
    """Return a stable source-only kind for a labelled review candidate."""

    normalized = _normalized_visible_title(title)
    words = normalized.split()
    if not words or words[0] not in _REVIEW_CANDIDATE_TITLE_WORDS:
        return ""
    return REVIEW_CANDIDATE_PRESENTATION_KIND_PREFIX + words[0]


def review_candidate_visible_kind(presentation_kind: object) -> str:
    """Return the visible title kind encoded by a review-candidate kind."""

    kind = str(presentation_kind or "").strip().lower()
    if not kind.startswith(REVIEW_CANDIDATE_PRESENTATION_KIND_PREFIX):
        return ""
    visible = kind.removeprefix(REVIEW_CANDIDATE_PRESENTATION_KIND_PREFIX)
    return visible if visible in _REVIEW_CANDIDATE_VISIBLE_KINDS else ""


def _declared_tex_environment_titles(source_text: str) -> dict[str, str]:
    """Return visible titles for source-declared theorem-like environments."""

    declaration_text = "\n".join(
        _strip_tex_comment(line) for line in _source_lines(source_text)
    )
    return {
        match.group("environment").strip().lower(): match.group("title").strip()
        for match in _TEX_NEW_THEOREM_RE.finditer(declaration_text)
    }


def _validated_kind_mapping(
    value: Mapping[str, str] | None,
    *,
    field_name: str,
) -> dict[str, str]:
    """Validate a declarative source-presentation classification table."""

    if value is None:
        return {}
    if not isinstance(value, Mapping):
        raise ValueError(
            f"{field_name} must be a mapping of source presentation to result kind"
        )
    result: dict[str, str] = {}
    for raw_key, raw_kind in value.items():
        if not isinstance(raw_key, str) or not raw_key.strip():
            raise ValueError(f"{field_name} keys must be nonempty strings")
        if (
            not isinstance(raw_kind, str)
            or raw_kind.strip().lower() not in NAMED_RESULT_KINDS
        ):
            raise ValueError(
                f"{field_name} values must be supported named result kinds"
            )
        result[raw_key.strip().lower()] = raw_kind.strip().lower()
    return result


def _tex_environment_kind_map(
    source_text: str, environment_kinds: Mapping[str, str] | None
) -> tuple[dict[str, str], dict[str, str], frozenset[str]]:
    """Return source-declared and caller-declared TeX environment meanings.

    A declarative mapping resolves only an ambiguous local presentation.  It
    cannot reinterpret a source-visible ``Theorem`` as a definition (or any
    other different kind), since that would weaken the source obligation merely
    through audit metadata.
    """

    result = {kind: kind for kind in NAMED_RESULT_KINDS}
    result.update(
        {
            environment: "equation"
            for environment in _STANDARD_NUMBERED_DISPLAY_ENVIRONMENTS
        }
    )
    declarations = _declared_tex_environment_titles(source_text)
    for environment, title in declarations.items():
        kind = _visible_title_result_kind(title)
        if kind:
            result[environment] = kind
    configured = _validated_kind_mapping(
        environment_kinds, field_name="environment_kinds"
    )
    for environment, configured_kind in configured.items():
        visible_kind = (
            _visible_title_result_kind(declarations[environment])
            if environment in declarations
            else ""
        )
        canonical_kind = visible_kind or result.get(environment, "")
        if canonical_kind and configured_kind != canonical_kind:
            raise ValueError(
                "environment_kinds cannot override unambiguous source presentation "
                f"`{environment}` ({canonical_kind}) as `{configured_kind}`"
            )
        result[environment] = configured_kind
    return result, declarations, frozenset(configured)


def _tex_equation_or_formula_is_named(
    entry: Mapping[str, object], declared_environment_titles: Mapping[str, str]
) -> bool:
    """Whether a display visibly presents itself as a Formula or Equation."""

    tag_kind = _visible_title_result_kind(str(entry.get("tag") or ""))
    if tag_kind in {"equation", "formula"}:
        return True
    environment = str(entry.get("environment") or "")
    declared_kind = _visible_title_result_kind(
        str(declared_environment_titles.get(environment) or "")
    )
    # A ``newtheorem``-style source declaration supplies the visible title
    # even when the author omits a local ``\\label``.
    return declared_kind in {"equation", "formula"}


def _tex_tag_formula_or_equation_kind(tag: str) -> str:
    """Return a Formula/Equation kind only for a visibly titled tag."""

    kind = _visible_title_result_kind(tag)
    return kind if kind in {"equation", "formula"} else ""


def _multiline_display_visible_formula_or_equation_tag(
    source_lines: list[str], entry: Mapping[str, object], line_end: int
) -> tuple[str, str] | None:
    """Return the first explicitly titled Formula/Equation tag in a display."""

    line_start = entry.get("line_start")
    if not isinstance(line_start, int) or line_start < 1 or line_end < line_start:
        return None
    display_text = "\n".join(
        _strip_tex_comment(source_lines[line_number - 1])
        for line_number in range(line_start, line_end + 1)
    )
    for match in _TEX_TAG_RE.finditer(display_text):
        tag = match.group("tag").strip()
        kind = _tex_tag_formula_or_equation_kind(tag)
        if kind:
            return kind, tag
    return None


def _simple_multiline_equation_rows(
    source_lines: list[str], entry: Mapping[str, object], line_end: int
) -> list[NamedResultPresentation] | None:
    """Extract clear physical-line rows from an unstarred ``align``/``gather``.

    This deliberately accepts only the ordinary one-row-per-source-line form.
    Nested displays, multi-line rows, and special alignment commands are left
    unparsed instead of guessing which rendered rows have a visible Formula or
    Equation title. A caller can then retain only an explicit titled tag for
    the enclosing display.
    """

    line_start = entry.get("line_start")
    environment = str(entry.get("environment") or "")
    if (
        not isinstance(line_start, int)
        or line_start < 1
        or line_end <= line_start
        or environment not in _STANDARD_MULTIROW_DISPLAY_ENVIRONMENTS
    ):
        return None

    # A label/tag on the same physical line as ``\\begin`` belongs to the
    # enclosing display rather than an unambiguously identified numbered row.
    opening_line = _strip_tex_comment(source_lines[line_start - 1])
    opening_match = next(
        (
            match
            for match in _TEX_ENV_RE.finditer(opening_line)
            if match.group("action").lower() == "begin"
            and match.group("environment").strip().lower() == environment
        ),
        None,
    )
    if opening_match is None:
        return None
    if _TEX_LABEL_RE.search(opening_line[opening_match.end() :]) or _TEX_TAG_RE.search(
        opening_line[opening_match.end() :]
    ):
        return None

    body_lines = [
        (line_number, _strip_tex_comment(source_lines[line_number - 1]).strip())
        for line_number in range(line_start + 1, line_end)
    ]
    rows = [(line_number, line) for line_number, line in body_lines if line]
    if not rows:
        return None

    presentations: list[NamedResultPresentation] = []
    for index, (row_line, row_text) in enumerate(rows):
        if _TEX_UNSUPPORTED_MULTIROW_RE.search(row_text):
            return None
        row_breaks = list(_TEX_ROW_BREAK_RE.finditer(row_text))
        is_last_row = index == len(rows) - 1
        if len(row_breaks) > 1:
            return None
        if not is_last_row and len(row_breaks) != 1:
            return None
        if row_breaks:
            row_break = row_breaks[0]
            if not _TEX_ROW_BREAK_SUFFIX_RE.fullmatch(row_text[row_break.end() :]):
                return None
            row_body = row_text[: row_break.start()]
        else:
            row_body = row_text
        if not row_body.strip():
            return None

        labels = list(_TEX_LABEL_RE.finditer(row_body))
        tags = list(_TEX_TAG_RE.finditer(row_body))
        if (
            len(labels) > 1
            or len(tags) > 1
            or (r"\label" in row_body and not labels)
            or (r"\tag" in row_body and not tags)
        ):
            return None
        if _TEX_NONNUMBER_RE.search(row_body):
            continue
        tag = tags[0].group("tag").strip() if tags else ""
        visible_kind = _tex_tag_formula_or_equation_kind(tag)
        if not visible_kind:
            continue
        presentations.append(
            NamedResultPresentation(
                kind=visible_kind,
                label=_presentation_label(visible_kind, tag, row_line),
                line_start=row_line,
                line_end=row_line,
                presentation="tex_multiline_display_row",
            )
        )
    return presentations


def extract_tex_named_result_presentations(
    source_text: str,
    *,
    environment_kinds: Mapping[str, str] | None = None,
    include_review_candidates: bool = False,
) -> list[NamedResultPresentation]:
    """Extract standard named TeX environments with inclusive source spans.

    The TeX environment itself is the source presentation.  Numbered theorem
    environments need not have a ``\\label`` because their rendered number is
    supplied by the document class; a label is retained when present for useful
    diagnostics.  Standard ``\\newtheorem`` declarations are read from the
    source so aliases such as ``thm`` and ``prop`` remain source-visible rather
    than being silently ignored.  ``thmtools`` ``restatable`` wrappers are
    classified from their first inner environment argument, not the outer
    wrapper or its TeX macro identifier.  ``environment_kinds`` permits a
    declarative caller-supplied mapping for document-class-generated aliases.
    Ordinary numbered equation/alignment displays and ``\\label`` keys do not
    enter ordinary named-theory coverage. A Formula/Equation display needs a
    source-visible Formula/Equation title (a matching tag or source-declared
    theorem-style title). Algorithm environments require a caption or label so
    an unnumbered algorithmic implementation block cannot become an obligation.
    """

    (
        resolved_environment_kinds,
        declared_environment_titles,
        _explicitly_configured_environments,
    ) = _tex_environment_kind_map(source_text, environment_kinds)
    active: list[dict[str, Any]] = []
    presentations: list[NamedResultPresentation] = []
    normalized_source_text = _normalized_source_text(source_text)
    source_lines = _source_lines(normalized_source_text)
    source_offset = 0
    for line_number, raw_line in enumerate(source_lines, start=1):
        line = _strip_tex_comment(raw_line)
        events: list[tuple[int, str, re.Match[str]]] = [
            (match.start(), "environment", match)
            for match in _TEX_ENV_RE.finditer(line)
        ]
        events.extend(
            (match.start(), "label", match) for match in _TEX_LABEL_RE.finditer(line)
        )
        events.extend(
            (match.start(), "caption", match)
            for match in _TEX_CAPTION_RE.finditer(line)
        )
        events.extend(
            (match.start(), "tag", match) for match in _TEX_TAG_RE.finditer(line)
        )
        for _offset, event_kind, match in sorted(events, key=lambda event: event[0]):
            if event_kind == "label":
                if active and not active[-1]["label"]:
                    active[-1]["label"] = match.group("label").strip()
                continue
            if event_kind == "caption":
                if active and active[-1]["kind"] == "algorithm":
                    active[-1]["caption"] = match.group("caption").strip()
                continue
            if event_kind == "tag":
                if active and not active[-1]["tag"]:
                    active[-1]["tag"] = match.group("tag").strip()
                continue

            environment = match.group("environment").strip().lower()
            action = match.group("action").lower()
            if action == "begin":
                is_restatable = environment == _TEX_RESTATABLE_ENVIRONMENT
                semantic_environment = environment
                if is_restatable:
                    parsed_environment = _restatable_inner_environment(
                        normalized_source_text, source_offset + match.end()
                    )
                    if parsed_environment is None:
                        # A malformed wrapper has no reliable inner source
                        # presentation. Do not classify it from the wrapper or
                        # from the macro identifier that follows it.
                        continue
                    semantic_environment = parsed_environment

                kind = resolved_environment_kinds.get(semantic_environment)
                if not kind and is_restatable:
                    # The first ``restatable`` argument is a source-visible
                    # theorem-like title. It can therefore carry a standard
                    # meaning even if this file omits the preamble declaration.
                    kind = _visible_title_result_kind(semantic_environment)
                if not kind:
                    declared_title = declared_environment_titles.get(
                        semantic_environment
                    )
                    if declared_title is None:
                        candidate_kind = _review_candidate_kind(semantic_environment)
                        if candidate_kind and include_review_candidates:
                            kind = candidate_kind
                            display_kind = _normalized_visible_title(
                                semantic_environment
                            )
                        elif not is_restatable or _visible_title_is_non_theoretical(
                            semantic_environment
                        ):
                            continue
                        else:
                            # A restatable wrapper visibly contains a named result,
                            # but its inner source title has no generic meaning.
                            # Preserve it as a source-first closeout blocker rather
                            # than guessing from the inner local environment name.
                            kind = UNCLASSIFIED_NAMED_PRESENTATION_KIND
                            display_kind = (
                                _normalized_visible_title(semantic_environment)
                                or semantic_environment
                            )
                    elif (
                        candidate_kind := _review_candidate_kind(declared_title)
                    ) and include_review_candidates:
                        kind = candidate_kind
                        display_kind = _normalized_visible_title(declared_title)
                    elif _visible_title_is_non_theoretical(declared_title):
                        continue
                    else:
                        # The source itself visibly declares a named
                        # presentation, but its title has no generic semantic
                        # interpretation. Preserve it as an explicit closeout
                        # blocker rather than guessing from its local
                        # environment name.
                        kind = UNCLASSIFIED_NAMED_PRESENTATION_KIND
                        display_kind = (
                            _normalized_visible_title(declared_title)
                            or semantic_environment
                        )
                else:
                    display_kind = kind
                active.append(
                    {
                        "kind": kind,
                        "display_kind": display_kind,
                        "environment": environment,
                        "semantic_environment": semantic_environment,
                        "line_start": line_number,
                        "label": "",
                        "caption": "",
                        "tag": "",
                        "starred": bool(match.group("star")),
                        "restatable": is_restatable,
                    }
                )
                continue

            matching_index = next(
                (
                    index
                    for index in range(len(active) - 1, -1, -1)
                    if active[index]["environment"] == environment
                ),
                None,
            )
            if matching_index is None:
                continue
            entry = active.pop(matching_index)
            entry_kind = str(entry["kind"])
            if (
                entry_kind == "equation"
                and environment in _STANDARD_MULTIROW_DISPLAY_ENVIRONMENTS
                and not bool(entry["starred"])
            ):
                row_presentations = _simple_multiline_equation_rows(
                    source_lines, entry, line_number
                )
                if row_presentations is not None:
                    presentations.extend(row_presentations)
                    continue
                visible_tag = _multiline_display_visible_formula_or_equation_tag(
                    source_lines, entry, line_number
                )
                if visible_tag is None:
                    # Ordinary alignment row numbers and labels are not named
                    # theoretical presentations. Leave them to deep review.
                    continue
                visible_kind, visible_label = visible_tag
                # The source explicitly names this display Formula/Equation,
                # but its row syntax cannot be safely split. Keep the complete
                # display as one named presentation instead of inventing rows.
                presentations.append(
                    NamedResultPresentation(
                        kind=visible_kind,
                        label=_presentation_label(
                            visible_kind,
                            visible_label,
                            int(entry["line_start"]),
                        ),
                        line_start=int(entry["line_start"]),
                        line_end=line_number,
                        presentation="tex_multiline_named_display",
                    )
                )
                continue
            label = _presentation_label(
                str(entry["display_kind"]),
                str(entry["label"] or entry["tag"]),
                int(entry["line_start"]),
            )
            if (
                not bool(entry.get("restatable"))
                and entry_kind == "algorithm"
                and not (entry["label"] or entry["caption"])
            ):
                continue
            if not bool(entry.get("restatable")) and entry_kind in {
                "equation",
                "formula",
            } and not _tex_equation_or_formula_is_named(
                entry, declared_environment_titles
            ):
                continue
            presentations.append(
                NamedResultPresentation(
                    kind=entry_kind,
                    label=label,
                    line_start=int(entry["line_start"]),
                    line_end=line_number,
                    presentation="tex_environment",
                )
            )
        source_offset += len(raw_line) + 1
    return sorted(
        presentations,
        key=lambda item: (item.line_start, item.line_end, item.kind, item.label),
    )


def _clean_text_heading_line(line: str) -> str:
    cleaned = _TEX_LEADING_COMMAND_RE.sub("", _strip_tex_comment(line))
    cleaned = _TEX_INLINE_STYLE_RE.sub("", cleaned)
    cleaned = cleaned.replace("}", "")

    def canonical_title(match: re.Match[str]) -> str:
        collapsed = re.sub(r"\s+", "", match.group(0)).lower()
        return _TEXT_OCR_SPACED_TITLE_CANONICAL[collapsed]

    return _TEXT_OCR_SPACED_TITLE_RE.sub(canonical_title, cleaned)


def _unclassified_heading_has_formal_label(title: str, label: str) -> bool:
    """Whether an ambiguous source title has a result-like label.

    A numbered or capital-letter ``Model``/``Condition`` may be a paper's
    explicitly named mathematical setup.  An ordinary prose heading such as
    ``Model generalizations`` is not.  This distinction is based only on the
    rendered source title and label, never map keys or Lean declarations.
    Proof-internal ``Case`` headings are deliberately not indexed at all: they
    are neither named source results nor named governing conditions.
    """

    if _visible_title_result_kind(title):
        return True
    normalized_title = _normalized_visible_title(title)
    if normalized_title not in (
        _UNCLASSIFIED_NAMED_TITLE_WORDS | _REVIEW_CANDIDATE_TITLE_WORDS
    ):
        return True
    normalized_label = label.strip()
    if re.fullmatch(
        r"\(\s*(?:[A-Za-z]+\.)?\d+(?:\.\d+)*\s*\)|"
        r"(?:[A-Za-z]+\.)?\d+(?:\.\d)*",
        normalized_label,
    ):
        return True
    return bool(re.fullmatch(r"[A-Z](?:\.\d+)*", normalized_label))


def _text_heading_is_sentence_continuation(line: str, match: re.Match[str]) -> bool:
    """Reject a line-broken cross-reference followed by discourse prose.

    A transcript can place ``Definition 1. Thus, ...`` at a fresh line even
    though it continues the preceding proof paragraph.  The visible discourse
    connective is source grammar; no map or Lean identifier participates.
    """

    return bool(_TEXT_REFERENCE_CONTINUATION_RE.match(line[match.end() :]))


def _text_heading_is_parallel_layout_header(
    line: str, match: re.Match[str]
) -> bool:
    """Reject two or more widely separated table-column labels on one line.

    Layout-preserving PDF extraction can render a table header such as
    ``Model A                 Model B`` at the start of a line.  The first
    column otherwise has exactly the grammar of a labelled source setup.  A
    second complete heading after a multi-space column gap is source-only
    evidence that the line is parallel table structure, not a declaration of
    the first model.  Ordinary prose such as ``Model A and Model B`` and an
    actual ``Model A: ...`` declaration do not satisfy this rule.
    """

    title = match.group("title").strip()
    if _normalized_visible_title(title) not in _UNCLASSIFIED_NAMED_TITLE_WORDS:
        return False
    suffix = line[match.end() :]
    column_gap = re.match(r"\s{2,}", suffix)
    if column_gap is None:
        return False
    parallel = _TEXT_HEADING_RE.match(suffix[column_gap.end() :])
    if parallel is None:
        return False
    parallel_title = parallel.group("title").strip()
    return (
        _normalized_visible_title(parallel_title)
        in _UNCLASSIFIED_NAMED_TITLE_WORDS
        and _unclassified_heading_has_formal_label(
            parallel_title, parallel.group("label")
        )
    )


def _text_heading_continues_prior_reference(
    lines: list[str], line_number: int
) -> bool:
    """Reject a heading-shaped line that completes unfinished reference prose."""

    if line_number <= 1:
        return False
    current_raw = _clean_text_heading_line(lines[line_number - 1])
    current_indent = len(current_raw) - len(current_raw.lstrip())
    # A layout-preserving PDF transcript can interleave the right column
    # between two consecutive left-column lines.  Look through at most two
    # such far-indented lines, but never cross a blank/source boundary.
    for offset in range(1, 4):
        prior_raw = _clean_text_heading_line(lines[line_number - 1 - offset])
        if not prior_raw.strip():
            return False
        prior_indent = len(prior_raw) - len(prior_raw.lstrip())
        if current_indent <= 16 and prior_indent >= current_indent + 24:
            continue
        prior = prior_raw.strip()
        if _SOURCE_STATEMENT_TERMINAL_RE.search(prior):
            return False
        return bool(_TEXT_PRIOR_NAMED_REFERENCE_LEAD_RE.search(prior))
    return False


def _text_two_line_section_boundary(lines: list[str], line_number: int) -> bool:
    """Recognize a decimal section number followed by a rendered title line."""

    if not _TEXT_STANDALONE_DECIMAL_SECTION_RE.match(lines[line_number - 1]):
        return False
    next_line = line_number + 1
    while next_line <= len(lines) and not lines[next_line - 1].strip():
        next_line += 1
    return (
        next_line <= len(lines)
        and _TEXT_SECTION_TITLE_LINE_RE.match(lines[next_line - 1]) is not None
    )


def _text_heading_matches(
    lines: list[str],
    heading_kinds: Mapping[str, str] | None,
    *,
    include_review_candidates: bool = False,
) -> list[tuple[int, str, str, str]]:
    configured_heading_kinds = _validated_kind_mapping(
        heading_kinds, field_name="heading_kinds"
    )
    headings: list[tuple[int, str, str, str]] = []
    for line_number, raw_line in enumerate(lines, start=1):
        cleaned = _clean_text_heading_line(raw_line)
        match = _TEXT_HEADING_RE.match(cleaned)
        if match is None:
            continue
        if _text_heading_is_sentence_continuation(cleaned, match):
            continue
        if _text_heading_is_parallel_layout_header(cleaned, match):
            continue
        if _text_heading_continues_prior_reference(lines, line_number):
            continue
        title = match.group("title").strip()
        title_key = _normalized_visible_title(title)
        visible_kind = _visible_title_result_kind(title)
        configured_kind = configured_heading_kinds.get(title_key)
        if visible_kind and configured_kind and configured_kind != visible_kind:
            raise ValueError(
                "heading_kinds cannot override unambiguous source presentation "
                f"`{title}` ({visible_kind}) as `{configured_kind}`"
            )
        candidate_kind = _review_candidate_kind(title)
        if candidate_kind and not include_review_candidates:
            if title_key not in _UNCLASSIFIED_NAMED_TITLE_WORDS:
                continue
            candidate_kind = ""
        kind = visible_kind or candidate_kind or configured_kind or UNCLASSIFIED_NAMED_PRESENTATION_KIND
        label = match.group("label").strip()
        if not _unclassified_heading_has_formal_label(title, label):
            continue
        if kind == "algorithm" and not _is_numbered_algorithm_label(label):
            continue
        headings.append((line_number, kind, label, title))
    # Layout-preserving PDF text often renders small-caps headings with a gap
    # after the first letter (``T HEOREM``, ``L EMMA``).  That visible OCR form
    # is strong source-only evidence even when a two-column transcript embeds
    # it after unrelated left-column prose.  Parse it before the ordinary
    # normalized embedded-heading rule so punctuation after the label is kept.
    for line_number, raw_line in enumerate(lines, start=1):
        for match in _TEXT_OCR_SPACED_HEADING_RE.finditer(
            _strip_tex_comment(raw_line)
        ):
            collapsed = re.sub(r"\s+", "", match.group("title")).lower()
            title = _TEXT_OCR_SPACED_TITLE_CANONICAL[collapsed]
            kind = _visible_title_result_kind(title)
            if kind is None:
                continue
            label = match.group("label").strip()
            if kind == "algorithm" and not _is_numbered_algorithm_label(label):
                continue
            headings.append((line_number, kind, label, title))
    for line_number, raw_line in enumerate(lines, start=1):
        cleaned = _clean_text_heading_line(raw_line)
        for match in _TEXT_EMBEDDED_DECIMAL_HEADING_RE.finditer(cleaned):
            # A start-of-line presentation was already handled by the strict
            # heading matcher above.  This path is only for column-interleaved
            # PDF transcripts.
            if match.start() == 0:
                continue
            title = match.group("title").strip()
            title_key = _normalized_visible_title(title)
            visible_kind = _visible_title_result_kind(title)
            configured_kind = configured_heading_kinds.get(title_key)
            if visible_kind and configured_kind and configured_kind != visible_kind:
                raise ValueError(
                    "heading_kinds cannot override unambiguous source presentation "
                    f"`{title}` ({visible_kind}) as `{configured_kind}`"
                )
            candidate_kind = _review_candidate_kind(title)
            if candidate_kind and not include_review_candidates:
                if title_key not in _UNCLASSIFIED_NAMED_TITLE_WORDS:
                    continue
                candidate_kind = ""
            kind = visible_kind or candidate_kind or configured_kind or UNCLASSIFIED_NAMED_PRESENTATION_KIND
            label = match.group("label").strip()
            if not _unclassified_heading_has_formal_label(title, label):
                continue
            if kind == "algorithm" and not _is_numbered_algorithm_label(label):
                continue
            headings.append((line_number, kind, label, title))
    # This is intentionally separate from the general heading grammar.  A
    # visible all-caps ``DEFINITION.`` block is a conventional unnumbered
    # source result; broadening the regular expression to arbitrary
    # unnumbered title words would turn ordinary prose into theorem coverage.
    for line_number, raw_line in enumerate(lines, start=1):
        cleaned = _clean_text_heading_line(raw_line)
        if _TEXT_UNNUMBERED_DEFINITION_HEADING_RE.match(cleaned) is None:
            continue
        if _text_unnumbered_definition_sentence_end(lines, line_number) is None:
            continue
        headings.append((line_number, "definition", f"@{line_number}", "definition"))
    return sorted(set(headings))


def _text_heading_column(
    raw_line: str, *, title: str, label: str
) -> int:
    """Return the visible starting column of one already-detected heading.

    The source-only heading extractor accepts both ordinary line-leading
    headings and decimal/OCR headings embedded in a second PDF-text column.
    Presentation-boundary discovery needs the same distinction: a heading in
    the other rendered column must not truncate the current presentation.
    This helper only relocates a heading that the existing grammar has already
    accepted; it does not discover or classify any new source result.
    """

    cleaned = _clean_text_heading_line(raw_line)
    normalized_title = _normalized_visible_title(title)
    candidates: list[tuple[int, str, str]] = []
    ordinary = _TEXT_HEADING_RE.match(cleaned)
    if ordinary is not None:
        candidates.append(
            (ordinary.start("title"), ordinary.group("title"), ordinary.group("label"))
        )
    for match in _TEXT_EMBEDDED_DECIMAL_HEADING_RE.finditer(cleaned):
        candidates.append((match.start("title"), match.group("title"), match.group("label")))
    for match in _TEXT_OCR_SPACED_HEADING_RE.finditer(_strip_tex_comment(raw_line)):
        collapsed = re.sub(r"\s+", "", match.group("title")).lower()
        candidates.append(
            (
                match.start("title"),
                _TEXT_OCR_SPACED_TITLE_CANONICAL.get(collapsed, match.group("title")),
                match.group("label"),
            )
        )
    for column, candidate_title, candidate_label in candidates:
        if (
            _normalized_visible_title(candidate_title) == normalized_title
            and candidate_label.strip() == label.strip()
        ):
            return column
    return len(cleaned) - len(cleaned.lstrip())


def _visible_label_column(raw_line: str, label: str) -> int | None:
    """Locate a visible result label without interpreting its semantics."""

    words = [re.escape(word) for word in label.split() if word]
    if not words:
        return None
    match = re.search(r"\s+".join(words), raw_line, re.IGNORECASE)
    return match.start() if match is not None else None


def _text_heading_boundary_is_same_column(
    lines: list[str],
    current_heading: tuple[int, str, str, str],
    boundary_headings: list[tuple[int, str, str, str]],
) -> bool:
    """Whether a later detected heading occupies the current PDF-text column."""

    current_line, _current_kind, current_label, current_title = current_heading
    current_column = _text_heading_column(
        lines[current_line - 1], title=current_title, label=current_label
    )
    # A 24-space gap is already the extractor's conservative evidence for a
    # parallel rendered column. Treat the transcript as two lanes only when
    # one heading is line-leading and the other is beyond that same gap.
    current_lane = 0 if current_column < 24 else 1
    return any(
        (0 if _text_heading_column(
            lines[line_start - 1], title=title, label=label
        ) < 24 else 1) == current_lane
        for line_start, _kind, label, title in boundary_headings
    )


def _text_unnumbered_definition_sentence_end(
    lines: list[str], line_start: int
) -> int | None:
    """Find the bounded terminal line of a visible ``DEFINITION.`` block.

    Source line anchors cannot express a character-range endpoint, so this
    recognizes only a terminal sentence ending within a short consecutive run
    of nonblank source lines.  If a scan/OCR transcript does not expose that
    boundary, no unnumbered result is manufactured from it.
    """

    limit = min(len(lines), line_start + _TEXT_UNNUMBERED_DEFINITION_MAX_LINES - 1)
    for line_number in range(line_start, limit + 1):
        candidate = _clean_text_heading_line(lines[line_number - 1])
        if line_number > line_start and not candidate.strip():
            return None
        if line_number > line_start and (
            _TEXT_HEADING_RE.match(candidate)
            or _PROOF_START_RE.match(candidate)
            or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
            or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
            or _text_two_line_section_boundary(lines, line_number)
        ):
            return None
        heading = _TEXT_UNNUMBERED_DEFINITION_HEADING_RE.match(candidate)
        # A standalone heading's period is punctuation for the visible title,
        # not the terminal punctuation of its definition sentence.
        if (
            _SOURCE_STATEMENT_TERMINAL_RE.search(candidate)
            and not (
                line_number == line_start
                and heading is not None
                and not candidate[heading.end() :].strip()
            )
        ):
            return line_number
    return None


def _text_heading_presentation_label(title: str, label: str) -> str:
    """Render a stable visible label, including unnumbered source headings."""

    if label.startswith("@"):
        return f"{title.title()}{label}"
    return f"{title.title()} {label}"


def _text_subpart_markers(
    lines: list[str],
    headings: list[tuple[int, str, str, str]],
) -> dict[int, list[tuple[int, str]]]:
    """Find visibly enumerated leaves below a named result heading.

    A paper can present one named theorem/lemma followed by several numbered
    conclusion parts.  Those leaves are independent review obligations even
    when the PDF transcript does not repeat ``Theorem`` before every part.
    Detection is source-only: it begins at an actual named heading and accepts
    only an initial sequence of at least two Roman-numeral markers before the
    next named heading or proof.  Ordinary parenthesized model notation such
    as ``(t) iid`` and equation tags such as ``(7)`` are excluded.
    """

    markers_by_heading: dict[int, list[tuple[int, str]]] = {}
    heading_starts = [line_start for line_start, _kind, _label, _title in headings]
    for heading_index, (line_start, _kind, _label, _title) in enumerate(headings):
        next_heading = (
            heading_starts[heading_index + 1]
            if heading_index + 1 < len(heading_starts)
            else len(lines) + 1
        )
        markers: list[tuple[int, str]] = []
        for line_number in range(line_start + 1, next_heading):
            candidate = _clean_text_heading_line(lines[line_number - 1])
            if _PROOF_START_RE.match(candidate) or _TEXT_PROOF_NARRATIVE_RE.match(
                candidate
            ) or _TEXT_SECTION_BOUNDARY_RE.match(candidate) or _text_two_line_section_boundary(
                lines, line_number
            ):
                break
            marker = _TEXT_SUBPART_MARKER_RE.match(candidate)
            if marker is None:
                continue
            label = marker.group("label").strip().lower()
            expected_index = len(markers)
            if (
                expected_index >= len(_ROMAN_SUBPART_LABELS)
                or label != _ROMAN_SUBPART_LABELS[expected_index]
            ):
                if markers:
                    break
                continue
            markers.append((line_number, label))
        # A single enumerated parenthetical phrase is too ambiguous to replace
        # the named parent result.  Multiple sibling markers are a visible
        # source presentation of distinct theorem/lemma parts.
        if len(markers) >= 2:
            markers_by_heading[line_start] = markers
    return markers_by_heading


def _subparts_are_explicit_conditional_antecedents(
    lines: list[str],
    *,
    heading_start: int,
    markers: list[tuple[int, str]],
) -> bool:
    """Recognize a visibly conditional result whose list supplies premises.

    Enumerated leaves normally deserve separate source obligations.  A result
    of the form ``Proposition N. Suppose/Assume ... (i) ... (ii) ... Then
    ...`` is different: the leaves are one conditional statement's
    antecedents, not independent proposition conclusions.  Retain the parent
    presentation in that case.  The test uses only the printed connective
    grammar and never source-map or Lean names.
    """

    if not markers:
        return False
    lead = " ".join(lines[heading_start - 1 : markers[0][0] - 1]).casefold()
    tail_lines: list[str] = []
    for line_number in range(
        markers[-1][0], min(len(lines) + 1, markers[-1][0] + 80)
    ):
        candidate = _clean_text_heading_line(lines[line_number - 1])
        if line_number > markers[-1][0] and (
            _TEXT_HEADING_RE.match(candidate)
            or _PROOF_START_RE.match(candidate)
            or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
            or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
            or _text_two_line_section_boundary(lines, line_number)
        ):
            break
        tail_lines.append(candidate)
    # A bare word occurrence is too weak: an independently claim-bearing
    # subpart can itself say, for example, ``if x, then y``.  Only a printed
    # statement-level `Then` line licenses treating the preceding enumerated
    # leaves as one result's antecedents.  This remains deliberately
    # conservative: an unfamiliar consequent connective leaves the parts
    # separate rather than hiding a paper-facing conclusion.
    has_statement_level_then = any(
        re.match(r"^\s*then\b", line, flags=re.IGNORECASE)
        for line in tail_lines
    )
    return bool(
        re.search(r"\b(?:suppose|assume|assuming)\b", lead)
        and has_statement_level_then
    )


def source_text_uses_conditional_antecedent_subpart_selection(
    source_text: str, *, heading_kinds: Mapping[str, str] | None = None
) -> bool:
    """Whether text exercises conditional-subpart source selection.

    This is intentionally a printed-source grammar predicate.  Callers use it
    only to attach a feature-scoped raw-surface producer identity, so a parser
    repair refreshes papers whose selected source presentation can actually
    change without invalidating unrelated current audit receipts.
    """

    lines = _source_lines(source_text)
    headings = _text_heading_matches(lines, heading_kinds)
    subparts_by_heading = _text_subpart_markers(lines, headings)
    return any(
        _subparts_are_explicit_conditional_antecedents(
            lines,
            heading_start=heading_start,
            markers=markers,
        )
        for heading_start, markers in subparts_by_heading.items()
        if markers
    )


def extract_text_named_result_presentations(
    source_text: str,
    *,
    heading_kinds: Mapping[str, str] | None = None,
    include_review_candidates: bool = False,
) -> list[NamedResultPresentation]:
    """Extract visible text/PDF-transcript heading presentations by line.

    A heading must begin its own line and use an explicit delimiter or line end
    after its label.  That intentionally excludes ordinary prose such as
    ``Theorem 2 proves ...`` from becoming a new source obligation.
    """

    lines = _source_lines(source_text)
    headings = _text_heading_matches(
        lines,
        heading_kinds,
        include_review_candidates=include_review_candidates,
    )
    starts = {line_number for line_number, _kind, _label, _title in headings}
    headings_by_line: dict[int, list[tuple[int, str, str, str]]] = {}
    for heading in headings:
        headings_by_line.setdefault(heading[0], []).append(heading)
    unnumbered_definition_ends = {
        line_start: _text_unnumbered_definition_sentence_end(lines, line_start)
        for line_start, _kind, label, _title in headings
        if label.startswith("@")
    }
    subparts_by_heading = _text_subpart_markers(lines, headings)
    presentations: list[NamedResultPresentation] = []
    for current_heading in headings:
        line_start, kind, label, title = current_heading
        unnumbered_definition_end = unnumbered_definition_ends.get(line_start)
        if unnumbered_definition_end is not None:
            presentations.append(
                NamedResultPresentation(
                    kind=kind,
                    label=_text_heading_presentation_label(title, label),
                    line_start=line_start,
                    line_end=unnumbered_definition_end,
                    presentation="text_unnumbered_definition",
                )
            )
            continue
        subparts = subparts_by_heading.get(line_start)
        if subparts and _subparts_are_explicit_conditional_antecedents(
            lines, heading_start=line_start, markers=subparts
        ):
            subparts = None
        if subparts:
            for subpart_index, (subpart_start, subpart_label) in enumerate(subparts):
                next_subpart_start = (
                    subparts[subpart_index + 1][0]
                    if subpart_index + 1 < len(subparts)
                    else len(lines) + 1
                )
                subpart_end = next_subpart_start - 1
                for line_number in range(subpart_start + 1, next_subpart_start):
                    candidate = lines[line_number - 1]
                    if (
                        (
                            line_number in starts
                            and _text_heading_boundary_is_same_column(
                                lines,
                                current_heading,
                                headings_by_line[line_number],
                            )
                        )
                        or _PROOF_START_RE.match(candidate)
                        or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
                        or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
                        or _text_two_line_section_boundary(lines, line_number)
                        or _TEXT_NONRESULT_PRESENTATION_BOUNDARY_RE.match(candidate)
                    ):
                        subpart_end = line_number - 1
                        break
                # Keep the source span complete while avoiding trailing blank
                # transcript lines that carry no part of the visible result.
                while subpart_end > subpart_start and not lines[subpart_end - 1].strip():
                    subpart_end -= 1
                presentations.append(
                    NamedResultPresentation(
                        kind=kind,
                        label=f"{_text_heading_presentation_label(title, label)}({subpart_label})",
                        line_start=subpart_start,
                        line_end=subpart_end,
                        presentation="text_heading_subpart",
                    )
                )
            continue
        line_end = line_start
        for line_number in range(line_start + 1, len(lines) + 1):
            if (
                line_number in starts
                and _text_heading_boundary_is_same_column(
                    lines,
                    current_heading,
                    headings_by_line[line_number],
                )
            ):
                break
            candidate = lines[line_number - 1]
            if (
                _PROOF_START_RE.match(candidate)
                or _TEXT_PROOF_NARRATIVE_RE.match(candidate)
                or _TEXT_SECTION_BOUNDARY_RE.match(candidate)
                or _text_two_line_section_boundary(lines, line_number)
                or _TEXT_NONRESULT_PRESENTATION_BOUNDARY_RE.match(candidate)
            ):
                break
            # PDF/transcript extraction often inserts blank lines inside a
            # displayed definition or conclusion. A blank line is not source
            # evidence that the named result has ended: retain scanning until
            # the next visible result/proof boundary, but exclude trailing
            # blank lines from the presentation's exact anchor span.
            if candidate.strip():
                line_end = line_number
        presentations.append(
            NamedResultPresentation(
                kind=kind,
                label=_text_heading_presentation_label(title, label),
                line_start=line_start,
                line_end=line_end,
                presentation="text_heading",
            )
        )
    return presentations


def _deduplicate_presentations(
    presentations: Iterable[NamedResultPresentation],
) -> list[NamedResultPresentation]:
    """Collapse text renderings nested inside the same TeX environment."""

    deduplicated: list[NamedResultPresentation] = []
    for candidate in sorted(
        presentations,
        key=lambda item: (
            item.line_start,
            0 if item.presentation == "tex_environment" else 1,
            item.line_end,
            item.kind,
            item.label,
        ),
    ):
        duplicate_index = next(
            (
                index
                for index, existing in enumerate(deduplicated)
                if existing.kind == candidate.kind
                and max(existing.line_start, candidate.line_start)
                <= min(existing.line_end, candidate.line_end)
            ),
            None,
        )
        if duplicate_index is None:
            deduplicated.append(candidate)
        elif candidate.presentation == "tex_environment":
            deduplicated[duplicate_index] = candidate
    return sorted(
        deduplicated,
        key=lambda item: (item.line_start, item.line_end, item.kind, item.label),
    )


def extract_named_result_presentations(
    source_text: str,
    *,
    source_format: str = "auto",
    environment_kinds: Mapping[str, str] | None = None,
    heading_kinds: Mapping[str, str] | None = None,
    include_review_candidates: bool = False,
) -> list[NamedResultPresentation]:
    """Extract named source results from canonical text or TeX source.

    ``source_format`` may be ``"text"``, ``"tex"``, or ``"auto"``.  TeX
    and auto mode both retain visible text headings because some TeX sources use
    manually styled headings rather than theorem environments.
    ``environment_kinds`` classifies document-class/local TeX environments;
    ``heading_kinds`` classifies visible transcript heading titles.  Both are
    declarative source-presentation mappings, never Lean aliases or map keys.
    """

    if source_format not in {"auto", "text", "tex"}:
        raise ValueError("source_format must be one of: auto, text, tex")
    if source_format == "text":
        return extract_text_named_result_presentations(
            source_text,
            heading_kinds=heading_kinds,
            include_review_candidates=include_review_candidates,
        )
    return _deduplicate_presentations(
        [
            *extract_tex_named_result_presentations(
                source_text,
                environment_kinds=environment_kinds,
                include_review_candidates=include_review_candidates,
            ),
            *extract_text_named_result_presentations(
                source_text,
                heading_kinds=heading_kinds,
                include_review_candidates=include_review_candidates,
            ),
        ]
    )


def review_candidate_presentations(
    presentations: Iterable[NamedResultPresentation],
) -> list[NamedResultPresentation]:
    """Return only labelled source headings requiring a reviewed disposition."""

    return [
        presentation
        for presentation in presentations
        if review_candidate_visible_kind(presentation.kind)
    ]


def add_holistic_review_candidate_presentations(
    presentations: Iterable[NamedResultPresentation],
    disposition_records: object,
) -> list[NamedResultPresentation]:
    """Reconstruct source-only candidates found by the holistic full-text pass."""

    current = list(presentations)
    if not isinstance(disposition_records, list):
        raise TypeError("candidate_presentations must be an explicit list")
    for record_index, raw_record in enumerate(disposition_records):
        if not isinstance(raw_record, Mapping):
            raise TypeError(f"candidate_presentations[{record_index}] must be an object")
        if raw_record.get("discovery_basis") != REVIEW_CANDIDATE_HOLISTIC_DISCOVERY:
            continue
        anchor = raw_record.get("source_anchor")
        if not isinstance(anchor, Mapping):
            raise ValueError(
                f"candidate_presentations[{record_index}].source_anchor is required"
            )
        line_start = anchor.get("line_start")
        line_end = anchor.get("line_end")
        if (
            not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or not isinstance(line_end, int)
            or isinstance(line_end, bool)
            or line_start < 1
            or line_end < line_start
        ):
            raise ValueError(
                f"candidate_presentations[{record_index}].source_anchor has an invalid line span"
            )
        presentation_label = str(
            raw_record.get("presentation_label") or ""
        ).strip()
        if not presentation_label:
            raise ValueError(
                f"candidate_presentations[{record_index}].presentation_label is required"
            )
        current.append(
            NamedResultPresentation(
                kind=REVIEW_CANDIDATE_PRESENTATION_KIND_PREFIX + "holistic",
                label=presentation_label,
                line_start=line_start,
                line_end=line_end,
                presentation=REVIEW_CANDIDATE_HOLISTIC_DISCOVERY,
            )
        )
    return sorted(
        current,
        key=lambda item: (
            item.line_start,
            item.line_end,
            item.kind,
            item.label,
            item.presentation,
        ),
    )


def classify_review_candidate_presentations(
    presentations: Iterable[NamedResultPresentation],
    disposition_records: object,
    *,
    source_text: str,
    source_path: str,
) -> list[NamedResultPresentation]:
    """Apply one exact reviewed disposition to every discovered candidate.

    Material candidates become ordinary ``claim`` presentations. Deep-only
    candidates remain present in the candidate receipt but do not enter the
    named-theory denominator. The selector is exact source path and span;
    labels, map keys, and Lean declarations never choose a candidate.
    """

    current = list(presentations)
    candidates = review_candidate_presentations(current)
    if not isinstance(disposition_records, list):
        raise ValueError("candidate_presentations must be an explicit list")
    matched_candidates: set[int] = set()
    seen_ids: set[str] = set()
    promoted: list[NamedResultPresentation] = []
    for record_index, raw_record in enumerate(disposition_records):
        label = f"candidate_presentations[{record_index}]"
        if not isinstance(raw_record, Mapping):
            raise TypeError(f"{label} must be an object")
        allowed_fields = {
            "schema",
            "id",
            "presentation_label",
            "visible_kind",
            "scope_disposition",
            "semantic_basis",
            "discovery_basis",
            "source_anchor",
        }
        unexpected = sorted(str(field) for field in raw_record if field not in allowed_fields)
        if unexpected:
            raise ValueError(
                f"{label} has unsupported field(s): " + ", ".join(unexpected)
            )
        if raw_record.get("schema") != 1 or isinstance(raw_record.get("schema"), bool):
            raise ValueError(f"{label}.schema must be 1")
        record_id = str(raw_record.get("id") or "").strip()
        if not record_id or record_id in seen_ids:
            raise ValueError(f"{label}.id must be nonempty and unique")
        seen_ids.add(record_id)
        disposition = str(raw_record.get("scope_disposition") or "").strip()
        if disposition not in REVIEW_CANDIDATE_DISPOSITIONS:
            raise ValueError(
                f"{label}.scope_disposition must be one of: "
                + ", ".join(sorted(REVIEW_CANDIDATE_DISPOSITIONS))
            )
        if not str(raw_record.get("semantic_basis") or "").strip():
            raise ValueError(f"{label}.semantic_basis is required")
        discovery_basis = str(raw_record.get("discovery_basis") or "").strip()
        if discovery_basis not in REVIEW_CANDIDATE_DISCOVERY_BASES:
            raise ValueError(
                f"{label}.discovery_basis must be one of: "
                + ", ".join(sorted(REVIEW_CANDIDATE_DISCOVERY_BASES))
            )
        anchor = raw_record.get("source_anchor")
        matches = [
            candidate_index
            for candidate_index, candidate in enumerate(candidates)
            if candidate_index not in matched_candidates
            and isinstance(anchor, Mapping)
            and source_paths_match(anchor.get("path"), source_path)
            and anchor.get("line_start") == candidate.line_start
            and anchor.get("line_end") == candidate.line_end
            and byte_pinned_anchor_covers_presentation(
                anchor,
                candidate,
                source_text=source_text,
                source_path=source_path,
            )
        ]
        if len(matches) != 1:
            raise ValueError(
                f"{label}.source_anchor must identify exactly one current review candidate"
            )
        candidate_index = matches[0]
        candidate = candidates[candidate_index]
        if raw_record.get("presentation_label") != candidate.label:
            raise ValueError(f"{label}.presentation_label is stale")
        if raw_record.get("visible_kind") != review_candidate_visible_kind(
            candidate.kind
        ):
            raise ValueError(f"{label}.visible_kind is stale")
        matched_candidates.add(candidate_index)
        if disposition == REVIEW_CANDIDATE_NORMAL_DISPOSITION:
            promoted.append(
                NamedResultPresentation(
                    kind="claim",
                    label=candidate.label,
                    line_start=candidate.line_start,
                    line_end=candidate.line_end,
                    presentation=candidate.presentation,
                )
            )
    if len(matched_candidates) != len(candidates):
        missing = ", ".join(
            f"{candidate.label}@{candidate.line_start}-{candidate.line_end}"
            for candidate_index, candidate in enumerate(candidates)
            if candidate_index not in matched_candidates
        )
        raise ValueError(
            "source inventory leaves review candidate(s) without a disposition: "
            + missing
        )
    ordinary = [
        presentation
        for presentation in current
        if not review_candidate_visible_kind(presentation.kind)
    ]
    return sorted(
        [*ordinary, *promoted],
        key=lambda item: (
            item.line_start,
            item.line_end,
            item.kind,
            item.label,
            item.presentation,
        ),
    )


def review_candidate_presentations_sha256(
    presentations: Iterable[NamedResultPresentation],
) -> str:
    """Return a source-only identity for all discovered review candidates."""

    return named_result_presentations_sha256(
        review_candidate_presentations(presentations)
    )


def classify_source_presentation_inventory(
    presentations: Iterable[NamedResultPresentation],
    *,
    source_text: str,
    source_path: str,
    candidate_dispositions: object | None,
) -> ReviewedSourcePresentationInventory:
    """Apply the one candidate ledger to an already discovered source surface."""

    discovered = tuple(presentations)
    if candidate_dispositions is None:
        return ReviewedSourcePresentationInventory(
            discovered=discovered,
            candidates=(),
            classified=discovered,
        )
    augmented = add_holistic_review_candidate_presentations(
        discovered,
        candidate_dispositions,
    )
    classified = classify_review_candidate_presentations(
        augmented,
        candidate_dispositions,
        source_text=source_text,
        source_path=source_path,
    )
    return ReviewedSourcePresentationInventory(
        discovered=tuple(augmented),
        candidates=tuple(review_candidate_presentations(augmented)),
        classified=tuple(classified),
    )


def reviewed_source_presentation_inventory(
    source_text: str,
    *,
    source_path: str,
    source_format: str = "auto",
    environment_kinds: Mapping[str, str] | None = None,
    heading_kinds: Mapping[str, str] | None = None,
    candidate_dispositions: object | None = None,
) -> ReviewedSourcePresentationInventory:
    """Build the one classified source presentation set used by all consumers.

    A missing candidate ledger preserves the recorded legacy parser surface.
    An explicit ledger, including an empty list, activates labelled-candidate
    discovery and any exact source spans added by the holistic full-text pass.
    """

    discovered = extract_named_result_presentations(
        source_text,
        source_format=source_format,
        environment_kinds=environment_kinds,
        heading_kinds=heading_kinds,
        include_review_candidates=candidate_dispositions is not None,
    )
    return classify_source_presentation_inventory(
        discovered,
        source_text=source_text,
        source_path=source_path,
        candidate_dispositions=candidate_dispositions,
    )


def source_line_spans(source_location: object) -> tuple[SourceLineSpan, ...]:
    """Parse concrete ``path:start[-end]`` spans from source metadata."""

    if not isinstance(source_location, str):
        return ()
    spans: list[SourceLineSpan] = []
    for match in _SOURCE_LOCATION_RE.finditer(source_location):
        line_start = int(match.group("start"))
        line_end = int(match.group("end") or line_start)
        if line_end < line_start:
            continue
        spans.append(
            SourceLineSpan(
                path=match.group("path").strip(),
                line_start=line_start,
                line_end=line_end,
            )
        )
    return tuple(spans)


def _normalized_path(path: str) -> str:
    return posixpath.normpath(path.replace("\\", "/").strip()).lstrip("./")


def source_paths_match(declared_path: object, source_path: object) -> bool:
    """Compare canonical paths, including the paper-local anchor convention.

    A paper's canonical source artifact may be repository-relative, for
    example ``papers/Example/source.txt``, while its row-level byte-pinned
    anchors conventionally name the same file relative to that paper,
    ``source.txt``.  That one conversion is safe because this function is
    called only after the enclosing paper has selected its one pinned source.
    It is not a general basename fallback: paths in any other directory remain
    distinct.
    """

    declared = _normalized_path(str(declared_path or ""))
    expected = _normalized_path(str(source_path or ""))
    if not declared or not expected:
        return False
    if declared == expected:
        return True
    expected_parts = expected.split("/")
    return (
        len(expected_parts) >= 3
        and expected_parts[0] == "papers"
        and declared == "/".join(expected_parts[2:])
    )


def _span_contains_presentation(
    line_start: int, line_end: int, presentation: NamedResultPresentation
) -> bool:
    return line_start <= presentation.line_start and presentation.line_end <= line_end


def source_location_covers_presentation(
    source_location: object,
    presentation: NamedResultPresentation,
    *,
    source_path: str = "",
) -> bool:
    """Return whether a concrete source-location range contains the result.

    A heading-only range is not enough to certify the statement below it: the
    source location must cover the complete discovered presentation span.
    """

    return any(
        source_paths_match(span.path, source_path)
        and _span_contains_presentation(span.line_start, span.line_end, presentation)
        for span in source_line_spans(source_location)
    )


def _byte_pinned_anchor_line_span(
    anchor: object,
    *,
    source_text: str,
    source_path: str = "",
) -> tuple[int, int] | None:
    """Return an exact current anchor's inclusive source span, if valid."""

    if not isinstance(anchor, Mapping):
        return None
    line_start = anchor.get("line_start")
    line_end = anchor.get("line_end")
    anchor_path = anchor.get("path")
    quote = anchor.get("quoted_text")
    quote_digest = anchor.get("quoted_text_sha256")
    if (
        not isinstance(anchor_path, str)
        or not anchor_path.strip()
        or not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
        or line_start < 1
        or line_end < line_start
        or not isinstance(quote, str)
        or not quote
        or not isinstance(quote_digest, str)
        or not _SHA256_RE.fullmatch(quote_digest.strip())
        or not source_paths_match(anchor_path, source_path)
    ):
        return None
    normalized_quote = _normalized_source_text(quote)
    if (
        hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
        != quote_digest.strip().lower()
    ):
        return None
    lines = _source_lines(source_text)
    if line_end > len(lines):
        return None
    if normalized_quote != "\n".join(lines[line_start - 1 : line_end]):
        return None
    return line_start, line_end


def byte_pinned_anchor_covers_presentation(
    anchor: object,
    presentation: NamedResultPresentation,
    *,
    source_text: str,
    source_path: str = "",
) -> bool:
    """Validate one exact source quote and test whether it contains a result.

    The required shape matches the repository's source-anchor contract:
    ``path``, integer line bounds, ``quoted_text``, and the SHA-256 of that
    normalized quote.  The quote must equal the exact canonical source line
    slice, and it must span the whole discovered presentation. A source-map
    item therefore cannot claim coverage merely by quoting a heading or one
    convenient line of a longer source statement.
    """

    span = _byte_pinned_anchor_line_span(
        anchor, source_text=source_text, source_path=source_path
    )
    return span is not None and _span_contains_presentation(*span, presentation)


def _single_line_heading_has_complete_statement(
    line: str,
    *,
    kind: str,
    label: str,
) -> bool:
    """Recognize a complete statement printed beside its visible heading.

    This is deliberately narrower than general source extraction.  It accepts
    only an ordinary start-of-line heading whose independently visible kind
    and label match the reconciliation record.  Text after the heading must
    contain more than punctuation or a parenthesized subtitle, and the line
    must end at a source-statement terminal.  A following visible continuation
    is checked separately by the caller.
    """

    cleaned = _clean_text_heading_line(line)
    match = _TEXT_HEADING_RE.match(cleaned)
    if match is None:
        return False
    title = match.group("title").strip()
    visible_kind = _visible_title_result_kind(title)
    visible_label = _text_heading_presentation_label(
        title, match.group("label").strip()
    )
    if visible_kind != kind or visible_label != label:
        return False
    tail = _SOURCE_HEADING_SEPARATOR_RE.sub("", cleaned[match.end() :], count=1)
    if not tail.strip() or _SOURCE_PARENTHETICAL_TITLE_ONLY_RE.fullmatch(tail.strip()):
        return False
    return _SOURCE_STATEMENT_TERMINAL_RE.search(cleaned) is not None


def source_presentation_reconciliation_errors(
    item: object,
    presentations: Iterable[NamedResultPresentation],
    *,
    source_text: str,
    source_path: str = "",
) -> tuple[str, ...]:
    """Validate an optional source-only core for a conservative text span.

    Text/PDF extraction deliberately makes a heading's span conservative when
    it cannot establish where a displayed statement ends.  This opt-in record
    permits a curator to pin a shorter complete statement core, but only when
    the core starts at an independently extracted visible heading, has the
    same visible kind and label, and contains either a complete same-line
    statement or at least one nonblank continuation line.  The core itself is
    independently byte-pinned against the source inventory text, so it may
    differ from the item's semantic-review anchor when a damaged PDF extraction
    requires a separately authenticated visual transcription. A
    ``complete_indexed_presentation`` instead pins the exact complete span
    selected by the independent source index when a displayed formula or
    structured layout has no sentence-terminal line. A two-column transcript may place
    a second independently indexed presentation inside that line span.  The
    reconciliation remains exclusive to its declared presentation, while the
    ordinary coverage gate still requires the interleaved presentation to be
    matched independently.  It never reads an item key, map summary, or Lean
    route.
    """

    if not isinstance(item, Mapping):
        return ()
    relation = item.get(SOURCE_PRESENTATION_RECONCILIATION_FIELD)
    if relation is None:
        return ()
    errors: list[str] = []
    if not isinstance(relation, Mapping):
        return (f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD} must be an object",)
    allowed_fields = {
        "schema",
        "relation",
        "presentation_kind",
        "presentation_label",
        SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD,
        "boundary_reason",
        "semantic_basis",
        "validator",
        "validated_at",
    }
    unexpected = sorted(str(key) for key in relation if str(key) not in allowed_fields)
    if unexpected:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if relation.get("schema") != SOURCE_PRESENTATION_RECONCILIATION_SCHEMA:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.schema must be "
            f"{SOURCE_PRESENTATION_RECONCILIATION_SCHEMA}"
        )
    if relation.get("relation") != SOURCE_PRESENTATION_RECONCILIATION_RELATION:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.relation must be "
            f"`{SOURCE_PRESENTATION_RECONCILIATION_RELATION}`"
        )
    boundary_reason = relation.get("boundary_reason")
    if (
        not isinstance(boundary_reason, str)
        or boundary_reason not in SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS
    ):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.boundary_reason must be one of: "
            + ", ".join(sorted(SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS))
        )
    kind = relation.get("presentation_kind")
    label = relation.get("presentation_label")
    if not isinstance(kind, str) or not kind.strip():
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.presentation_kind is required"
        )
    if not isinstance(label, str) or not label.strip():
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.presentation_label is required"
        )
    for field in ("semantic_basis", "validator"):
        value = relation.get(field)
        if not isinstance(value, str) or not value.strip():
            errors.append(f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.{field} is required")
    validated_at = str(relation.get("validated_at") or "").strip()
    if not _ISO_LIKE_UTC_TIMESTAMP_RE.fullmatch(validated_at):
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.validated_at must be an ISO-like UTC timestamp"
        )

    core_anchor = relation.get(SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD)
    core_span = _byte_pinned_anchor_line_span(
        core_anchor, source_text=source_text, source_path=source_path
    )
    if core_span is None:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must be an exact current source anchor"
        )
        return tuple(errors)
    core_start, core_end = core_span
    lines = _source_lines(source_text)
    current_presentations = tuple(presentations)
    candidates = [
        presentation
        for presentation in current_presentations
        if presentation.line_start == core_start
        and presentation.kind == str(kind or "").strip()
        and presentation.label == str(label or "").strip()
    ]
    candidate: NamedResultPresentation | None = None
    if len(candidates) != 1:
        errors.append(
            f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must begin at exactly one independently extracted presentation with the declared kind and label"
        )
    else:
        candidate = candidates[0]
        if core_end > candidate.line_end:
            errors.append(
                f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must remain inside the independently extracted presentation span"
            )
        if boundary_reason == "interleaved_parallel_columns":
            candidate_column = _visible_label_column(
                lines[candidate.line_start - 1], candidate.label
            )
            overlapping_other_column = any(
                other is not candidate
                and max(candidate.line_start, other.line_start)
                <= min(candidate.line_end, other.line_end)
                and candidate_column is not None
                and (
                    other_column := _visible_label_column(
                        lines[other.line_start - 1], other.label
                    )
                )
                is not None
                and (candidate_column < 24) != (other_column < 24)
                for other in current_presentations
            )
            if (core_start, core_end) != (
                candidate.line_start,
                candidate.line_end,
            ):
                errors.append(
                    f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must equal the complete conservative presentation span for interleaved parallel columns"
                )
            if not overlapping_other_column:
                errors.append(
                    f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.interleaved_parallel_columns requires an independently extracted overlapping presentation in the other visible text column"
                )

    if boundary_reason == "complete_indexed_presentation":
        if candidate is None or (core_start, core_end) != (
            candidate.line_start,
            candidate.line_end,
        ):
            errors.append(
                f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.complete_indexed_presentation "
                "must equal the complete independently extracted presentation span"
            )
    elif boundary_reason == "completed_statement_then_explanation":
        same_line_complete = (
            core_end == core_start
            and isinstance(kind, str)
            and isinstance(label, str)
            and _single_line_heading_has_complete_statement(
                lines[core_start - 1], kind=kind.strip(), label=label.strip()
            )
        )
        if (
            core_end < core_start
            or (
                not same_line_complete
                and not any(line.strip() for line in lines[core_start:core_end])
            )
        ):
            errors.append(
                f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must include a complete same-line statement or a nonblank continuation beyond the heading line"
            )
        elif not _SOURCE_STATEMENT_TERMINAL_RE.search(lines[core_end - 1]):
            errors.append(
                f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor must end at a complete source-statement terminal"
            )
        elif (
            core_end < len(lines)
            and _SOURCE_STATEMENT_CONTINUATION_RE.match(lines[core_end])
        ):
            errors.append(
                f"{SOURCE_PRESENTATION_RECONCILIATION_FIELD}.core_anchor stops before a visible statement continuation"
            )
    return tuple(errors)


def source_presentation_reconciliation_covers_presentation(
    item: object,
    presentation: NamedResultPresentation,
    presentations: Iterable[NamedResultPresentation],
    *,
    source_text: str,
    source_path: str = "",
) -> bool:
    """Whether a valid curated source core is this visible presentation."""

    if not isinstance(item, Mapping) or item.get(
        SOURCE_PRESENTATION_RECONCILIATION_FIELD
    ) is None:
        return False
    if source_presentation_reconciliation_errors(
        item,
        presentations,
        source_text=source_text,
        source_path=source_path,
    ):
        return False
    relation = item[SOURCE_PRESENTATION_RECONCILIATION_FIELD]
    assert isinstance(relation, Mapping)
    core_anchor = relation[SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD]
    core_span = _byte_pinned_anchor_line_span(
        core_anchor, source_text=source_text, source_path=source_path
    )
    assert core_span is not None
    return (
        presentation.kind == relation["presentation_kind"].strip()
        and presentation.label == relation["presentation_label"].strip()
        and presentation.line_start == core_span[0]
    )


def map_item_coverage_match(
    item: object,
    presentation: NamedResultPresentation,
    *,
    source_text: str,
    source_path: str = "",
    presentations: Iterable[NamedResultPresentation] | None = None,
) -> tuple[str, ...]:
    """Return source-only evidence fields by which one map item covers a result."""

    if not isinstance(item, Mapping):
        return ()
    # A dedicated statement-core reconciliation is intentionally exclusive.
    # Its purpose is to keep a broad context/proof anchor from being mistaken
    # for every named heading it happens to contain.  Maps without that opt-in
    # record retain the established exact-full-span behavior below.
    if item.get(SOURCE_PRESENTATION_RECONCILIATION_FIELD) is not None:
        if presentations is None:
            return ()
        return (
            (SOURCE_PRESENTATION_RECONCILIATION_FIELD,)
            if source_presentation_reconciliation_covers_presentation(
                item,
                presentation,
                presentations,
                source_text=source_text,
                source_path=source_path,
            )
            else ()
        )
    evidence: list[str] = []
    if source_location_covers_presentation(
        item.get("source_location"), presentation, source_path=source_path
    ):
        evidence.append("source_location")
    anchors = item.get("source_anchor_evidence")
    if isinstance(anchors, list):
        for index, anchor in enumerate(anchors):
            if byte_pinned_anchor_covers_presentation(
                anchor,
                presentation,
                source_text=source_text,
                source_path=source_path,
            ):
                evidence.append(f"source_anchor_evidence[{index}]")
    return tuple(evidence)


def reconcile_named_result_presentations(
    presentations: Iterable[NamedResultPresentation],
    source_items: object,
    *,
    source_text: str,
    source_path: str = "",
) -> list[NamedResultReconciliation]:
    """Match discovered source presentations to opaque source-map items.

    Map object keys are retained only as report identifiers.  Matching uses no
    key, alias, title, source kind, or Lean-route spelling: it is determined
    solely by source path, source line span, and exact source-anchor evidence.
    """

    items = source_items if isinstance(source_items, Mapping) else {}
    current_presentations = tuple(presentations)
    reconciliations: list[NamedResultReconciliation] = []
    for presentation in current_presentations:
        matches: list[NamedResultCoverageMatch] = []
        for raw_item_id, item in items.items():
            evidence = map_item_coverage_match(
                item,
                presentation,
                source_text=source_text,
                source_path=source_path,
                presentations=current_presentations,
            )
            if evidence:
                matches.append(
                    NamedResultCoverageMatch(
                        item_id=str(raw_item_id), evidence=evidence
                    )
                )
        reconciliations.append(
            NamedResultReconciliation(
                presentation=presentation,
                matches=tuple(sorted(matches, key=lambda match: match.item_id)),
            )
        )
    return reconciliations


def uncovered_named_result_presentations(
    reconciliations: Iterable[NamedResultReconciliation],
) -> list[NamedResultPresentation]:
    """Return discovered presentations that have no source-only map evidence."""

    return [
        reconciliation.presentation
        for reconciliation in reconciliations
        if not reconciliation.covered
    ]


def named_result_presentations_sha256(
    presentations: Iterable[NamedResultPresentation],
) -> str:
    """Return a stable source-only receipt for a discovered presentation set.

    This is deliberately derived from visible source spans and labels, never
    from source-map keys, source kinds, Lean names, or audit routes.  A
    closeout attestation records this receipt alongside the pinned source
    artifact so a stale manual inventory cannot silently survive a source-text
    change.
    """

    payload = [
        {
            "kind": presentation.kind,
            "label": presentation.label,
            "line_start": presentation.line_start,
            "line_end": presentation.line_end,
            "presentation": presentation.presentation,
        }
        for presentation in sorted(
            presentations,
            key=lambda item: (
                item.line_start,
                item.line_end,
                item.kind,
                item.label,
                item.presentation,
            ),
        )
    ]
    encoded = json.dumps(
        payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


__all__ = [
    "NAMED_RESULT_KINDS",
    "OPEN_NAMED_PRESENTATION_KIND",
    "REVIEW_CANDIDATE_DISCOVERY_BASES",
    "REVIEW_CANDIDATE_DEEP_DISPOSITION",
    "REVIEW_CANDIDATE_DISPOSITIONS",
    "REVIEW_CANDIDATE_HOLISTIC_DISCOVERY",
    "REVIEW_CANDIDATE_MECHANICAL_DISCOVERY",
    "REVIEW_CANDIDATE_NORMAL_DISPOSITION",
    "REVIEW_CANDIDATE_PRESENTATION_KIND_PREFIX",
    "SOURCE_PRESENTATION_RECONCILIATION_BOUNDARY_REASONS",
    "SOURCE_PRESENTATION_RECONCILIATION_CORE_ANCHOR_FIELD",
    "SOURCE_PRESENTATION_RECONCILIATION_FIELD",
    "SOURCE_PRESENTATION_RECONCILIATION_RELATION",
    "SOURCE_PRESENTATION_RECONCILIATION_SCHEMA",
    "UNCLASSIFIED_NAMED_PRESENTATION_KIND",
    "NamedResultCoverageMatch",
    "NamedResultPresentation",
    "NamedResultReconciliation",
    "ReviewedSourcePresentationInventory",
    "SourceLineSpan",
    "byte_pinned_anchor_covers_presentation",
    "add_holistic_review_candidate_presentations",
    "classify_review_candidate_presentations",
    "classify_source_presentation_inventory",
    "extract_named_result_presentations",
    "extract_tex_named_result_presentations",
    "extract_text_named_result_presentations",
    "map_item_coverage_match",
    "named_result_presentations_sha256",
    "reconcile_named_result_presentations",
    "review_candidate_presentations",
    "review_candidate_presentations_sha256",
    "review_candidate_visible_kind",
    "reviewed_source_presentation_inventory",
    "source_presentation_reconciliation_covers_presentation",
    "source_presentation_reconciliation_errors",
    "source_line_spans",
    "source_location_covers_presentation",
    "source_paths_match",
    "uncovered_named_result_presentations",
]
