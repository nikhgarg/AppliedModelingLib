"""Source-only classification of claims that require Lean proof evidence.

This module is deliberately independent of dashboard rendering, filesystem I/O,
and Lean discovery.  It consumes only a statement-map item's source-facing
fields and structured route role.  Both the accepting evidence gate and the
human dashboard use this one policy, so presentation code cannot become an
implicit semantic dependency of closeout.
"""

from __future__ import annotations

import hashlib
import re
from pathlib import Path
from typing import Any

from scripts.semantic_obligation_review import (
    EXACT_SOURCE_LOCATOR_RE,
    NAME_ONLY_SOURCE_COVERAGE_REASON_RE,
)
from scripts.source_coverage_scope import (
    SOURCE_VOCABULARY_KINDS,
    THEOREM_REALIZATION_SOURCE_KINDS,
    USER_APPROVED_SCOPE_EXCLUSION_KEY,
    source_item_effective_route_policy,
)


PAPER_STATEMENT_MAP_FILE = "audit/paper_statement_map.json"
SOURCE_RESULT_KINDS = frozenset(THEOREM_REALIZATION_SOURCE_KINDS - {"example"})

SOURCE_NAMED_CLAIM_RE = re.compile(
    r"""
    (?ix)
    (?:
        \\begin\s*\{\s*(?:theorem|lemma|proposition|corollary|claim|thm|lem|prop|cor)\*?\s*\}
      | \\(?:auto|[cC]|eq)?ref\s*\{\s*(?:(?:thm|theorem|lem|lemma|prop|proposition|cor|corollary|claim)[^}]*)\}
      | \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \\label\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)

SOURCE_NAMED_RESULT_PRESENTATION_RE = re.compile(
    r"""
    (?imx)
    (?:
        \\begin\s*\{\s*(?:theorem|lemma|proposition|corollary|claim|thm|lem|prop|cor)\*?\s*\}
      | ^\s*(?:\\(?:textbf|emph|textit|paragraph)\s*\{?\s*)?
        \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \\label\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
      | \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
        (?:(?![.!?;\n]).){0,80}?\b(?:states?|proves?|establishes?|shows?|asserts?|claims?|guarantees?)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)

SOURCE_COMPLEXITY_TERMINOLOGY_RE = re.compile(
    r"\b(?:"
    r"run(?:ning)?\s+time|runtime|time\s+complexity|space\s+complexity|"
    r"strongly\s+polynomial|polytime|polynomial[-\s]?(?:query|queries)|"
    r"fixed[-\s]?parameter[-\s]?tractable|fpt|"
    r"(?:polynomial|linear|quadratic|exponential)\s*(?:[-\s]+)"
    r"(?:time|runtime|space|work|steps?|operations?|queries|iterations?)|"
    r"(?:number|count)\s+of\s+(?:arithmetic\s+)?"
    r"(?:steps?|operations?|queries|iterations?)"
    r")\b",
    re.IGNORECASE,
)
SOURCE_BIG_O_COMPLEXITY_RE = re.compile(
    r"""
    (?ix)
    (?:
        (?<![A-Za-z])(?:O|o|Ω|Θ)\s*(?:\\!\s*)?(?:\\left\s*)?\(
      | \\(?:mathcal|mathrm|operatorname)\s*\{\s*(?:O|o|Omega|Theta|Ω|Θ)\s*\}
        \s*(?:\\!\s*)?(?:\\left\s*)?\(
      | \\(?:mathcal|mathrm)\s+(?:O|o|Omega|Theta|Ω|Θ)
        \s*(?:\\!\s*)?(?:\\left\s*)?\(
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_ALGORITHM_BEHAVIOR_RE = re.compile(
    r"""
    (?ix)
    \b(?:algorithm|procedure|method)\b
    (?:(?![.!?;\n]).){0,120}?
    \b(?:
        runs?|executes?|takes?|terminates?|halts?|outputs?|produces?|returns?|
        computes?|finds?|achieves?|guarantees?
    )\b
    | \b(?:algorithm|procedure|method)\b(?:(?![.!?;\n]).){0,120}?
      \bis\s+(?:correct|optimal)\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_GENERAL_OUTPUT_GUARANTEE_RE = re.compile(
    r"""
    (?ix)
    \b(?:outputs?|produces?|returns?|computes?|finds?|terminates?|halts?)\b
    (?:(?![.!?;\n]).){0,120}?
    \b(?:for|on)\s+(?:every|all|each|any)\s+(?:input|instance|case|problem)\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_RESOURCE_BOUND_RE = re.compile(
    r"""
    (?ix)
    \b(?:takes?|requires?|uses?|needs?)\b
    (?:(?![.!?;\n]).){0,100}?
    \b(?:time|steps?|operations?|queries|iterations?)\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_CONTEXTUAL_EFFICIENCY_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:computationally|algorithmically)\s+(?:efficient|tractable|scalable|fast)\b
      | \b(?:efficient|tractable|scalable|fast)\s+(?:algorithm|procedure|method|implementation)\b
      | \b(?:algorithm|procedure|method)\b(?:(?![.!?;\n]).){0,80}?
        \b(?:efficient|tractable|scalable|fast)\b
      | \b(?:computed|solved|implemented|tested|evaluated|verified)\s+efficiently\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_GENERAL_RESULT_ASSERTION_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:if|when|whenever|provided\s+that|assuming)\b
        (?:(?![.!?;\n]).){0,160}?
        \b(?:then|holds?|implies?|is|are|remains?|becomes?)\b
      | \b(?:for|on)\s+(?:all|every|each|any)\s+
        (?:admissible\s+)?
        (?:input|instance|case|problem|profile|parameter(?:\s+value)?|model|distribution)\b
      | \b(?:always|never|universally|in\s+general|for\s+arbitrary)\b
      | \b(?:there\s+(?:is|are|exists?)|exists?|existence)\b
      | \b(?:correct(?:ness)?|strategy[-\s]?proof(?:ness)?|truthful(?:ness)?|sound(?:ness)?|complete(?:ness)?|incentive[-\s]?compatib(?:le|ility)|condorcet[-\s]?consisten(?:t|cy)|monotonicity|anonymity|proportionality)\b
      | \b(?:optimality|pareto[-\s]?optimal|globally\s+optimal|maximi[sz](?:e|es|ing)|minimi[sz](?:e|es|ing))\b
      | \b(?:approximation|competitive)\s+ratio\b|\bbounded\s+regret\b
      | \b(?:guarantees?|ensures?|certifies?|elects?)\b
        (?:(?![.!?;\n]).){0,100}?
        \b(?:winner|outcome|allocation|matching)\b
      | \b(?:rule|mechanism|method|approach|procedure|algorithm|solution)\b
        (?:(?![.!?;\n]).){0,80}?
        \b(?:satisfies|meets|obeys)\b
      | \b(?:algorithm|procedure|method|mechanism|approach|implementation|solution)\b
        (?:(?![.!?;\n]).){0,80}?
        \b(?:is|are|remains?|becomes?|achieves?|attains?|guarantees?|provides?|yields?|has|have)\b
        (?:(?![.!?;\n]).){0,80}?
        \b(?:correct|optimal|efficient|accurate|tractable|scalable|fast|performance|approximation|competitive)\b
      | \b(?:is|are|remains?|becomes?)\b
        (?:(?![.!?;\n]).){0,40}?
        \b(?:correct|optimal|efficient|accurate|tractable|scalable|fast|strategyproof)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)

SOURCE_NAMED_ALGORITHM_BLOCK_RE = re.compile(
    r"""
    (?ix)
    (?:
        \\begin\s*\{\s*(?:algorithm|algorithmic|procedure|method)\*?\s*\}
      | \\caption\s*\{[^}]*\b(?:algorithm|procedure|method)\b
      | \b(?:algorithm|procedure|method)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \d+(?:\.\d+)*(?:[a-z])?
          | (?-i:[A-Z])[A-Za-z0-9_.-]*
          | :
        )
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)
SOURCE_FINITE_OBSERVATION_CONCRETE_CUE_RE = re.compile(
    r"""
    (?ix)
    \b(?:
        simulation|simulated|benchmark|experiment(?:al)?|numerical|
        comput(?:ation|ational|ed|ing)|calibration|empirical|data\s*set|
        sample|observation|measurement|estimate
    )\b
    | \b(?:n|k|m)\s*=\s*\d+\b
    | \b\d+\s*[- ]?(?:candidate|firm|voter|agent|instance|setting|parameter)s?\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_FINITE_OBSERVATION_REPORT_RE = re.compile(
    r"""
    (?ix)
    \b(?:
        reports?|depicts?|plots?|illustrates?|shows?|observes?|finds?|records?|
        displays?|outputs?|estimates?|computes?|calculates?|verif(?:y|ies|ied)
    )\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_ARTIFACT_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
SOURCE_FILE_LINE_ANCHOR_RE = re.compile(
    r"(?P<path>(?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\.(?:tex|txt|md|pdf)):"
    r"(?P<start>[1-9]\d*)(?:-(?P<end>[1-9]\d*))?",
    re.IGNORECASE,
)
SOURCE_CATALOGUED_NONFORMAL_OBSERVATION_KINDS = frozenset({"example", "remark"})
NON_NAMED_COMPUTATIONAL_ILLUSTRATION = "non_named_computational_illustration"
SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION = (
    "source_declared_open_nonresult_observation"
)
SOURCE_DECLARED_OPEN_NONRESULT_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:remains?|is)\s+(?:an\s+)?open\s+(?:question|problem|issue|case)\b
      | \b(?:we|the\s+(?:paper|work|article))\s+(?:leave|do\s+not\s+(?:resolve|settle|know))
        (?:(?![.!?;\n]).){0,120}?\bopen\b
      | \b(?:open\s+(?:question|problem|issue)|future\s+work)\b
      | \bc\s*onjecture\b
      | \b(?:it\s+is\s+not\s+known|remains?\s+unresolved)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_POSITIVE_RESULT_PRESENTATION_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:we|this\s+(?:paper|work|article)|our\s+(?:main\s+)?(?:result|analysis))\b
        (?:(?![.!?;\n]).){0,100}?
        \b(?:prove|show|establish|demonstrate|derive|obtain|give|provide|guarantee|ensure)\b
      | \b(?:theorem|lemma|proposition|corollary|claim)\b
        (?:(?![.!?;\n]).){0,100}?
        \b(?:proves?|shows?|establishes?|demonstrates?|guarantees?|asserts?)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_SCOPE_CLASSIFICATIONS = frozenset(
    {
        NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
        SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION,
    }
)
# Compatibility export for existing claim-policy, manifest, evidence, and
# dashboard callers.  The lightweight source-coverage owner defines the one
# canonical field spelling so scope selection never imports this heavier
# semantic policy module merely to read a key.
USER_APPROVED_SCOPE_EXCLUSION = USER_APPROVED_SCOPE_EXCLUSION_KEY
USER_APPROVED_SCOPE_EXCLUSION_SCHEMA = 1
USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND = "explicit_user_instruction"
USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}(?:[T ][0-2]\d:[0-5]\d(?::[0-5]\d(?:\.\d+)?)?(?:Z|[+-][0-2]\d:[0-5]\d)?)?$"
)


def source_inventory_core_text(item: dict[str, Any]) -> str:
    """Return source assertion text without curator-only routing metadata."""

    fields = (item.get("title"), item.get("statement"), item.get("source_location"))
    return "\n".join(
        str(field or "") for field in fields if str(field or "").strip()
    )


def source_inventory_search_text(item: dict[str, Any]) -> str:
    """Return literal source-facing text; keys and Lean names never participate."""

    fields = (
        item.get("title"),
        item.get("statement"),
        item.get("source_location"),
        item.get("source_evidence"),
        item.get("source_note"),
    )
    return " ".join(str(field or "") for field in fields)


def source_text_has_general_computational_claim(text: str) -> bool:
    """Return whether source prose asserts general computational behavior."""

    return bool(
        SOURCE_COMPLEXITY_TERMINOLOGY_RE.search(text)
        or SOURCE_BIG_O_COMPLEXITY_RE.search(text)
        or SOURCE_ALGORITHM_BEHAVIOR_RE.search(text)
        or SOURCE_GENERAL_OUTPUT_GUARANTEE_RE.search(text)
        or SOURCE_RESOURCE_BOUND_RE.search(text)
        or SOURCE_CONTEXTUAL_EFFICIENCY_RE.search(text)
    )


def source_text_has_general_result_assertion(text: str) -> bool:
    """Return whether ordinary source prose makes a general result claim."""

    return bool(SOURCE_GENERAL_RESULT_ASSERTION_RE.search(text))


def source_inventory_item_is_named_claim(item: dict[str, Any]) -> bool:
    """Return whether source-facing text contains a named formal claim/reference."""

    return bool(SOURCE_NAMED_CLAIM_RE.search(source_inventory_search_text(item)))


def source_inventory_item_is_named_result_presentation(item: dict[str, Any]) -> bool:
    """Return whether the anchored source assertion itself presents a result."""

    return bool(SOURCE_NAMED_RESULT_PRESENTATION_RE.search(source_inventory_core_text(item)))


def source_text_has_finite_computational_observation(text: str) -> bool:
    """Return whether one source sentence presents a finite observed result."""

    sentences = re.split(r"[.!?;]+", text.replace("\n", " "))
    return any(
        SOURCE_FINITE_OBSERVATION_CONCRETE_CUE_RE.search(sentence)
        and SOURCE_FINITE_OBSERVATION_REPORT_RE.search(sentence)
        for sentence in sentences
    )


def source_inventory_item_is_named_algorithm_block(item: dict[str, Any]) -> bool:
    """Return whether source text identifies an Algorithm/Procedure/Method block."""

    if str(item.get("source_kind") or "").strip().lower() == "algorithm":
        return True
    return bool(SOURCE_NAMED_ALGORITHM_BLOCK_RE.search(source_inventory_core_text(item)))


def source_anchor_paths_match(left: str, right: str) -> bool:
    """Return whether two source anchors name the same relative file path."""

    normalized_left = left.replace("\\", "/").lstrip("./")
    normalized_right = right.replace("\\", "/").lstrip("./")
    return (
        normalized_left == normalized_right
        or normalized_left.endswith("/" + normalized_right)
        or normalized_right.endswith("/" + normalized_left)
    )


def source_inventory_anchor_quote_text(item: dict[str, Any]) -> tuple[str, str]:
    """Return self-hashed quotes tied one-to-one to declared file/line anchors."""

    source_location = str(item.get("source_location") or "").strip()
    anchors = [
        (
            match.group("path"),
            int(match.group("start")),
            int(match.group("end") or match.group("start")),
        )
        for match in SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_location)
    ]
    if not anchors:
        return (
            "",
            "requires byte-verified source_anchor_evidence tied to exact "
            "file:line source anchors",
        )
    raw_evidence = item.get("source_anchor_evidence")
    if not isinstance(raw_evidence, list) or not raw_evidence:
        return "", "requires a nonempty byte-verified source_anchor_evidence list"
    quotes: list[str | None] = [None] * len(anchors)
    for raw_entry in raw_evidence:
        if not isinstance(raw_entry, dict):
            return "", "source_anchor_evidence entries must be objects"
        raw_path = str(raw_entry.get("path") or "").strip()
        line_start = raw_entry.get("line_start")
        line_end = raw_entry.get("line_end")
        if (
            not raw_path
            or not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or not isinstance(line_end, int)
            or isinstance(line_end, bool)
        ):
            return (
                "",
                "source_anchor_evidence entries require path, line_start, and line_end",
            )
        matches = [
            index
            for index, (anchor_path, anchor_start, anchor_end) in enumerate(anchors)
            if source_anchor_paths_match(raw_path, anchor_path)
            and line_start == anchor_start
            and line_end == anchor_end
        ]
        if len(matches) != 1 or quotes[matches[0]] is not None:
            return (
                "",
                "source_anchor_evidence must provide exactly one quote for each "
                "declared source anchor",
            )
        raw_quote = raw_entry.get("quoted_text")
        raw_quote_digest = raw_entry.get("quoted_text_sha256")
        if not isinstance(raw_quote, str) or not raw_quote:
            return "", "source_anchor_evidence quoted_text must be a nonempty string"
        quote = raw_quote.replace("\r\n", "\n").replace("\r", "\n")
        if (
            not isinstance(raw_quote_digest, str)
            or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(raw_quote_digest.strip())
            or hashlib.sha256(quote.encode("utf-8")).hexdigest()
            != raw_quote_digest.strip().lower()
        ):
            return (
                "",
                "source_anchor_evidence quoted_text_sha256 must match the "
                "normalized quoted_text",
            )
        quotes[matches[0]] = quote
    if any(quote is None for quote in quotes):
        return (
            "",
            "source_anchor_evidence must provide exactly one quote for each "
            "declared source anchor",
        )
    return "\n".join(quote for quote in quotes if quote is not None), ""


def _source_location_has_pinned_artifact_anchor(
    item: dict[str, Any], *, classification: str
) -> str:
    artifact_path = str(item.get("source_artifact_path") or "").strip()
    artifact_sha256 = str(item.get("source_artifact_sha256") or "").strip()
    source_location = str(item.get("source_location") or "").strip()
    if not artifact_path:
        return (
            f"{classification} requires a pinned "
            "source_artifact_path"
        )
    if not SOURCE_ARTIFACT_SHA256_RE.fullmatch(artifact_sha256):
        return (
            f"{classification} requires a valid pinned "
            "source_artifact_sha256"
        )
    canonical_path = str(item.get("canonical_source_artifact_path") or "").strip()
    canonical_sha256 = str(
        item.get("canonical_source_artifact_sha256") or ""
    ).strip()
    if canonical_path and (
        artifact_path.replace("\\", "/").lstrip("./")
        != canonical_path.replace("\\", "/").lstrip("./")
    ):
        return (
            f"{classification} must use the source map's "
            "canonical pinned source artifact"
        )
    if canonical_sha256 and artifact_sha256.lower() != canonical_sha256.lower():
        return (
            f"{classification} must use the source map's "
            "canonical source_artifact_sha256"
        )
    if not EXACT_SOURCE_LOCATOR_RE.search(source_location):
        return (
            f"{classification} requires an exact "
            "source_location anchor"
        )
    artifact_suffix = Path(artifact_path).suffix.lower()
    file_anchors = list(SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_location))
    if artifact_suffix in {".tex", ".txt", ".md"}:
        if not file_anchors:
            return (
                f"{classification} requires a file:line "
                "anchor into the pinned source artifact"
            )
        normalized_artifact = artifact_path.replace("\\", "/").lstrip("./")
        normalized_anchor_paths = {
            match.group("path").replace("\\", "/").lstrip("./")
            for match in file_anchors
        }
        if not any(
            anchor_path == normalized_artifact
            or normalized_artifact.endswith("/" + anchor_path)
            or anchor_path.endswith("/" + normalized_artifact)
            for anchor_path in normalized_anchor_paths
        ):
            return (
                f"{classification} source_location must name "
                "the pinned source artifact"
            )
    _, quote_error = source_inventory_anchor_quote_text(item)
    if quote_error:
        return f"{classification} {quote_error}"
    return ""


def source_inventory_item_scope_classification_error(item: dict[str, Any]) -> str:
    """Return an error when an explicit source-scope classification is unsafe."""

    classification = str(item.get("source_scope_classification") or "").strip().lower()
    if not classification:
        return ""
    if classification not in SOURCE_SCOPE_CLASSIFICATIONS:
        return f"unknown source_scope_classification `{classification}`"
    if classification == SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION:
        if item.get("claim_bearing") is not False:
            return "source_declared_open_nonresult_observation requires claim_bearing: false"
        if str(item.get("coverage_status") or "").strip().lower() != "source_declared_open":
            return (
                "source_declared_open_nonresult_observation requires coverage_status "
                "`source_declared_open`"
            )
        if str(item.get("protocol_role") or "").strip().lower() != "source_declared_open":
            return (
                "source_declared_open_nonresult_observation requires protocol_role "
                "`source_declared_open`"
            )
        if str(item.get("source_kind") or "").strip().lower() not in {
            "remark",
            "open_problem",
        }:
            return (
                "source_declared_open_nonresult_observation requires source_kind "
                "`remark` or `open_problem`"
            )
        artifact_error = _source_location_has_pinned_artifact_anchor(
            item, classification=SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
        )
        if artifact_error:
            return artifact_error
        if not str(item.get("scope_reason") or "").strip():
            return (
                "source_declared_open_nonresult_observation requires a "
                "source-grounded scope_reason"
            )
        if not str(item.get("source_evidence") or "").strip():
            return "source_declared_open_nonresult_observation requires source_evidence"
        source_quote, quote_error = source_inventory_anchor_quote_text(item)
        if quote_error:
            return f"source_declared_open_nonresult_observation {quote_error}"
        if not SOURCE_DECLARED_OPEN_NONRESULT_RE.search(source_quote):
            return (
                "source_declared_open_nonresult_observation requires an explicit "
                "unresolved/open declaration in the byte-verified source quote"
            )
        if (
            SOURCE_NAMED_RESULT_PRESENTATION_RE.search(source_quote)
            or SOURCE_POSITIVE_RESULT_PRESENTATION_RE.search(source_quote)
        ):
            return (
                "source_declared_open_nonresult_observation cannot combine its open "
                "observation with a positive named or ordinary result assertion"
            )
        return ""
    if item.get("claim_bearing") is not False:
        return "non_named_computational_illustration requires claim_bearing: false"
    source_kind = str(item.get("source_kind") or "").strip().lower()
    if source_kind not in SOURCE_CATALOGUED_NONFORMAL_OBSERVATION_KINDS:
        return (
            "non_named_computational_illustration requires source_kind "
            "`example` or `remark`"
        )
    artifact_error = _source_location_has_pinned_artifact_anchor(
        item, classification="non_named_computational_illustration"
    )
    if artifact_error:
        return artifact_error
    source_assertion = source_inventory_core_text(item)
    source_quote, quote_error = source_inventory_anchor_quote_text(item)
    if quote_error:
        return f"non_named_computational_illustration {quote_error}"
    source_presentation = "\n".join(
        text
        for text in (
            str(item.get("title") or "").strip(),
            str(item.get("statement") or "").strip(),
            str(item.get("source_location") or "").strip(),
            str(item.get("source_evidence") or "").strip(),
        )
        if text
    )
    if SOURCE_NAMED_CLAIM_RE.search(source_assertion) or SOURCE_NAMED_CLAIM_RE.search(
        source_quote
    ):
        return (
            "non_named_computational_illustration cannot label a named formal "
            "statement or theorem reference"
        )
    combined = "\n".join((source_presentation, source_quote))
    if source_text_has_general_computational_claim(combined):
        return (
            "non_named_computational_illustration cannot label a general "
            "algorithmic, runtime, complexity, or performance assertion"
        )
    if source_text_has_general_result_assertion(combined):
        return (
            "non_named_computational_illustration cannot label a general "
            "correctness, existence, optimality, or mathematical assertion"
        )
    if (
        source_inventory_item_is_named_algorithm_block(item)
        or SOURCE_NAMED_ALGORITHM_BLOCK_RE.search(source_quote)
    ):
        return (
            "non_named_computational_illustration cannot label a named "
            "Algorithm, Procedure, or Method block"
        )
    if not source_text_has_finite_computational_observation(source_quote):
        return (
            "non_named_computational_illustration requires a literal finite "
            "observation/report in the byte-verified source quote"
        )
    if not str(item.get("scope_reason") or "").strip():
        return "non_named_computational_illustration requires a source-grounded scope_reason"
    if not str(item.get("source_evidence") or "").strip():
        return "non_named_computational_illustration requires source_evidence"
    return ""


def source_inventory_item_user_approved_scope_exclusion_error(
    item: dict[str, Any],
) -> str:
    """Validate an explicit user scope choice from source-only evidence."""

    raw_approval = item.get(USER_APPROVED_SCOPE_EXCLUSION)
    if raw_approval is None:
        return ""
    if not isinstance(raw_approval, dict):
        return "user_approved_scope_exclusion must be an object"
    if raw_approval.get("schema") != USER_APPROVED_SCOPE_EXCLUSION_SCHEMA:
        return (
            "user_approved_scope_exclusion.schema must be "
            f"{USER_APPROVED_SCOPE_EXCLUSION_SCHEMA}"
        )
    if (
        str(raw_approval.get("approval_kind") or "").strip()
        != USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND
    ):
        return (
            "user_approved_scope_exclusion.approval_kind must be "
            f"`{USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND}`"
        )
    approval_reference = str(raw_approval.get("approval_reference") or "").strip()
    if len(approval_reference) < 8:
        return (
            "user_approved_scope_exclusion.approval_reference must identify "
            "the explicit user instruction"
        )
    approved_at = str(raw_approval.get("approved_at") or "").strip()
    if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(approved_at):
        return (
            "user_approved_scope_exclusion.approved_at must be an ISO-like "
            "date or timestamp"
        )
    for field in ("reason", "source_evidence"):
        text = str(raw_approval.get(field) or "").strip()
        if len(text) < 8:
            return f"user_approved_scope_exclusion.{field} must be nonempty source-facing text"
        if NAME_ONLY_SOURCE_COVERAGE_REASON_RE.search(text):
            return (
                f"user_approved_scope_exclusion.{field} cannot rely on a "
                "declaration name or map key"
            )
    if item.get("claim_bearing") is not True:
        return (
            "user_approved_scope_exclusion must keep the source assertion "
            "claim_bearing: true"
        )
    if str(item.get("source_scope_classification") or "").strip():
        return (
            "user_approved_scope_exclusion cannot coexist with a "
            "source_scope_classification"
        )
    if str(item.get("inventory_role") or "").strip().lower() == "proof_support":
        return (
            "user_approved_scope_exclusion cannot remove an assertion marked "
            "as proof_support for a retained paper result"
        )
    source_locator = str(raw_approval.get("source_locator") or "").strip()
    source_location = str(item.get("source_location") or "").strip()
    if not source_locator:
        return "user_approved_scope_exclusion.source_locator must be a concrete source anchor"
    if source_locator != source_location:
        return (
            "user_approved_scope_exclusion.source_locator must exactly match "
            "the source item's source_location"
        )
    if not list(SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_locator)):
        return (
            "user_approved_scope_exclusion.source_locator requires an exact "
            "file:line anchor"
        )
    source_quote, quote_error = source_inventory_anchor_quote_text(item)
    if quote_error:
        return f"user_approved_scope_exclusion {quote_error}"
    quoted_digest = str(
        raw_approval.get("source_anchor_quote_sha256") or ""
    ).strip().lower()
    if not SOURCE_ARTIFACT_SHA256_RE.fullmatch(quoted_digest):
        return (
            "user_approved_scope_exclusion.source_anchor_quote_sha256 must be "
            "a SHA-256 digest"
        )
    expected_digest = hashlib.sha256(source_quote.encode("utf-8")).hexdigest()
    if quoted_digest != expected_digest:
        return (
            "user_approved_scope_exclusion.source_anchor_quote_sha256 must pin "
            "the byte-verified source anchor quote"
        )
    return ""


def source_inventory_item_requires_proof_evidence(item: object) -> bool:
    """Return whether direct coverage must include a Lean proof declaration.

    Structured source kinds control the ordinary proof/translation boundary.
    Legacy or ambiguous items fail closed through source text.  Explicit source
    definitions, assumptions, and model vocabulary stay on their direct
    translation lane; support-only and quarantined-defect items retain their
    separately validated evidence lanes.
    """

    if not isinstance(item, dict):
        return True
    source_kind = str(item.get("source_kind") or "").strip().lower()
    route_policy = source_item_effective_route_policy(item)
    if route_policy["is_support_only"]:
        return False
    if route_policy["is_quarantined_source_defect"]:
        return False
    if source_kind in {"assumption", "model"}:
        return False
    if source_kind in SOURCE_VOCABULARY_KINDS:
        return False
    if source_kind in SOURCE_RESULT_KINDS:
        return True
    if item.get("claim_bearing") is True:
        return True
    source_text = source_inventory_search_text(item)
    if (
        source_text_has_general_computational_claim(source_text)
        or source_text_has_general_result_assertion(source_text)
    ):
        return True
    if source_inventory_item_is_named_result_presentation(item):
        return True
    if source_kind:
        return source_kind in SOURCE_RESULT_KINDS
    if str(item.get("source") or "") == PAPER_STATEMENT_MAP_FILE:
        return True
    return source_inventory_item_is_named_claim(item)
