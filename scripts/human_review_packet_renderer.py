"""Pure TeX rendering of one already authenticated human-review surface.

Callers supply the prepared cards, template bytes, and generated date. This
owner neither reads files nor discovers, prepares, or certifies Lean material.
The shared bounded public projector preserves the exact release sanitization.
"""
from __future__ import annotations

import hashlib
import re
import unicodedata
from pathlib import Path
from typing import Any, Iterable, Mapping
from urllib.parse import urlsplit

from scripts.public_release_projection import ProjectionError, project_text
from scripts.report_context_presentation import (
    context_presentation_summary,
    validated_row_context_presentation,
)

PACKET_NAME = "HUMAN_REVIEW_PACKET"
SOURCE_MAP_NAME = "audit/paper_statement_map.json"
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"

_PREESCAPED_PACKET_LOCATOR_RE = re.compile(
    r"(\\textbf\{(?:Source locator|Archival source anchor):\}\s*)"
    r"\{\\footnotesize\\raggedright\s*(.*?)\\par\}",
    flags=re.DOTALL,
)

_NON_READER_GIT_TRANSPORT_HOSTS = frozenset({"git.overleaf.com"})

_ENDORSEMENT_DASH = r"(?:-|\u2010|\u2011|\u2012|\u2013|\u2014)"
_REVIEW_PROSE_NOUN = (
    r"(?:target|model|clarification|correction|reading|interpretation|"
    r"assumptions?|conditions?|formalization|replacement|scope|claim|result|theorem)"
)
_OWNER_REVIEW_SUBJECT_NOUN = (
    r"(?:target|model|clarification|correction|reading|interpretation|"
    r"assumptions?|conditions?|formalization|replacement|scope)"
)
_OWNER_REPOSITORY_MODIFIER = (
    r"(?:corrected\b|source[ \t]+clarification\b|governing[ \t]+model\b|"
    r"procedural[ \t]+clarification\b|formalization[ \t]+target\b|target\b|"
    r"strict-surplus\b|all-unassigned-bidder\b)"
)
_AUTHOR_FORMALIZER_MODIFIER_RE = re.compile(
    rf"(?P<article>\ban[ \t]+)?\b(?:author|formalizer){_ENDORSEMENT_DASH}"
    r"approved[ \t]+",
    flags=re.IGNORECASE,
)
_OWNER_REVIEW_MODIFIER_RE = re.compile(
    rf"(?P<article>\ban[ \t]+)?\bowner{_ENDORSEMENT_DASH}approved[ \t]+"
    rf"(?={_OWNER_REPOSITORY_MODIFIER})",
    flags=re.IGNORECASE,
)
_AUTHOR_FORMALIZER_PREDICATE_RE = re.compile(
    rf"(?P<copula>\b(?:is|was|remains)[ \t]+)"
    rf"(?:author|formalizer)(?:{_ENDORSEMENT_DASH}|[ \t]+)approved\b",
    flags=re.IGNORECASE,
)
_OWNER_REVIEW_PREDICATE_RE = re.compile(
    rf"(?P<subject>\b(?:this|the|that)[ \t]+(?:corrected[ \t]+)?"
    rf"{_OWNER_REVIEW_SUBJECT_NOUN}[ \t]+)"
    rf"(?P<copula>(?:is|was|remains)[ \t]+)"
    rf"owner(?:{_ENDORSEMENT_DASH}|[ \t]+)approved\b",
    flags=re.IGNORECASE,
)
_UNSUPPORTED_REVIEW_BRANDING_RE = re.compile(
    rf"(?:\b(?:author|formalizer){_ENDORSEMENT_DASH}approved\b|"
    rf"\b(?:author|formalizer)[ \t]+approved\b)",
    flags=re.IGNORECASE,
)


def _reader_source_url(value: object) -> str:
    """Return the primary URL only when it is useful to a public reader."""

    primary = str(value or "").split(";", maxsplit=1)[0].strip()
    try:
        parsed = urlsplit(primary)
    except ValueError:
        return ""
    hostname = (parsed.hostname or "").lower().rstrip(".")
    if (
        parsed.scheme.lower() not in {"http", "https"}
        or not hostname
        or hostname in _NON_READER_GIT_TRANSPORT_HOSTS
    ):
        return ""
    return primary


def _packet_presentation_text(value: object) -> str:
    """Project ordinary packet prose before TeX escaping it.

    Raw source excerpts remain inside ``ReviewVerbatim`` and therefore retain
    the exact quoted mathematical text.  Locators, metadata, reasons, and
    other normal presentation fields must not expose a private checkout path
    merely because TeX later turns an underscore into ``\\_``.
    """

    try:
        return project_text(
            str(value or ""),
            relative_path="docs/HUMAN_REVIEW_PACKET.tex",
        )
    except ProjectionError as exc:
        raise ValueError("packet contains non-public presentation text: " + str(exc)) from exc


def _neutral_review_prose(value: object) -> str:
    """Neutralize endorsement labels in selected reader-facing review prose.

    This is deliberately not part of ``_verbatim`` or the general packet
    projection: archival source excerpts and Lean displays must retain their
    exact text.  Callers use it only for a formalized-target description,
    reviewer reason, settled-context summary, or source-version description.
    Ambiguous economic uses of ``owner`` are preserved.  Unrecognized
    author/formalizer branding fails closed so it can receive a deliberate
    reader-facing rewrite rather than an ungrammatical word deletion.
    """

    text = str(value or "")
    text = _AUTHOR_FORMALIZER_PREDICATE_RE.sub(
        lambda match: match.group("copula") + "formalized", text
    )
    text = _OWNER_REVIEW_PREDICATE_RE.sub(
        lambda match: (
            match.group("subject") + match.group("copula") + "formalized"
        ),
        text,
    )

    def remove_modifier(match: re.Match[str]) -> str:
        if match.group("article"):
            return "a "
        prefix = text[: match.start()]
        if not prefix or re.search(r"[.!?][ \t]*$", prefix):
            return "Formalized "
        return ""

    text = _AUTHOR_FORMALIZER_MODIFIER_RE.sub(remove_modifier, text)
    text = _OWNER_REVIEW_MODIFIER_RE.sub(remove_modifier, text)
    unsupported = _UNSUPPORTED_REVIEW_BRANDING_RE.search(text)
    if unsupported:
        raise ValueError(
            "reader review prose uses unsupported endorsement wording: "
            + unsupported.group(0)
        )
    return text


def _packet_source_version(
    status: Mapping[str, Any], source_map: Mapping[str, Any]
) -> str:
    """Prefer source-map metadata, with canonical status as fallback."""

    return _packet_presentation_text(
        _neutral_review_prose(
            source_map.get("source_version")
            or status.get("source_version")
            or "not recorded"
        )
    )


def _tex_escape(value: object) -> str:
    text = _packet_presentation_text(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "#": r"\#",
        "$": r"\$",
        "%": r"\%",
        "&": r"\&",
        "_": r"\_",
        "^": r"\textasciicircum{}",
        "~": r"\textasciitilde{}",
    }
    # The prose font omits some mathematical alphanumeric symbols, including
    # bold script letters and script ell. Preserve the exact character with the math
    # font already provided by the TeX distribution, without changing source
    # text or substituting an ordinary Latin letter.
    return "".join(
        r"{\fontspec{Latin Modern Math}" + character + "}"
        if character == "ℓ" or 0x1D400 <= ord(character) <= 0x1D7FF
        else replacements.get(character, character)
        for character in text
    )


def _source_version_metadata_tex(source_version: object) -> str:
    """Render long source identities without overflowing the packet cover."""

    return (
        "\\textbf{Source version:} "
        "\\parbox[t]{0.76\\linewidth}{\\raggedright "
        + _tex_escape(source_version)
        + "}\\\\"
    )


def _tex_identifier(value: object) -> str:
    """Escape a Lean identifier while allowing graceful segment-level breaks."""

    # Long camel-case components can exceed even the physical page width in
    # dependency links. Insert break opportunities before escaping so TeX
    # control sequences and the visible identifier bytes remain intact.
    # Public projection must see the entire input before line-break markers
    # separate words or repository identifiers.
    text = _packet_presentation_text(value)
    segments = re.split(
        r"(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])", text
    )
    escaped = r"\allowbreak{}".join(_tex_escape(part) for part in segments)
    return escaped.replace(".", ".\\allowbreak{}").replace(
        r"\_", r"\_\allowbreak{}"
    )


def _tex_locator(value: object) -> str:
    """Render a public citation locator without exposing a local audit path."""

    locator = str(value or "").strip()
    # The source map's path is private provisioning detail.  Line spans remain
    # useful to a reviewer, so retain only a bounded human-facing location.
    line_match = re.search(
        r"(?:\bline(?:s)?\s*|:)" r"(\d+)(?:\s*[-–]\s*(\d+))?",
        locator,
        flags=re.IGNORECASE,
    )
    if line_match:
        start, end = line_match.group(1), line_match.group(2)
        locator = "cited publication, lines " + start + (
            "-" + end if end else ""
        )
    else:
        locator = "cited publication"
    escaped = _tex_escape(locator)
    for separator in ("/", ":", "-", ";", "."):
        escaped = escaped.replace(separator, separator + r"\allowbreak{}")
    return r"{\footnotesize\raggedright " + escaped + r"\par}"


def _tex_breakable_text(value: object) -> str:
    """Escape ordinary text while permitting breaks inside path-like references."""

    escaped = _tex_escape(value)
    for separator in ("/", ":", "-", ";", "."):
        escaped = escaped.replace(separator, separator + r"\allowbreak{}")
    escaped = escaped.replace(r"\_", r"\_\allowbreak{}")
    return escaped


def _packet_anchor(prefix: str, identity: object) -> str:
    """Return a short deterministic PDF anchor safe for arbitrary Lean names."""

    digest = hashlib.sha256(str(identity or "").encode("utf-8")).hexdigest()[:16]
    return f"{prefix}-{digest}"


def _verbatim(value: object) -> str:
    """Render untrusted audit text as TeX verbatim without ending its block."""

    text = str(value or "").strip()
    if not text:
        text = "[No record available.]"
    # A source or Lean declaration cannot normally contain this delimiter, but
    # prevent a malformed sidecar from terminating generated TeX early.
    text = text.replace(r"\end{ReviewVerbatim}", r"\textbackslash{}end{ReviewVerbatim}")
    # DejaVu Sans Mono does not contain every Unicode mathematical-alphabet
    # glyph that appears in Lean pretty-printing.  Keep the compact review
    # packet readable rather than emitting missing-character boxes.
    text = text.replace("𝓕", "calF")
    text = text.replace("ℓ", "ell")
    # CACHE_RENDERER_NEUTRAL_START
    # The monospace packet font does not provide U+2225.  Preserve the
    # standard plain-text norm notation rather than letting XeTeX drop each
    # delimiter from a reviewer-visible source formula.
    text = text.replace("∥", "||")
    # CACHE_RENDERER_NEUTRAL_END
    text = text.replace("⦃", "{{").replace("⦄", "}}")
    # Lean's pretty printer can emit private-use pieces of extensible
    # delimiters.  The packet font cannot render those pieces; retain an
    # explicit marker instead of silently deleting an unknown mathematical
    # glyph from a reviewer-visible target.
    for codepoint in (0xF8EB, 0xF8ED, 0xF8F1, 0xF8F2, 0xF8F3, 0xF8F4, 0xF8F6, 0xF8F8):
        text = text.replace(chr(codepoint), f"[U+{codepoint:04X} delimiter glyph]")
    # Lean's exact private-use pieces can vary by version.  Keep an unlisted
    # piece visible rather than emitting a missing glyph into the reviewer
    # packet.
    text = "".join(
        f"[U+{ord(character):04X} private-use glyph]"
        if unicodedata.category(character) == "Co"
        else character
        for character in text
    )
    # PDF-to-text sources sometimes retain page controls or an unprintable
    # epsilon-like control byte.  They are part of the source extraction, but
    # XeTeX cannot place them in a verbatim environment.  Render a visible,
    # deterministic marker rather than silently dropping any source content.
    rendered: list[str] = []
    for character in text:
        codepoint = ord(character)
        if character in {"\n", "\t"} or codepoint >= 32:
            rendered.append(character)
        elif character == "\f":
            rendered.append("\n[form-feed in source extraction]\n")
        else:
            rendered.append(f"[U+{codepoint:04X} control character]")
    text = "".join(rendered)
    return "\\begin{ReviewVerbatim}\n" + text + "\n\\end{ReviewVerbatim}\n"


def _governing_declaration_links_tex(
    links: object,
    *,
    heading: str = "Retained governing declarations",
) -> str:
    """Render navigation supplied by the authenticated graph projection."""

    if links is None:
        return ""
    if not isinstance(links, (list, tuple)):
        raise ValueError("governing declaration links must be a sequence")
    if not links:
        return ""
    rendered = ["\\paragraph{" + _tex_escape(heading) + "}", "\\begin{itemize}\\raggedright"]
    for raw_link in links:
        if not isinstance(raw_link, Mapping):
            raise ValueError("governing declaration link must be an object")
        name = str(raw_link.get("lean_name") or "").strip()
        anchor_kind = str(raw_link.get("anchor_kind") or "").strip()
        if not name or anchor_kind not in {
            "governing-declaration",
            "paper-prerequisite",
            "library-prerequisite",
        }:
            raise ValueError("governing declaration link has no valid destination")
        rendered.append(
            "\\item \\hyperlink{"
            + _packet_anchor(anchor_kind, name)
            + "}{"
            + _tex_identifier(name)
            + "}"
        )
    rendered.append("\\end{itemize}")
    return "\n".join(rendered)


def _prerequisites_tex(
    paper_dir: Path,
    entries: Iterable[Mapping[str, Any]],
) -> str:
    """Render source-connected library definitions before dependent claims.

    A library primitive is review material, not an unexplained glossary word.
    The shared dashboard helper returns the exact declaration body, a selected
    byte-pinned paper-source bundle, and the freshness of the independent
    source-to-library semantic judgment.  The packet deliberately preserves
    the raw source and code rather than rendering a curator paraphrase.
    """

    entries = list(entries)
    if not entries:
        return ""
    rendered = [
        "\\clearpage",
        "\\hypertarget{" + _packet_anchor("library-section", paper_dir.name) + "}{}",
        "\\section*{Material library prerequisites}",
    ]
    for entry_index, entry in enumerate(entries):
        correction_target = _approved_corrected_target_tex([entry])
        if entry.get("corrected_target_required") and not correction_target:
            raise ValueError(
                "corrected library prerequisite lacks its identity-bound "
                "formalized review target: "
                + str(entry.get("lean_name") or "unnamed declaration")
            )
        reviewer_label = (
            "Matches formalized target"
            if correction_target
            else "Matches source input"
        )
        rendered.extend(
            [
                *( ["\\clearpage"] if entry_index else [] ),
                "\\hypertarget{"
                + _packet_anchor("library-prerequisite", entry.get("lean_name"))
                + "}{}",
                "\\subsection*{\\small\\ttfamily\\raggedright "
                + _tex_identifier(entry.get("label") or entry.get("lean_name"))
                + "}",
            ]
        )
        source_input = str(entry.get("verbatim_source_input") or "").strip()
        if source_input:
            # A library prerequisite is independently reviewable.  Even when
            # multiple declarations share a byte-pinned source bundle, repeat
            # its verbatim input here instead of asking a reviewer to find an
            # earlier prerequisite page.
            rendered.extend(
                [
                    "\\textbf{Source locator:} "
                    + _tex_locator(entry.get("source_locator") or "not recorded"),
                    *(
                        [
                            "\\textbf{Source connection:} \\texttt{"
                            + _tex_escape(
                                entry.get("source_connection_state")
                                or "release_projected_excerpt"
                            )
                            + "}"
                        ]
                        if entry.get("source_connection_display_only")
                        else []
                    ),
                    "\\paragraph{Verbatim paper-source connection}",
                    _verbatim(source_input),
                    _approved_review_contexts_tex(
                        entry.get("approved_review_contexts"),
                        entry.get("approved_review_context_presentation"),
                    ),
                    correction_target,
                ]
            )
        else:
            rendered.append(
                "\\textbf{Source connection:} "
                + _tex_escape(entry.get("source_connection_error") or "not recorded")
                + "."
            )
        rendered.extend(
            [
                "\\paragraph{"
                + (
                    "Lean-expanded library semantic target"
                    if entry.get("semantic_recorded_graph_sha256")
                    or entry.get("library_semantic_target_kind") in {"definition", "abbrev"}
                    else "Lean declaration type (metadata)"
                )
                + "}",
                _verbatim(
                    entry.get("library_semantic_target")
                    or entry.get("library_semantic_target_error")
                ),
                *(
                    [
                        "\\paragraph{Exact Lean library declaration}",
                        _verbatim(entry.get("library_definition") or entry.get("library_definition_error")),
                    ]
                    if (
                        not entry.get("semantic_recorded_graph_sha256")
                        or entry.get(
                            "library_definition_recorded_graph_authenticated"
                        )
                        is True
                    )
                    else []
                ),
            ]
        )
        dependency_links = _governing_declaration_links_tex(
            entry.get("governing_declaration_links"),
            heading="Direct retained dependencies",
        )
        if dependency_links:
            rendered.append(dependency_links)
        rendered.extend(
            [
                "\\paragraph{Recorded source-to-library screening}",
                "\\textbf{Verdict:} \\texttt{"
                + _tex_escape(entry.get("semantic_judgment") or "not recorded")
                + "}",
            ]
        )
        reason = _neutral_review_prose(entry.get("semantic_reason")).strip()
        if reason:
            rendered.append("\\\\\n{\\raggedright\n\\textbf{Reason:} " + _tex_breakable_text(reason) + "\n\\par}")
        rendered.extend(
            [
                "\\reviewmatch{" + reviewer_label + "}",
                "\\noindent\\textbf{Reviewer annotation}\\par",
                "\\reviewerbox",
            ]
        )
    return "\n".join(rendered)


def _paper_prerequisites_tex(entries: Iterable[Mapping[str, Any]]) -> str:
    """Render paper-local semantic prerequisites before their dependent claims."""

    entries = list(entries)
    if not entries:
        return ""
    rendered = [
        "\\clearpage",
        "\\hypertarget{" + _packet_anchor("paper-prerequisite-section", "all") + "}{}",
        "\\section*{Paper-specific semantic prerequisites}",
    ]
    for entry_index, entry in enumerate(entries):
        correction_target = _approved_corrected_target_tex([entry])
        if entry.get("corrected_target_required") and not correction_target:
            raise ValueError(
                "corrected paper prerequisite lacks its identity-bound "
                "formalized review target: "
                + str(entry.get("lean_name") or "unnamed declaration")
            )
        reviewer_label = (
            "Matches formalized target"
            if correction_target
            else "Matches source input"
        )
        rendered.extend(
            [
                *( ["\\clearpage"] if entry_index else [] ),
                "\\hypertarget{"
                + _packet_anchor("paper-prerequisite", entry.get("lean_name"))
                + "}{}",
                "\\subsection*{\\small\\ttfamily\\raggedright "
                + _tex_identifier(entry.get("lean_name"))
                + "}",
                "\\noindent\\textbf{Paper-local declaration:}\\par",
                "{\\footnotesize\\ttfamily\\raggedright "
                + _tex_identifier(entry.get("lean_name"))
                + "\\par}",
            ]
        )
        source_input = str(entry.get("verbatim_source_input") or "").strip()
        if source_input:
            rendered.extend(
                [
                    "\\textbf{Source locator:} "
                    + _tex_locator(entry.get("source_locator") or "not recorded"),
                    *(
                        [
                            "\\textbf{Source connection:} \\texttt{"
                            + _tex_escape(
                                entry.get("source_connection_state")
                                or "release_projected_excerpt"
                            )
                            + "}"
                        ]
                        if entry.get("source_connection_display_only")
                        else []
                    ),
                    "\\paragraph{Verbatim paper-source connection}",
                    _verbatim(source_input),
                    _approved_review_contexts_tex(
                        entry.get("approved_review_contexts"),
                        entry.get("approved_review_context_presentation"),
                    ),
                    correction_target,
                ]
            )
        else:
            rendered.append(
                "\\textbf{Source connection:} "
                + _tex_escape(entry.get("source_connection_error") or "not recorded")
                + "."
            )
        rendered.extend(
            [
                "\\paragraph{"
                + (
                    "Lean-expanded paper semantic target"
                    if entry.get("paper_semantic_target_kind") in {"definition", "abbrev"}
                    else "Lean-elaborated paper signature"
                )
                + "}",
                _verbatim(
                    entry.get("paper_semantic_target")
                    or entry.get("paper_semantic_target_error")
                    or "Lean paper-prerequisite semantic target is unavailable."
                ),
                _governing_declaration_links_tex(
                    entry.get("governing_declaration_links"),
                    heading="Direct retained dependencies",
                ),
                "\\paragraph{Recorded source-to-declaration screening}",
                "\\textbf{Verdict:} \\texttt{"
                + _tex_escape(entry.get("semantic_judgment") or "not recorded")
                + "}",
            ]
        )
        reason = _neutral_review_prose(entry.get("semantic_reason")).strip()
        if reason:
            rendered.append("\\\\\n{\\raggedright\n\\textbf{Reason:} " + _tex_breakable_text(reason) + "\n\\par}")
        rendered.extend(
            [
                "\\reviewmatch{" + reviewer_label + "}",
                "\\noindent\\textbf{Reviewer annotation}\\par",
                "\\reviewerbox",
            ]
        )
    return "\n".join(rendered)


def _governing_declarations_tex(entries: Iterable[Mapping[str, Any]]) -> str:
    """Render the deduplicated authenticated dependency closure as context."""

    entries = list(entries)
    if not entries:
        return ""
    rendered = [
        "\\clearpage",
        "\\hypertarget{"
        + _packet_anchor("governing-declaration-section", "all")
        + "}{}",
        "\\section*{Governing Lean declarations}",
        (
            "These exact graph-bound declaration bodies are retained by the "
            "displayed specifications or reviewed prerequisites. They are "
            "supporting context and do not add source-result rows or semantic "
            "judgments."
        ),
    ]
    for entry in entries:
        name = str(entry.get("lean_name") or "").strip()
        location = str(entry.get("location") or "").strip()
        display = str(entry.get("display") or "")
        if not name or location not in {"paper", "library"} or not display.strip():
            raise ValueError("governing declaration display is incomplete")
        rendered.extend(
            [
                "\\hypertarget{"
                + _packet_anchor("governing-declaration", name)
                + "}{}",
                "\\subsection*{\\small\\ttfamily\\raggedright "
                + _tex_identifier(name)
                + "}",
                "\\textbf{Declaration location:} "
                + ("paper-local" if location == "paper" else "reusable library"),
                "\\paragraph{Lean declaration body}",
                _verbatim(display),
                _governing_declaration_links_tex(
                    entry.get("governing_declaration_links"),
                    heading="Direct retained dependencies",
                ),
            ]
        )
    return "\n".join(rendered)


def _record_source_blocks(
    records: Iterable[Mapping[str, Any]],
    verbatim_source_input: object,
) -> str:
    records = list(records)
    if not records:
        return "\\paragraph{Verbatim source input}\n" + _verbatim(verbatim_source_input)
    locations = [
        str(record.get("source_location") or "not recorded")
        for record in records
    ]
    chunks = [
        "\\textbf{Source locator:} " + _tex_locator("; ".join(locations)),
        "\\paragraph{Verbatim source input}",
        _verbatim(verbatim_source_input),
    ]
    return "\n".join(chunks)


def _public_packet_presentation_tex(tex: str, *, paper: str) -> str:
    """Apply the bounded public projection to non-verbatim packet material.

    ``ReviewVerbatim`` holds raw paper excerpts and Lean displays.  The source
    excerpts are permitted public evidence, so this final safety pass leaves
    those byte-visible blocks untouched.  Every surrounding heading, locator,
    metadata field, and diagnostic is projected once more as a fail-closed
    release presentation boundary.
    """

    relative_path = f"papers/{paper}/docs/{PACKET_NAME}.tex"
    blocks = re.split(
        r"(\\begin\{ReviewVerbatim\}.*?\\end\{ReviewVerbatim\})",
        tex,
        flags=re.DOTALL,
    )
    projected: list[str] = []
    for index, block in enumerate(blocks):
        if index % 2:
            projected.append(block)
            continue
        try:
            public_block = project_text(block, relative_path=relative_path)
        except ProjectionError as exc:
            raise ValueError("packet contains non-public presentation text: " + str(exc)) from exc
        projected.append(_sanitize_preescaped_packet_locators(public_block))
    return "".join(projected)


def _sanitize_preescaped_packet_locators(tex: str) -> str:
    """Normalize locators in packets generated before the public projection.

    Old packets first TeX-escaped private source paths (for example
    ``audit/\\allowbreak{}source\\_archive\\_surface.tex``), so a normal text
    projection can no longer recognize the locator.  This bounded rewrite
    touches only the two public locator labels, retains any visible line span,
    and leaves the raw-source ``ReviewVerbatim`` blocks untouched.
    """

    def replacement(match: re.Match[str]) -> str:
        raw_locator = match.group(2)
        locator = raw_locator.replace(r"\allowbreak{}", "").replace(r"\_", "_")
        return match.group(1) + _tex_locator(locator)

    return _PREESCAPED_PACKET_LOCATOR_RE.sub(replacement, tex)


def _approved_corrected_target_tex(records: Iterable[Mapping[str, Any]]) -> str:
    """Render the reviewer-visible replacement for a false archival statement.

    The archival source bundle remains first on the page.  When its map row
    deliberately records a different, approved target, the reviewer must also
    see that target and the human-facing basis for it.  A digest alone would
    make the exceptional correction lane impossible to review.
    """

    corrected: list[Mapping[str, Any]] = []
    for record in records:
        target = record.get("corrected_target")
        if (
            str(record.get("coverage_status") or "").strip()
            == "corrected_source_statement"
            and isinstance(target, Mapping)
        ):
            corrected.append(target)
    if not corrected:
        return ""
    if len(corrected) != 1:
        return (
            "\\paragraph{Formalized review target}\\textbf{Error:} "
            "multiple corrected targets are routed to one source claim."
        )
    target = corrected[0]
    archival_locator = str(target.get("archival_source_locator") or "not recorded")
    return "\n".join(
        [
            "\\paragraph{Formalized review target}",
            "The archival source above is not asserted equivalent to this formalized target.",
            _verbatim(_neutral_review_prose(target.get("statement"))),
            "\\textbf{Archival source anchor:} " + _tex_locator(archival_locator),
        ]
    )


def _approved_review_contexts_tex(
    raw_contexts: object, raw_presentation: object = None
) -> str:
    """Render the settled interpretation or addition beside the raw source."""

    if not isinstance(raw_contexts, list) or not raw_contexts:
        return ""
    summaries, omitted_convention_ids, presentation_sha256, presentation_error = (
        validated_row_context_presentation(raw_contexts, raw_presentation)
    )
    if presentation_error:
        raise ValueError("invalid review-context presentation: " + presentation_error)
    rendered: list[str] = []
    for context in raw_contexts:
        if not isinstance(context, Mapping):
            continue
        kind = str(context.get("kind") or "").strip()
        if kind == "source_model_convention":
            context_id = str(context.get("id") or "").strip()
            if context_id in omitted_convention_ids:
                continue
            rendered.extend(
                [
                    "\\paragraph{Settled source reading}",
                    "\\begin{sloppypar}",
                    _tex_breakable_text(
                        _neutral_review_prose(
                            context_presentation_summary(context, summaries)
                        )
                    ),
                    "\\end{sloppypar}",
                ]
            )
        elif kind == "maintainer_approved_additional_assumptions":
            conditions = "; ".join(
                str(value).strip() for value in context.get("conditions", [])
            )
            rendered.extend(
                [
                    "\\paragraph{Additional assumptions}",
                    "\\begin{sloppypar}",
                    _tex_escape(
                        _neutral_review_prose(conditions or "not recorded")
                    ),
                    "\\end{sloppypar}",
                ]
            )
    if not rendered:
        return ""
    return "\n".join(
        ["% report-context-presentation-sha256: " + presentation_sha256, *rendered]
    )


def _row_tex(
    item: Mapping[str, Any],
    records: Iterable[Mapping[str, Any]],
    proof_endpoint: str,
    row_number: int,
    *,
    presentation_section: str = "",
    presentation_section_anchor: str = "",
) -> str:
    verdict = str(item.get("llm_match_judgment") or "not recorded")
    reason = _neutral_review_prose(
        item.get("llm_match_reason") or "not recorded"
    )
    correction_target = _approved_corrected_target_tex(records)
    reviewer_label = (
        "Matches formalized target"
        if correction_target
        else "Matches source input"
    )
    claim_atoms = item.get("review_claim_atoms")
    claim_roles = (
        "\n".join(
            f"{index}. {str(atom.get('role') or '').strip()}: "
            f"{str(atom.get('display') or '').strip()}"
            for index, atom in enumerate(claim_atoms, start=1)
            if isinstance(atom, Mapping)
        )
        if isinstance(claim_atoms, list)
        else ""
    )

    heading = (
        [
         "\\hypertarget{" + presentation_section_anchor + "}{}"
         if presentation_section_anchor
         else "",
         "\\section*{" + _tex_escape(presentation_section) + "}",
         "\\subsection*{Review row " + str(row_number) + "}"]
        if presentation_section
        else ["\\section*{Review row " + str(row_number) + "}"]
    )
    return "\n".join(
        [
            "\\clearpage",
            "\\hypertarget{"
            + _packet_anchor("source-claim", item.get("full_name") or item.get("name"))
            + "}{}",
            *heading,
            _record_source_blocks(
                records,
                item.get("verbatim_source_input") or item.get("paper_statement"),
            ),
            _approved_review_contexts_tex(
                item.get("approved_review_contexts"),
                item.get("approved_review_context_presentation"),
            ),
            correction_target,
            (
                "\\paragraph{Lean definition declaration}"
                if item.get("semantic_target_kind")
        == "definition_declaration"
                else "\\paragraph{Expanded PaperInterface specification}"
            ),
            _verbatim(
                item.get("semantic_expanded_statement")
                or item.get("lean_statement")
                or item.get("interface_source")
            ),
            _governing_declaration_links_tex(
                item.get("governing_declaration_links")
            ),
            "\\paragraph{Lean-elaborated claim roles}" + _verbatim(claim_roles)
            if claim_roles
            else "",
            "\\paragraph{Lean proof endpoint (built separately)}"
            + _verbatim(proof_endpoint)
            if proof_endpoint
            else "",
            "\\paragraph{Recorded source-to-Spec screening}",
            "\\textbf{Verdict:} \\texttt{" + _tex_escape(verdict) + "}",
            "\\\\\n{\\raggedright\n\\textbf{Reason:} " + _tex_breakable_text(reason) + "\n\\par}",
            "\\reviewmatch{" + reviewer_label + "}",
            "\\noindent\\textbf{Reviewer annotation}\\par",
            "\\reviewerbox",
        ]
    )


def _review_readiness_notice(
    claim_rows: Iterable[Mapping[str, Any]],
    paper_prerequisites: Iterable[Mapping[str, Any]],
    library_prerequisites: Iterable[Mapping[str, Any]],
) -> str:
    """Describe pending direct reviews once, before the packet cards.

    An activated v11 surface is enough to generate a human-review worksheet;
    it is not enough to imply that the current source-to-Spec and material
    library judgments have all been recorded.  Keep this summary in the front
    matter, rather than repeating a generic diagnostic disclaimer on each
    page.  Individual cards still expose their own recorded verdict.
    """

    categories = (
        ("source-claim screens", list(claim_rows), "llm_match_current"),
        (
            "paper-prerequisite screens",
            list(paper_prerequisites),
            "semantic_current",
        ),
        ("library prerequisite screens", list(library_prerequisites), "semantic_current"),
    )
    pending = [
        f"{sum(bool(row.get(field)) for row in rows)}/{len(rows)} {label}"
        for label, rows, field in categories
        if rows and not all(bool(row.get(field)) for row in rows)
    ]
    if not pending:
        return ""
    return (
        "\\noindent\\fbox{\\parbox{0.96\\linewidth}{\\textbf{Review status:} "
        + _tex_escape("; ".join(pending))
        + ". This is a review worksheet while those direct checks remain pending; "
        "it is not a final validation receipt.}}\\par"
    )


def _contents_tex(
    paper_dir: Path,
    claim_sections: Iterable[
        tuple[str, list[tuple[dict[str, Any], list[Mapping[str, Any]], str]]]
    ],
    paper_prerequisites: Iterable[Mapping[str, Any]],
    library_prerequisites: Iterable[Mapping[str, Any]],
    governing_declarations: Iterable[Mapping[str, Any]] = (),
) -> str:
    """Render a compact linked contents list for the packet's review order."""

    # ``PreparedReviewSurface`` has already interpreted Lean's direct
    # dependency edges once.  Contents and body must consume that same order;
    # neither renderer is allowed to perform another graph walk.
    library_entries = list(library_prerequisites)
    paper_entries = list(paper_prerequisites)
    governing_entries = list(governing_declarations)
    rendered = ["\\section*{Contents}", "\\begin{itemize}[leftmargin=1.2em]"]
    if governing_entries:
        rendered.append(
            "\\item \\hyperlink{"
            + _packet_anchor("governing-declaration-section", "all")
            + "}{Governing Lean declarations ("
            + str(len(governing_entries))
            + "; supporting context)}"
        )
    if library_entries:
        rendered.extend(
            [
                "\\item \\hyperlink{"
                + _packet_anchor("library-section", paper_dir.name)
                + "}{Semantic library prerequisites ("
                + str(len(library_entries))
                + "; not paper claims)}",
                "\\begin{itemize}[leftmargin=1.2em]",
            ]
        )
        for entry in library_entries:
            name = str(entry.get("label") or entry.get("lean_name") or "Library prerequisite")
            rendered.append(
                "\\item \\hyperlink{"
                + _packet_anchor("library-prerequisite", entry.get("lean_name"))
                + "}{"
                + _tex_identifier(name)
                + "}"
            )
        rendered.append("\\end{itemize}")
    if paper_entries:
        rendered.extend(
            [
                "\\item \\hyperlink{"
                + _packet_anchor("paper-prerequisite-section", "all")
                + "}{Paper-specific semantic prerequisites ("
                + str(len(paper_entries))
                + "; not paper claims)}",
                "\\begin{itemize}[leftmargin=1.2em]",
            ]
        )
        for entry in paper_entries:
            name = str(entry.get("lean_name") or "Paper prerequisite")
            rendered.append(
                "\\item \\hyperlink{"
                + _packet_anchor("paper-prerequisite", name)
                + "}{"
                + _tex_identifier(name)
                + "}"
            )
        rendered.append("\\end{itemize}")
    for raw_title, section_rows in claim_sections:
        title = raw_title or "Source claims"
        rendered.extend(
            [
                "\\item \\hyperlink{"
                + _packet_anchor("source-section", title)
                + "}{"
                + _tex_escape(title)
                + " ("
                + str(len(section_rows))
                + ")}",
                "\\begin{itemize}[leftmargin=1.2em]",
            ]
        )
        for item, records, _proof_endpoint in section_rows:
            record = records[0] if records else {}
            name = str(
                record.get("source_item")
                or record.get("title")
                or item.get("name")
                or "Source claim"
            )
            rendered.append(
                "\\item \\hyperlink{"
                + _packet_anchor(
                    "source-claim", item.get("full_name") or item.get("name")
                )
                + "}{"
                + _tex_identifier(name)
                + "}"
            )
        rendered.append("\\end{itemize}")
    rendered.append("\\end{itemize}")
    return "\n".join(rendered)


def render_packet(
    surface: Any,
    *,
    template: str,
    generated_date: str,
) -> str:
    """Return deterministic TeX for one current dashboard review surface."""

    paper = surface.paper_dir.name
    paper_dir = surface.paper_dir
    source_map = surface.source_map
    status = surface.status
    surface_error = surface.surface_error
    prepared_rows = list(surface.claim_rows)
    rows: list[str] = []
    row_number = 0
    claim_sections = [
        (title, list(section_rows))
        for title, section_rows in surface.claim_sections
    ]
    for section_title, section_rows in claim_sections:
        display_section_title = section_title or "Source claims"
        for section_index, (item, records, proof_endpoint) in enumerate(section_rows):
            row_number += 1
            rows.append(
                _row_tex(
                    item,
                    records,
                    proof_endpoint,
                    row_number,
                    presentation_section=(
                        display_section_title if section_index == 0 else ""
                    ),
                    presentation_section_anchor=(
                        _packet_anchor("source-section", display_section_title)
                        if section_index == 0
                        else ""
                    ),
                )
            )
    if not rows:
        raise ValueError(f"{paper} has no dashboard review rows")
    paper_prerequisites = list(surface.paper_prerequisites)
    library_prerequisites = list(surface.library_prerequisites)
    governing_declarations = list(
        getattr(surface, "governing_declarations", ())
    )
    # Do this before TeX escaping so a path such as `.audit_source` cannot
    # become an escaped form that a later public-content scan cannot recognize.
    source_version = _packet_source_version(status, source_map)
    source_url = _reader_source_url(source_map.get("source_url"))
    metadata = [
        "\\noindent\\textbf{Paper:} " + _tex_escape(paper) + "\\\\",
        "\\textbf{Paper id:} \\texttt{" + _tex_escape(paper) + "}\\\\",
        _source_version_metadata_tex(source_version),
        "\\textbf{Source record:} \\texttt{" + _tex_escape(SOURCE_MAP_NAME) + "}\\\\",
        "\\textbf{Rows:} " + str(len(rows)) + "\\\\",
        "\\textbf{Generated:} " + generated_date
        + ("\\\\" if source_url else ""),
    ]
    if source_url:
        # The exact URL is a convenience link, not review evidence (the map's
        # byte-pinned anchors are).  Keep it compact enough that it cannot
        # create an overfull header in packets with an archival and TeX URL.
        metadata.append(
            "\\textbf{Source URL:} "
            + "\\href{"
            + source_url.replace("%", r"\%")
            + "}{official source}"
        )
    draft_notice = (
        "\\noindent\\fbox{\\parbox{0.96\\linewidth}{\\textbf{Draft diagnostic only.} "
        + _tex_escape(surface_error)
        + ". This is not a complete v11 human-review packet or a closeout artifact.}}\\par"
        if surface_error
        else ""
    )
    review_readiness_notice = _review_readiness_notice(
        [item for item, _records, _proof in prepared_rows],
        paper_prerequisites,
        library_prerequisites,
    )
    rendered = (
        template.replace("@@PAPER_TITLE@@", _tex_escape(paper))
        .replace("@@PAPER_ID@@", _tex_escape(paper))
        .replace("@@METADATA@@", "\n".join(metadata))
        .replace("@@REVIEW_STATUS_NOTICE@@", review_readiness_notice)
        .replace("@@DRAFT_NOTICE@@", draft_notice)
        .replace(
            "@@CONTENTS@@",
            _contents_tex(
                paper_dir,
                claim_sections,
                paper_prerequisites,
                library_prerequisites,
                governing_declarations,
            ),
        )
        .replace(
            "@@PREREQUISITES@@",
            "\n".join(
                part
                for part in (
                    _governing_declarations_tex(governing_declarations),
                    _prerequisites_tex(
                        paper_dir,
                        library_prerequisites,
                    ),
                    _paper_prerequisites_tex(paper_prerequisites),
                )
                if part
            ),
        )
        .replace("@@ROWS@@", "\n".join(rows))
    )
    return _public_packet_presentation_tex(rendered, paper=paper)
