#!/usr/bin/env python3
"""Generate a v11 semantic PaperInterface from a theorem review surface.

This is intentionally a mechanical interface migration only.  It moves no
source maps, semantic judgments, or final status forward.  A paper can enter
the v11 lane only after the resulting Specs have independently source-matched
against a newly atomized, byte-pinned source inventory.

The proof module must expose its checked endpoints under the
``proof_bridge_module`` namespace. For ordinary theorem rows, the generator copies
the theorem's complete proposition into one transparent ``...Spec : Prop``
definition and creates an exact-type endpoint whose proof reuses that endpoint.
Definition-valued source rows require explicit overrides:
they cannot be guessed from a Lean declaration name or a wrapper body.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import textwrap
from pathlib import Path
from typing import Any, Iterable, Mapping


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import review_dashboard  # noqa: E402


class MigrationError(ValueError):
    """Raised when a theorem declaration cannot be migrated mechanically."""


# Lean source identifiers may carry Unicode subscripts such as ``X₁``.  At
# this point we only need a binder token that can be reused as a named
# application, so reject syntax delimiters rather than imposing ASCII.
IDENTIFIER = re.compile(r"^[^\s:()\[\]{}]+$")


def _read_json(path: Path) -> dict[str, Any]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise MigrationError(f"could not read {path}: {exc}") from exc
    if not isinstance(raw, dict):
        raise MigrationError(f"{path} must contain a JSON object")
    return raw


def _top_level_colon(text: str) -> int:
    depth = 0
    pairs = {"(": ")", "{": "}", "[": "]"}
    closes = set(pairs.values())
    for index, char in enumerate(text):
        if char in pairs:
            depth += 1
        elif char in closes:
            depth -= 1
            if depth < 0:
                raise MigrationError("unbalanced declaration header")
        elif char == ":" and depth == 0:
            return index
    raise MigrationError("could not find the declaration proposition separator")


def _top_level_token(text: str, token: str) -> int:
    """Return a declaration delimiter that is outside binder groups."""

    depth = 0
    pairs = {"(": ")", "{": "}", "[": "]"}
    closes = set(pairs.values())
    index = 0
    while index < len(text):
        char = text[index]
        if char in pairs:
            depth += 1
        elif char in closes:
            depth -= 1
            if depth < 0:
                raise MigrationError("unbalanced declaration header")
        elif depth == 0 and text.startswith(token, index):
            return index
        index += 1
    raise MigrationError(f"could not find top-level `{token}` in declaration")


def _top_level_binder_groups(text: str) -> list[str]:
    groups: list[str] = []
    index = 0
    while index < len(text):
        if text[index].isspace():
            index += 1
            continue
        if text[index] not in "([{":
            raise MigrationError(
                "unexpected text before the declaration proposition: " + text[index:]
            )
        open_char = text[index]
        close_char = {"(": ")", "[": "]", "{": "}"}[open_char]
        start = index
        depth = 0
        while index < len(text):
            char = text[index]
            if char == open_char:
                depth += 1
            elif char == close_char:
                depth -= 1
                if depth == 0:
                    groups.append(text[start : index + 1])
                    index += 1
                    break
            index += 1
        else:
            raise MigrationError("unclosed declaration binder")
    return groups


def _binder_names(groups: Iterable[str]) -> list[str]:
    names: list[str] = []
    for group in groups:
        if group.startswith("["):
            # Named and anonymous typeclass parameters are resolved by Lean
            # from the generated endpoint's expected Spec type.
            continue
        inner = group[1:-1]
        colon = _top_level_colon(inner)
        for name in inner[:colon].strip().split():
            if not IDENTIFIER.fullmatch(name):
                raise MigrationError(
                    "unsupported binder name in theorem header: " + name
                )
            names.append(name)
    return names


def _introduction_names(groups: Iterable[str]) -> list[str]:
    """Name every theorem binder while leaving typeclass evidence anonymous."""

    names: list[str] = []
    for group in groups:
        if group.startswith("["):
            # `intro _` consumes the instance binder while preserving its
            # typeclass availability.  Omitting it shifts every following
            # human binder one position to the left.
            names.append("_")
            continue
        inner = group[1:-1]
        colon = _top_level_colon(inner)
        names.extend(inner[:colon].strip().split())
    return names


def _theorem_parts(name: str, source: str) -> tuple[str, str, list[str]]:
    prefix = "theorem " + name
    if not source.startswith(prefix):
        raise MigrationError(f"{name}: source declaration is not a theorem")
    suffix = source[len(prefix) :]
    colon = _top_level_colon(suffix)
    binders = suffix[:colon].rstrip()
    # Keep leading layout here.  In particular, a theorem conclusion formed by
    # a sequence of ``let`` binders needs that shared indentation preserved
    # until `_theorem_spec_and_endpoint` can dedent the whole conclusion.
    proposition = suffix[colon + 1 :]
    if not proposition.strip():
        raise MigrationError(f"{name}: theorem has no proposition")
    groups = _top_level_binder_groups(binders)
    return binders, proposition, _binder_names(groups)


def _theorem_declarations_in_file(path: Path) -> dict[str, tuple[str, str]]:
    """Return theorem headers, including declarations whose conclusion has lets.

    The dashboard parser intentionally ignores some large implementation
    declarations whose propositions contain a chain of ``let`` bindings.  A
    v11 target may still need to copy such a proposition verbatim.  The
    fallback below extracts only through a declaration assignment boundary; it
    never infers a formula from a declaration name.  A local proposition-level
    ``let`` has a nonempty right side, whereas a final theorem assignment is
    either ``:= by`` or an assignment whose right side begins on the next
    line.  We also
    replace a dashboard-parser result when it accidentally swallowed a proof
    after a proposition-level ``let`` chain.
    """

    declarations = {
        str(short): (str(kind), str(source))
        for kind, short, _full, source, _comment, _line, _path in
        review_dashboard.parse_review_source_declarations(path)
    }
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n")
    lines = text.split("\n")
    start_pattern = re.compile(r"^theorem\s+([^\s:(]+)\b")
    for index, line in enumerate(lines):
        match = start_pattern.match(line)
        if match is None:
            continue
        name = match.group(1)
        header: list[str] = [line]
        for candidate in lines[index + 1 :]:
            boundary = candidate.find(":=")
            rhs = candidate[boundary + 2 :].strip() if boundary >= 0 else ""
            is_local_let = candidate.lstrip().startswith("let ")
            if (
                boundary >= 0
                and not is_local_let
                and (not rhs or rhs.startswith("by"))
            ):
                header.append(candidate[:boundary].rstrip())
                declarations[name] = ("theorem", "\n".join(header).rstrip())
                break
            header.append(candidate)
    return declarations


def _ordinary_spec(
    name: str, source: str, *, proof_bridge_namespace: str
) -> tuple[str, str]:
    binders, proposition, names = _theorem_parts(name, source)
    return _theorem_spec_and_endpoint(
        name,
        binders,
        proposition,
        names,
        endpoint=f"{proof_bridge_namespace}.{name}",
    )


def _theorem_spec_and_endpoint(
    name: str,
    binders: str,
    proposition: str,
    names: list[str],
    *,
    endpoint: str,
) -> tuple[str, str]:
    """Make a transparent target from a theorem and reuse its named proof.

    ``endpoint`` is deliberately explicit.  Some older interfaces expose an
    implementation theorem from a retained module instead of restating it in
    the transitional bridge.  Copying that theorem's full proposition keeps
    the new semantic target inspectable rather than turning its name into a
    wrapper-only claim.
    """

    if re.search(r"\btype_of%?\b", proposition):
        raise MigrationError(
            f"{name}: theorem proposition uses `type_of`; select the original "
            "source theorem through semantic_theorem_declarations instead of "
            "turning a proof-wrapper type into the semantic target"
        )

    # The header extractor preserves the source declaration's layout.  A
    # proposition beginning with ``let`` needs its body at the same layout
    # level after it is nested beneath ``def ... :=``; normalize first rather
    # than accidentally treating that body as part of the let value.
    proposition = textwrap.dedent(proposition).strip()
    spec = "\n".join(
        [
            f"/-- Source-facing semantic target for `{name}`. -/",
            f"def {name}Spec{binders} : Prop :=",
            "  " + proposition.replace("\n", "\n  "),
        ]
    )
    applications = " ".join(f"({value} := {value})" for value in names)
    proof_bridge_call = f"{endpoint}{(' ' + applications) if applications else ''}"
    endpoint = "\n".join(
        [
            f"theorem {name}{binders} : {name}Spec{(' ' + applications) if applications else ''} := by",
            f"  exact {proof_bridge_call}",
        ]
    )
    return spec, endpoint


def _external_source_declarations_in_file(
    path: Path,
) -> dict[str, tuple[str, str, str]]:
    """Return direct paper-local declarations with their fully qualified names.

    A transitional ``ProofBridge`` frequently aliases a source definition with
    ``@`` solely to preserve implicit universe arguments.  That alias cannot
    be a reviewable semantic target: it hides precisely the binders and body a
    reviewer needs.  This extractor lets a migration copy the original source
    declaration instead, while keeping the selected source file inside the
    paper directory.
    """

    declarations = {
        str(short): (str(kind), str(full), str(source))
        for kind, short, full, source, _comment, _line, _path in
        review_dashboard.parse_review_source_declarations(path)
    }
    # The dashboard parser intentionally declines a few very large `let`-
    # based value definitions when building an interactive surface.  The
    # migration needs their full direct body, however, and its source file is
    # already explicitly selected.  Reuse the parser's declaration collector
    # for those omissions rather than falling back to a wrapper name.
    lines = path.read_text(encoding="utf-8").replace("\r\n", "\n").split("\n")
    namespace_stack: list[str] = []
    start_pattern = re.compile(
        r"^(?:noncomputable\s+)?(?:private\s+|protected\s+)?"
        r"(?P<kind>def|abbrev|structure)\s+"
        r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b"
    )
    namespace_open = re.compile(
        r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$"
    )
    namespace_end = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_']*))?\s*$")
    for index, line in enumerate(lines):
        opened = namespace_open.match(line)
        if opened is not None:
            namespace_stack.extend(opened.group(1).split("."))
            continue
        ended = namespace_end.match(line)
        if ended is not None:
            end_name = ended.group(1)
            if namespace_stack and (end_name is None or namespace_stack[-1] == end_name):
                namespace_stack.pop()
            continue
        match = start_pattern.match(line)
        if match is None:
            continue
        name = match.group("name")
        if name in declarations:
            continue
        collected = review_dashboard.collect_review_decl_text(
            lines, index, match.group("kind")
        )
        if collected is None:
            continue
        source, _next_index = collected
        full_name = ".".join([*namespace_stack, name])
        declarations[name] = (match.group("kind"), full_name, source)
    return declarations


def _direct_source_prop_spec(
    name: str,
    source_name: str,
    source: str,
) -> tuple[str, str, list[str]]:
    """Copy a direct source ``Prop`` definition without a bridge alias."""

    binders, result_type, body, names = _definition_parts(source_name, source)
    if re.sub(r"\s+", "", result_type) != "Prop":
        raise MigrationError(
            f"{name}: external source declaration `{source_name}` is not a Prop definition"
        )
    spec = "\n".join(
        [
            f"/-- Source-facing semantic target for `{source_name}`. -/",
            f"def {name}Spec{binders} : Prop :=",
            "  " + body.replace("\n", "\n  "),
        ]
    )
    return spec, binders, names


def _direct_source_value_spec(
    name: str,
    source_name: str,
    source_full_name: str,
    source: str,
) -> tuple[str, str, list[str]]:
    """Expose an external value definition as its exact source equation."""

    binders, _result_type, body, names = _definition_parts(source_name, source)
    applications = " ".join(f"({value} := {value})" for value in names)
    application = (" " + applications) if applications else ""
    spec = "\n".join(
        [
            f"/-- Source-facing semantic target for `{source_name}`. -/",
            f"def {name}Spec{binders} : Prop :=",
            f"  {source_full_name}{application} =",
            "    " + body.replace("\n", "\n    "),
        ]
    )
    return spec, binders, names


def _structure_parts(
    name: str, source: str
) -> tuple[str, list[tuple[str, str]], list[str]]:
    """Split a simple source-model structure into binders and named fields.

    Structures have no proposition body to copy.  The semantic form used in a
    paper interface therefore quantifies over a value and exposes every source
    field with its exact type.  This is deliberately restricted to ordinary
    named fields; a structure with inheritance or commands in its body must be
    given an explicit special row rather than guessed at.
    """

    prefix = "structure " + name
    if not source.startswith(prefix):
        raise MigrationError(f"{name}: source declaration is not a structure")
    suffix = source[len(prefix) :]
    marker = re.search(r"\bwhere\b", suffix)
    if marker is None:
        raise MigrationError(f"{name}: structure has no `where` body")
    binders = suffix[: marker.start()].rstrip()
    fields: list[tuple[str, str]] = []
    for raw in suffix[marker.end() :].splitlines():
        line = raw.strip()
        if not line or line.startswith("--"):
            continue
        if ":" not in line or line.startswith(("extends ", "deriving ")):
            raise MigrationError(
                f"{name}: structure field `{line}` needs an explicit special row"
            )
        field, field_type = line.split(":", maxsplit=1)
        field = field.strip()
        field_type = field_type.strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", field) or not field_type:
            raise MigrationError(
                f"{name}: structure field `{line}` needs an explicit special row"
            )
        fields.append((field, field_type))
    if not fields:
        raise MigrationError(f"{name}: structure has no reviewable named fields")
    groups = _top_level_binder_groups(binders)
    return binders, fields, _binder_names(groups)


def _direct_source_structure_spec(
    name: str,
    source_name: str,
    source_full_name: str,
    source: str,
) -> tuple[str, str, list[str], str]:
    """Make a transparent field-level proposition for a source data model."""

    binders, fields, names = _structure_parts(source_name, source)
    applications = " ".join(f"({value} := {value})" for value in names)
    application = (" " + applications) if applications else ""
    value_type_args = " ".join(names)
    value_type_application = (" " + value_type_args) if value_type_args else ""
    existential_fields = "\n    ".join(
        f"∃ {field} : {field_type}," for field, field_type in fields
    )
    equalities = " ∧\n      ".join(
        f"value.{field} = {field}" for field, _field_type in fields
    )
    spec = "\n".join(
        [
            f"/-- Source-facing field-level semantic target for `{source_name}`. -/",
            f"def {name}Spec{binders} : Prop :=",
            f"  ∀ value : {source_full_name}{value_type_application},",
            "    " + existential_fields,
            "      " + equalities,
        ]
    )
    witnesses = ", ".join(f"value.{field}" for field, _field_type in fields)
    endpoint = "\n".join(
        [
            f"theorem {name}_realizes_spec{binders} : {name}Spec{application} := by",
            "  intro value",
            f"  exact ⟨{witnesses}, " + ", ".join("rfl" for _ in fields) + "⟩",
        ]
    )
    return spec, binders, names, endpoint


def _definition_parts(name: str, source: str) -> tuple[str, str, str, list[str]]:
    """Split a direct legacy ``def`` or ``abbrev`` into binders, type, body."""

    # `noncomputable def` has exactly the same transparent semantic body as
    # `def`; treating the modifier as part of the declaration name would
    # unnecessarily block a source presentation from the canonical surface.
    if source.startswith("noncomputable "):
        source = source[len("noncomputable ") :]
    prefixes = ("def " + name, "abbrev " + name)
    prefix = next((candidate for candidate in prefixes if source.startswith(candidate)), "")
    if not prefix:
        raise MigrationError(f"{name}: source declaration is not a def or abbrev")
    suffix = source[len(prefix) :]
    assignment = _top_level_token(suffix, ":=")
    header = suffix[:assignment]
    body = suffix[assignment + 2 :].strip()
    try:
        colon = _top_level_colon(header)
    except MigrationError:
        # Lean permits an inferred result type for `def`/`abbrev`.  The
        # value-definition and bundled-definition lanes only need the exact
        # transparent body, while the Prop-only lane will reject this absent
        # annotation rather than guessing its type.
        binders = header.rstrip()
        result_type = ""
    else:
        binders = header[:colon].rstrip()
        result_type = header[colon + 1 :].strip()
    if not body:
        raise MigrationError(f"{name}: definition has no body")
    groups = _top_level_binder_groups(binders)
    return binders, result_type, body, _binder_names(groups)


def _source_definition_spec(
    name: str,
    source_name: str,
    source: str,
    *,
    proof_bridge_namespace: str,
) -> tuple[str, str, list[str]]:
    """Generate the direct semantic target of a source predicate definition.

    A source definition is a semantic review target rather than a proposition
    asserted to hold.  Its ``Spec`` must therefore expose the full predicate
    body once, without an implementation-name wrapper.  The paired proof
    endpoint, generated by ``render``, separately proves the exact
    definition-to-Spec equivalence in the ``definitionally_realizes`` lane.
    """

    binders, result_type, body, names = _definition_parts(source_name, source)
    if re.sub(r"\s+", "", result_type) != "Prop":
        raise MigrationError(
            f"{name}: only direct Prop definitions can be migrated automatically; "
            "use special_rows for a source-specific formula target"
        )
    spec = "\n".join(
        [
            f"/-- Source-facing semantic target for the definition `{source_name}`. -/",
            f"def {name}Spec{binders} : Prop :=",
            "  " + body.replace("\n", "\n  "),
        ]
    )
    return spec, binders, names


def _source_value_definition_spec(
    name: str,
    source_name: str,
    source: str,
    *,
    proof_bridge_namespace: str,
) -> tuple[str, str, list[str]]:
    """Expose an explicitly selected value definition as an exact formula.

    The migration never infers that a value-valued Lean definition is
    paper-facing.  Once the configuration explicitly selects one, the
    canonical target displays both sides of its equality: the retained bridge
    declaration and the definition's full transparent body.  This preserves
    source-reviewable semantics without pretending that a bare declaration
    name is itself a paper claim.
    """

    binders, _result_type, body, names = _definition_parts(source_name, source)
    applications = " ".join(f"({value} := {value})" for value in names)
    application = (" " + applications) if applications else ""
    spec = "\n".join(
        [
            f"/-- Source-facing semantic target for the definition `{source_name}`. -/",
            f"def {name}Spec{binders} : Prop :=",
            f"  {proof_bridge_namespace}.{source_name}{application} =",
            "    " + body.replace("\n", "\n    "),
        ]
    )
    return spec, binders, names


def _source_definition_bundle_spec(
    name: str,
    source_names: list[str],
    declarations: Mapping[str, tuple[str, str]],
    *,
    proof_bridge_namespace: str,
) -> tuple[str, str]:
    """Make one source-presentation target from several direct definitions.

    Some sources introduce a single named definition through several related
    clauses (for example, deterministic and randomized revenue).  The source
    inventory intentionally keeps that presentation as one human claim.  A
    v11 target therefore exposes every clause as a universally quantified
    transparent equality, joined visibly rather than creating multiple
    denominator rows or hiding a component behind an alias.
    """

    components: list[str] = []
    component_proofs: list[str] = []
    for source_name in source_names:
        kind, source = declarations.get(source_name, ("", ""))
        if kind in {"def", "abbrev"}:
            binders, _result_type, body, binder_names = _definition_parts(source_name, source)
            if not binders.strip() and "@" in body:
                raise MigrationError(
                    f"{name}: polymorphic source alias `{source_name}` hides its "
                    "universe binders behind `@`; supply an explicit source-shaped "
                    "special row rather than generating a metavariable-bearing Spec"
                )
            applications = " ".join(f"({value} := {value})" for value in binder_names)
            application = (" " + applications) if applications else ""
            quantified = binders.strip()
            prefix = f"∀ {quantified}, " if quantified else ""
            # A few source-facing abbreviations construct the relevant
            # finite/nonempty carrier with a multi-line ``by`` block.  It is
            # still the declaration's transparent body, but flattening that
            # block into one line changes Lean's tactic layout and can erase
            # the binders on which its local instance construction depends.
            # Preserve the body verbatim as a term within the displayed
            # equality instead.
            if body.lstrip().startswith("by"):
                rendered_body = "\n" + textwrap.indent(body, "      ")
            else:
                rendered_body = " " + body.replace("\n", " ")
            components.append(
                prefix
                + f"{proof_bridge_namespace}.{source_name}{application} ="
                + rendered_body
            )
            # The component lives under the universal binders copied from the
            # source declaration.  Enter them before reducing the transparent
            # alias; bare `rfl` only works for a zero-binder component.
            component_proofs.append("by intros; rfl")
            continue
        if kind != "theorem":
            raise MigrationError(
                f"{name}: bundled source declaration `{source_name}` is not a def, abbrev, or theorem"
            )
        binders, proposition, theorem_binder_names = _theorem_parts(source_name, source)
        theorem_introduction_names = _introduction_names(
            _top_level_binder_groups(binders)
        )
        quantified = binders.strip()
        prefix = f"∀ {quantified}, " if quantified else ""
        components.append(prefix + textwrap.dedent(proposition).strip().replace("\n", " "))
        theorem_applications = " ".join(
            f"({value} := {value})" for value in theorem_binder_names
        )
        introduction = (
            "intro " + " ".join(theorem_introduction_names)
            if theorem_introduction_names
            else "intros"
        )
        component_proofs.append(
            "by " + introduction + "; exact "
            + f"{proof_bridge_namespace}.{source_name}"
            + (" " + theorem_applications if theorem_applications else "")
        )
    if not components:
        raise MigrationError(f"{name}: definition bundle cannot be empty")
    proposition = " ∧\n    ".join("(" + component + ")" for component in components)
    spec = "\n".join(
        [
            f"/-- Source-facing semantic target for the bundled definition `{name}`. -/",
            f"def {name}Spec : Prop :=",
            "  " + proposition,
        ]
    )
    proof_term = component_proofs[-1]
    for component_proof in reversed(component_proofs[:-1]):
        proof_term = f"⟨{component_proof}, {proof_term}⟩"
    endpoint = "\n".join(
        [
            f"theorem {name}_realizes_spec : {name}Spec := by",
            # A `Spec` is intentionally a named transparent proposition.
            # Unfold it before constructing its conjunction; otherwise Lean
            # sees only the opaque-looking proposition name and `rfl`/`intro`
            # cannot reach the bundled component goals.
            f"  unfold {name}Spec",
            f"  exact {proof_term}",
        ]
    )
    return spec, endpoint


def _semantic_claim_spec(
    name: str, source_name: str, source: str
) -> tuple[str, str, list[str]]:
    """Copy an already source-shaped legacy ``Prop`` target under its new name."""

    binders, result_type, body, names = _definition_parts(source_name, source)
    if re.sub(r"\s+", "", result_type) != "Prop":
        raise MigrationError(
            f"{name}: semantic source declaration `{source_name}` is not a Prop target"
        )
    spec = "\n".join(
        [
            f"/-- Source-facing semantic target migrated from `{source_name}`. -/",
            f"def {name}Spec{binders} : Prop :=",
            "  " + body.replace("\n", "\n  "),
        ]
    )
    return spec, binders, names


def _endpoint_for_spec(
    name: str,
    binders: str,
    names: list[str],
    *,
    proof_bridge_namespace: str,
    endpoint_declaration: str,
) -> str:
    applications = " ".join(f"({value} := {value})" for value in names)
    application = (" " + applications) if applications else ""
    return "\n".join(
        [
            f"theorem {name}{binders} : {name}Spec{application} := by",
            f"  exact {proof_bridge_namespace}.{endpoint_declaration}{application}",
        ]
    )


def _special_row(name: str, raw: object) -> tuple[str, str]:
    if not isinstance(raw, Mapping):
        raise MigrationError(f"{name}: special row must be an object")
    spec = str(raw.get("spec") or "").strip()
    endpoint = str(raw.get("endpoint") or "").strip()
    if not spec.startswith("def " + name + "Spec"):
        raise MigrationError(f"{name}: special spec must define `{name}Spec`")
    if not endpoint.startswith("theorem " + name):
        raise MigrationError(f"{name}: special endpoint must define `{name}`")
    if re.search(r"\btype_of%?\b", spec):
        raise MigrationError(
            f"{name}: special spec uses `type_of`; copy the complete semantic "
            "proposition from its source declaration instead"
        )
    return spec, endpoint


def _presentation_sections(
    config: Mapping[str, Any], names: list[str]
) -> list[tuple[str, list[str]]]:
    """Return the declared human-reading order for source claim Specs.

    Source appendices remain review material.  This setting only keeps the
    paper's main-text results together before an explicitly labelled appendix
    section; it neither changes the denominator nor suppresses a claim from
    the source-to-Spec audit.
    """

    raw_sections = config.get("presentation_sections")
    if raw_sections is None:
        return [("", names)]
    if not isinstance(raw_sections, list) or not raw_sections:
        raise MigrationError("presentation_sections must be a nonempty list")
    sections: list[tuple[str, list[str]]] = []
    seen: list[str] = []
    for raw in raw_sections:
        if not isinstance(raw, Mapping):
            raise MigrationError("each presentation section must be an object")
        title = str(raw.get("title") or "").strip()
        section_names = raw.get("names")
        if (
            not title
            or "-/" in title
            or not isinstance(section_names, list)
            or not section_names
            or not all(isinstance(item, str) and item.strip() for item in section_names)
        ):
            raise MigrationError(
                "each presentation section needs a safe title and nonempty names"
            )
        normalized = [str(item).strip() for item in section_names]
        seen.extend(normalized)
        sections.append((title, normalized))
    if len(seen) != len(set(seen)):
        raise MigrationError("presentation_sections names must be unique")
    if set(seen) != set(names):
        missing = sorted(set(names) - set(seen))
        extra = sorted(set(seen) - set(names))
        details = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unknown " + ", ".join(extra))
        raise MigrationError(
            "presentation_sections must partition include_names: " + "; ".join(details)
        )
    if seen != names:
        raise MigrationError(
            "presentation_sections must preserve include_names source/DAG order; "
            "they may add headings but cannot reorder source claims"
        )
    return sections


def render(
    *,
    paper_dir: Path,
    config: Mapping[str, Any],
) -> tuple[str, str]:
    paper = str(config.get("paper") or "").strip()
    if paper != paper_dir.name:
        raise MigrationError("migration config paper does not match --paper")
    namespace = str(config.get("namespace") or "").strip()
    proof_bridge_module = str(config.get("proof_bridge_module") or "").strip()
    if not namespace or not proof_bridge_module:
        raise MigrationError("migration config needs namespace and proof_bridge_module")
    status = _read_json(paper_dir / "status.json")
    review_surface = status.get("review_surface")
    if not isinstance(review_surface, Mapping):
        raise MigrationError("status.json has no review_surface")
    names = config.get("include_names", review_surface.get("include_names"))
    if not isinstance(names, list) or not all(isinstance(name, str) for name in names):
        raise MigrationError("migration config/status.json has no valid include_names list")
    if len(names) != len(set(names)):
        raise MigrationError("status.json include_names are not unique")
    presentation_sections = _presentation_sections(config, names)

    interface = paper_dir / "ProofBridge.lean"
    declarations = {
        str(short): (str(kind), str(source))
        for kind, short, _full, source, _comment, _line, _path in
        review_dashboard.parse_review_source_declarations(interface)
    }
    # Keep the dashboard's declaration inventory for definitions and replace
    # theorem entries with exact headers.  Such chains are common in
    # source-faithful LP and dynamic-game results; accepting a parser result
    # that swallowed a proof would silently change the semantic target.
    for short, declaration in _theorem_declarations_in_file(interface).items():
        declarations[short] = declaration
    special_rows = config.get("special_rows")
    if not isinstance(special_rows, Mapping):
        special_rows = {}
    raw_semantic_sources = config.get("semantic_source_declarations", {})
    if not isinstance(raw_semantic_sources, Mapping) or not all(
        isinstance(name, str) and isinstance(source, str)
        for name, source in raw_semantic_sources.items()
    ):
        raise MigrationError("semantic_source_declarations must be a string-to-string object")
    semantic_sources = {
        str(name).strip(): str(source).strip()
        for name, source in raw_semantic_sources.items()
    }
    raw_endpoint_sources = config.get("proof_endpoint_declarations", {})
    if not isinstance(raw_endpoint_sources, Mapping) or not all(
        isinstance(name, str) and isinstance(source, str)
        for name, source in raw_endpoint_sources.items()
    ):
        raise MigrationError("proof_endpoint_declarations must be a string-to-string object")
    endpoint_sources = {
        str(name).strip(): str(source).strip()
        for name, source in raw_endpoint_sources.items()
    }
    raw_definition_sources = config.get("source_definition_declarations", {})
    if not isinstance(raw_definition_sources, Mapping) or not all(
        isinstance(name, str) and isinstance(source, str)
        for name, source in raw_definition_sources.items()
    ):
        raise MigrationError("source_definition_declarations must be a string-to-string object")
    definition_sources = {
        str(name).strip(): str(source).strip()
        for name, source in raw_definition_sources.items()
    }
    raw_external_sources = config.get("external_source_declarations", {})
    if not isinstance(raw_external_sources, Mapping):
        raise MigrationError("external_source_declarations must be an object")
    external_sources: dict[str, tuple[str, str, str, str]] = {}
    external_declaration_cache: dict[Path, dict[str, tuple[str, str, str]]] = {}
    for raw_name, raw_source in raw_external_sources.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_source, Mapping):
            raise MigrationError(
                "each external_source_declarations entry must be a named object"
            )
        source_file = str(raw_source.get("source_file") or "").strip()
        source_name = str(raw_source.get("source_declaration") or "").strip()
        if not source_file or not source_name:
            raise MigrationError(
                f"{name}: external source needs source_file and source_declaration"
            )
        source_path = paper_dir / source_file
        try:
            source_path.resolve().relative_to(paper_dir.resolve())
        except ValueError as error:
            raise MigrationError(
                f"{name}: external source file must remain paper-local"
            ) from error
        if not source_path.is_file():
            raise MigrationError(
                f"{name}: external source file `{source_file}` is not readable"
            )
        if source_path not in external_declaration_cache:
            external_declaration_cache[source_path] = _external_source_declarations_in_file(
                source_path
            )
        kind, source_full_name, source = external_declaration_cache[source_path].get(
            source_name, ("", "", "")
        )
        if kind not in {"def", "abbrev", "structure"}:
            raise MigrationError(
                f"{name}: external source declaration `{source_name}` must be a def, abbrev, or structure in {source_file}"
            )
        external_sources[name] = (kind, source_name, source_full_name, source)
    raw_theorem_sources = config.get("semantic_theorem_declarations", {})
    if not isinstance(raw_theorem_sources, Mapping):
        raise MigrationError("semantic_theorem_declarations must be an object")
    theorem_sources: dict[str, tuple[str, str, str]] = {}
    external_declaration_cache: dict[Path, dict[str, tuple[str, str]]] = {}
    for raw_name, raw_source in raw_theorem_sources.items():
        name = str(raw_name).strip()
        if not name or not isinstance(raw_source, Mapping):
            raise MigrationError(
                "each semantic_theorem_declarations entry must be a named object"
            )
        source_file = str(raw_source.get("source_file") or "").strip()
        source_name = str(raw_source.get("source_declaration") or "").strip()
        endpoint = str(raw_source.get("proof_endpoint") or "").strip()
        if not source_file or not source_name or not endpoint:
            raise MigrationError(
                f"{name}: theorem source needs source_file, source_declaration, and proof_endpoint"
            )
        source_path = paper_dir / source_file
        try:
            source_path.resolve().relative_to(paper_dir.resolve())
        except ValueError as error:
            raise MigrationError(f"{name}: theorem source file must remain paper-local") from error
        if not source_path.is_file():
            raise MigrationError(f"{name}: theorem source file `{source_file}` is not readable")
        if source_path not in external_declaration_cache:
            external_declaration_cache[source_path] = _theorem_declarations_in_file(
                source_path
            )
        external_declarations = external_declaration_cache[source_path]
        kind, source = external_declarations.get(source_name, ("", ""))
        if kind != "theorem":
            raise MigrationError(
                f"{name}: theorem source declaration `{source_name}` is not a theorem in {source_file}"
            )
        theorem_sources[name] = (source_name, source, endpoint)
    raw_value_definition_sources = config.get("source_value_definition_declarations", {})
    if not isinstance(raw_value_definition_sources, Mapping) or not all(
        isinstance(name, str) and isinstance(source, str)
        for name, source in raw_value_definition_sources.items()
    ):
        raise MigrationError(
            "source_value_definition_declarations must be a string-to-string object"
        )
    value_definition_sources = {
        str(name).strip(): str(source).strip()
        for name, source in raw_value_definition_sources.items()
    }
    raw_definition_bundles = config.get("source_definition_bundles", {})
    if not isinstance(raw_definition_bundles, Mapping) or not all(
        isinstance(name, str)
        and isinstance(values, list)
        and values
        and all(isinstance(value, str) and value.strip() for value in values)
        for name, values in raw_definition_bundles.items()
    ):
        raise MigrationError(
            "source_definition_bundles must map names to nonempty string lists"
        )
    definition_bundles = {
        str(name).strip(): [str(value).strip() for value in values]
        for name, values in raw_definition_bundles.items()
    }
    for label, selected in (
        ("semantic_source_declarations", semantic_sources),
        ("proof_endpoint_declarations", endpoint_sources),
        ("source_definition_declarations", definition_sources),
        ("external_source_declarations", external_sources),
        ("source_value_definition_declarations", value_definition_sources),
        ("source_definition_bundles", definition_bundles),
        ("semantic_theorem_declarations", theorem_sources),
    ):
        unknown = sorted(set(selected) - set(names))
        if unknown:
            raise MigrationError(
                f"{label} names not selected by include_names: " + ", ".join(unknown)
            )
    specs_by_name: dict[str, str] = {}
    endpoints_by_name: dict[str, str] = {}
    for name in names:
        if name in special_rows:
            spec, endpoint = _special_row(name, special_rows[name])
        elif name in external_sources:
            kind, source_name, source_full_name, source = external_sources[name]
            if kind in {"def", "abbrev"}:
                _binders, result_type, _body, _binder_names = _definition_parts(
                    source_name, source
                )
                if re.sub(r"\s+", "", result_type) == "Prop":
                    spec, binders, binder_names = _direct_source_prop_spec(
                        name, source_name, source
                    )
                else:
                    spec, binders, binder_names = _direct_source_value_spec(
                        name, source_name, source_full_name, source
                    )
                applications = " ".join(
                    f"({value} := {value})" for value in binder_names
                )
                application = (" " + applications) if applications else ""
                endpoint = "\n".join(
                    [
                        f"theorem {name}_realizes_spec{binders} : {name}Spec{application} := by",
                        "  rfl",
                    ]
                )
            else:
                spec, _binders, _binder_names, endpoint = _direct_source_structure_spec(
                    name, source_name, source_full_name, source
                )
        elif name in theorem_sources:
            # An explicit direct theorem route is a deliberate source-fidelity
            # override of an older bridge bundle.  It must win over that
            # bundle so a polymorphic `@` alias cannot reclaim the row.
            source_name, source, endpoint_name = theorem_sources[name]
            binders, proposition, binder_names = _theorem_parts(source_name, source)
            spec, endpoint = _theorem_spec_and_endpoint(
                name,
                binders,
                proposition,
                binder_names,
                endpoint=endpoint_name,
            )
        elif name in definition_bundles:
            spec, endpoint = _source_definition_bundle_spec(
                name,
                definition_bundles[name],
                declarations,
                proof_bridge_namespace=proof_bridge_module,
            )
        elif name in definition_sources:
            source_name = definition_sources[name]
            kind, source = declarations.get(source_name, ("", ""))
            if kind not in {"def", "abbrev"}:
                raise MigrationError(
                    f"{name}: source definition declaration `{source_name}` is not a def or abbrev"
                )
            spec, binders, binder_names = _source_definition_spec(
                name,
                source_name,
                source,
                proof_bridge_namespace=proof_bridge_module,
            )
            applications = " ".join(
                f"({value} := {value})" for value in binder_names
            )
            application = (" " + applications) if applications else ""
            source_application = (
                " "
                + " ".join(f"({value} := {value})" for value in binder_names)
                if binder_names
                else ""
            )
            endpoint = "\n".join(
                [
                    # The Spec carries the source predicate directly.  Its
                    # endpoint certifies, rather than duplicates, the exact
                    # definitional equivalence with the paper-local source
                    # declaration.
                    f"theorem {name}_realizes_spec{binders} : "
                    f"{proof_bridge_module}.{source_name}{source_application} ↔ "
                    f"{name}Spec{application} := by",
                    "  rfl",
                ]
            )
        elif name in value_definition_sources:
            source_name = value_definition_sources[name]
            kind, source = declarations.get(source_name, ("", ""))
            if kind not in {"def", "abbrev"}:
                raise MigrationError(
                    f"{name}: source value definition `{source_name}` is not a def or abbrev"
                )
            spec, binders, binder_names = _source_value_definition_spec(
                name,
                source_name,
                source,
                proof_bridge_namespace=proof_bridge_module,
            )
            applications = " ".join(
                f"({value} := {value})" for value in binder_names
            )
            application = (" " + applications) if applications else ""
            endpoint = "\n".join(
                [
                    # See the Prop-definition lane above: an equality target
                    # for a value definition must not replace that definition
                    # in the namespace used by later copied theorem headers.
                    f"theorem {name}_realizes_spec{binders} : {name}Spec{application} := by",
                    "  rfl",
                ]
            )
        elif name in semantic_sources:
            source_name = semantic_sources[name]
            kind, source = declarations.get(source_name, ("", ""))
            if kind != "def":
                raise MigrationError(
                    f"{name}: semantic source declaration `{source_name}` is not a def"
                )
            endpoint_name = endpoint_sources.get(name, "")
            if not endpoint_name:
                raise MigrationError(
                    f"{name}: semantic_source_declarations requires a proof_endpoint_declarations entry"
                )
            spec, binders, binder_names = _semantic_claim_spec(
                name, source_name, source
            )
            endpoint = _endpoint_for_spec(
                name,
                binders,
                binder_names,
                proof_bridge_namespace=proof_bridge_module,
                endpoint_declaration=endpoint_name,
            )
        else:
            kind, source = declarations.get(name, ("", ""))
            if kind != "theorem":
                raise MigrationError(
                    f"{name}: non-theorem source row needs an explicit special_rows entry"
                )
            spec, endpoint = _ordinary_spec(
                name, source, proof_bridge_namespace=proof_bridge_module
            )
        specs_by_name[name] = spec
        endpoints_by_name[name] = endpoint

    specs: list[str] = []
    endpoints: list[str] = []
    for section_title, section_names in presentation_sections:
        if section_title:
            specs.append("/-! ## " + section_title + " -/")
            endpoints.append("/-! ## " + section_title + " -/")
        specs.extend(specs_by_name[name] for name in section_names)
        endpoints.extend(endpoints_by_name[name] for name in section_names)

    imports = config.get("semantic_imports")
    if not isinstance(imports, list) or not all(isinstance(item, str) for item in imports):
        raise MigrationError("migration config needs semantic_imports as a string list")
    open_namespaces = config.get("open_namespaces", [])
    if not isinstance(open_namespaces, list) or not all(
        isinstance(item, str) for item in open_namespaces
    ):
        raise MigrationError("open_namespaces must be a string list")
    open_scoped = config.get("open_scoped", [])
    if not isinstance(open_scoped, list) or not all(
        isinstance(item, str) and item.strip() for item in open_scoped
    ):
        raise MigrationError("open_scoped must be a string list")
    variables = str(config.get("variables") or "").strip()
    noncomputable_section = bool(config.get("noncomputable_section", False))
    namespace_parts = namespace.split(".")
    namespace_open = "\n".join("namespace " + part for part in namespace_parts)
    namespace_close = "\n".join("end " + part for part in reversed(namespace_parts))
    header = "\n".join([*(f"import {item}" for item in imports), "", namespace_open])
    shared = "\n".join(
        [
            *("open " + item for item in open_namespaces),
            *("open scoped " + item for item in open_scoped),
            *(["noncomputable section"] if noncomputable_section else []),
            variables,
        ]
    ).strip()
    section_close = "end" if noncomputable_section else ""
    paper_interface = "\n\n".join(
        [
            header,
            "namespace PaperInterface",
            shared,
            *specs,
            section_close,
            "end PaperInterface\n" + namespace_close,
            "",
        ]
    )
    proof_interface = "\n\n".join(
        [
            f"import {namespace}.PaperInterface",
            f"import {proof_bridge_module}",
            "",
            namespace_open,
            "namespace PaperInterface",
            shared,
            *endpoints,
            section_close,
            "end PaperInterface\n" + namespace_close,
            "",
        ]
    )
    return paper_interface, proof_interface


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    paper_dir = ROOT / "papers" / args.paper
    try:
        config = _read_json(args.config)
        paper_interface, proof_interface = render(paper_dir=paper_dir, config=config)
        if not args.write:
            print(
                f"{args.paper}: generated {paper_interface.count(chr(10) + 'def ')} Specs "
                "and proof endpoints; rerun with --write"
            )
            return 0
        (paper_dir / "PaperInterface.lean").write_text(paper_interface, encoding="utf-8")
        (paper_dir / "ProofInterface.lean").write_text(proof_interface, encoding="utf-8")
        print(f"{args.paper}: wrote PaperInterface.lean and ProofInterface.lean")
        return 0
    except MigrationError as exc:
        print("legacy-v11-interface-migration: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
