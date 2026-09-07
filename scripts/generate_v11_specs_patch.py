#!/usr/bin/env python3
"""Emit an ``apply_patch`` patch adding transparent v11 Specs to one interface.

This migration helper never writes a Lean file.  It reads the currently
configured legacy review rows and prints a patch which appends one explicit
``...Spec : Prop`` declaration for each row.  A theorem row's Spec repeats its
checked proposition verbatim; a definition/abbreviation row's Spec is the
corresponding explicit equality to its existing transparent value.  The caller
reviews and applies the patch separately, so this is a mechanical interface
migration rather than an unreviewed source-to-Lean judgment.
"""

from __future__ import annotations

import argparse
import json
import re

import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.review_dashboard import parse_review_source_declarations


_DECL_HEAD_RE = re.compile(
    r"^(?P<prefix>(?:(?:noncomputable|private|protected)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*)\b",
    re.S,
)


class GenerationError(ValueError):
    """A selected row cannot be mechanically represented as a transparent Spec."""


def _outer_token(text: str, token: str) -> int | None:
    """Find ``token`` outside Lean's ordinary paired delimiters and strings."""

    opening = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⟪": "⟫", "⟦": "⟧"}
    expected: list[str] = []
    in_string = False
    i = 0
    while i < len(text):
        if in_string:
            if text[i] == "\\\\":
                i += 2
                continue
            if text[i] == '"':
                in_string = False
            i += 1
            continue
        if text.startswith("--", i):
            newline = text.find("\n", i)
            if newline < 0:
                return None
            i = newline + 1
            continue
        if text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        if text[i] == '"':
            in_string = True
            i += 1
            continue
        char = text[i]
        if char in opening:
            expected.append(opening[char])
            i += 1
            continue
        if expected and char == expected[-1]:
            expected.pop()
            i += 1
            continue
        if not expected and text.startswith(token, i):
            return i
        i += 1
    return None


def _explicit_binder_arguments(binders: str) -> str:
    """Return explicit parenthesized binder names for a transparent def equality."""

    names: list[str] = []
    opening = {"(": ")", "[": "]", "{": "}"}
    stack: list[tuple[str, int]] = []
    groups: list[tuple[str, str]] = []
    for index, character in enumerate(binders):
        if character in opening:
            stack.append((character, index))
            continue
        if not stack or character != opening[stack[-1][0]]:
            continue
        opener, start = stack.pop()
        if not stack:
            groups.append((opener, binders[start + 1 : index]))
    for opener, body in groups:
        # Bracketed binders are typeclass arguments, and brace binders are
        # inferred implicit arguments.  A positional equality target needs
        # only the explicitly parenthesized term arguments.
        if opener != "(":
            continue
        colon = _outer_token(body, ":")
        if colon is None:
            continue
        for name in body[:colon].strip().split():
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", name):
                names.append(name)
    return " ".join(names)


_ABBREVIATION_TYPE_MACRO = """\
/- Elaborator support for Specs of polymorphic theorem aliases.

The target is the alias's exact proposition type, obtained from Lean's
environment rather than reconstructed from a lossy pretty-printed expression.
-/
open Lean Elab Term Meta

syntax "v11PropositionTypeOf " ident : term

elab_rules : term
  | `(v11PropositionTypeOf $identifier:ident) => do
    let name ← resolveGlobalConstNoOverload identifier
    let info ← getConstInfo name
    let proposition := info.type
    let sort ← inferType proposition
    unless sort.isProp do
      throwError "v11PropositionTypeOf expects a proposition-valued declaration"
    return proposition
"""


def _render_spec(name: str, kind: str, source: str) -> str:
    match = _DECL_HEAD_RE.match(source.lstrip())
    if match is None or match.group("name") != name or match.group("kind") != kind:
        raise GenerationError(f"could not parse configured declaration `{name}`")
    after_name = source.lstrip()[match.end() :]
    colon = _outer_token(after_name, ":")
    assignment = _outer_token(after_name, ":=")
    if kind in {"theorem", "lemma"}:
        if colon is None:
            raise GenerationError(f"`{name}` has no proposition delimiter")
        binders = after_name[:colon].rstrip()
        conclusion = textwrap.dedent(after_name[colon + 1 :]).strip()
        if not conclusion:
            raise GenerationError(f"`{name}` has an empty proposition")
        rendered_conclusion = conclusion.replace("\n", "\n  ")
        return (
            f"/-- Transparent v11 semantic target for `{name}`. -/\n"
            f"def {name}Spec{binders} : Prop :=\n"
            f"  {rendered_conclusion}\n"
        )
    if kind == "abbrev":
        return (
            f"/-- Transparent v11 semantic target for the source abbreviation `{name}`. -/\n"
            f"def {name}Spec : Prop :=\n"
            f"  v11PropositionTypeOf {name}\n"
        )
    if assignment is None:
        raise GenerationError(f"`{name}` has no transparent definition value")
    binders = after_name[:assignment].rstrip()
    # A definition may declare its result type between its binders and `:=`.
    # That result belongs to the original definition, not to the transparent
    # proposition's binder list.
    result_annotation = _outer_token(binders, ":")
    if result_annotation is not None:
        binders = binders[:result_annotation].rstrip()
    value = after_name[assignment + 2 :].strip()
    # An abbreviation declared as ``:= @constant`` stores the same semantic
    # function but exposes different binder-info when repeated under an
    # equality target.  Let the explicit left-hand type infer the constant's
    # implicits instead of forcing all of them with ``@``.
    if value.startswith("@"):
        value = value[1:].lstrip()
    arguments = _explicit_binder_arguments(binders)
    application = f"{name} {arguments}".rstrip()
    return (
        f"/-- Transparent v11 semantic target for the source definition `{name}`. -/\n"
        f"def {name}Spec{binders} : Prop :=\n"
        f"  {application} = ({value})\n"
    )


def generate(paper: str) -> str:
    folder = ROOT / "papers" / paper
    status_path = folder / "status.json"
    interface_path = folder / "PaperInterface.lean"
    try:
        status = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise GenerationError(f"could not read {status_path}: {error}") from error
    surface = status.get("review_surface")
    names = surface.get("include_names") if isinstance(surface, dict) else None
    if not isinstance(names, list) or not names or not all(isinstance(name, str) for name in names):
        raise GenerationError("status review_surface.include_names must be a nonempty string list")
    text = interface_path.read_text(encoding="utf-8")
    declarations = {
        name: (kind, source)
        for kind, name, _full_name, source, _comment, _line, _path
        in parse_review_source_declarations(interface_path, source_text=text)
    }
    # Once a v11 surface is activated, status records the selected `...Spec`
    # names.  If a generated block was deliberately removed for repair, recover
    # its legacy source declaration rather than treating the selected target as
    # an unrelated missing declaration.
    names = [
        name[:-4]
        if name.endswith("Spec") and name not in declarations and name[:-4] in declarations
        else name
        for name in names
    ]
    already = {name for name in declarations if name.endswith("Spec")}
    chunks: list[str] = []
    needs_abbreviation_type_macro = False
    missing: list[str] = []
    for name in names:
        if name + "Spec" in already:
            continue
        row = declarations.get(name)
        if row is None:
            missing.append(name)
            continue
        kind, source = row
        if kind not in {"theorem", "lemma", "def", "abbrev"}:
            missing.append(name)
            continue
        chunks.append(_render_spec(name, kind, source))
        needs_abbreviation_type_macro = needs_abbreviation_type_macro or kind == "abbrev"
    if missing:
        raise GenerationError(
            "configured rows not found as theorem/lemma/def/abbrev: " + ", ".join(missing)
        )
    if not chunks:
        return ""
    closing_matches = list(
        re.finditer(r"(?m)^end(?:\s+[A-Za-z_][A-Za-z0-9_']*)?[ \t]*$", text)
    )
    preferred = [
        index
        for index, match in enumerate(closing_matches)
        if match.group(0).strip() == "end PaperInterface"
    ]
    if preferred:
        interface_closing = closing_matches[preferred[-1]]
        if preferred[-1] > 0 and closing_matches[preferred[-1] - 1].group(0).strip() == "end":
            # Preserve section-scoped variables (notably `noncomputable section`)
            # used by older theorem headers.  The transparent Specs belong just
            # before that section closes, not after it at the namespace boundary.
            closing = closing_matches[preferred[-1] - 1]
        else:
            # The common nested-namespace layout ends directly with
            # `end PaperInterface`; place Specs inside that namespace.
            closing = interface_closing
    else:
        closing = closing_matches[-1] if closing_matches else None
    if closing is None:
        raise GenerationError("could not find the closing PaperInterface namespace")
    offset = closing.start()
    marker = closing.group(0)
    insertion = (
        (_ABBREVIATION_TYPE_MACRO + "\n" if needs_abbreviation_type_macro else "")
        + "\n".join(chunks)
    )
    # `apply_patch` resolves relative paths from the shared workspace root,
    # while this helper lives inside the private checkout.
    relative = Path(ROOT.name) / interface_path.relative_to(ROOT)
    added = "+" + insertion.replace("\n", "\n+")
    return (
        "*** Begin Patch\n"
        f"*** Update File: {relative}\n"
        "@@\n"
        f"-{text[offset:offset + len(marker)]}\n"
        f"{added}\n"
        f"+{text[offset:offset + len(marker)]}\n"
        "*** End Patch\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    args = parser.parse_args()
    try:
        patch = generate(args.paper)
    except GenerationError as error:
        print(f"v11 Spec patch generation refused: {error}", file=sys.stderr)
        return 1
    if patch:
        print(patch, end="")
    else:
        print(f"{args.paper}: every configured row already has a Spec")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
