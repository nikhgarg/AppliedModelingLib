#!/usr/bin/env python3
"""Emit an ``apply_patch`` patch for source-item-level v11 contract Specs.

Older review interfaces often split one source presentation into several
checked Lean rows.  The v11 protocol instead has one transparent Spec for each
byte-pinned source-inventory item.  This helper combines the existing exact
proposition rows for such an item with conjunction, and emits a paper-local
proof endpoint assembled from their existing checked proofs.  It does not
infer source meanings or alter the source map; it only makes its already
declared direct routes into a one-source/one-Spec surface.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.generate_v11_specs_patch import _DECL_HEAD_RE, _outer_token
from scripts.review_dashboard import parse_review_source_declarations




class GenerationError(ValueError):
    """A direct route cannot be turned into an explicit source-item contract."""


def _header_parts(name: str, kind: str, source: str) -> tuple[str, str]:
    match = _DECL_HEAD_RE.match(source.lstrip())
    if match is None or match.group("name") != name or match.group("kind") != kind:
        raise GenerationError(f"could not parse direct route `{name}`")
    after_name = source.lstrip()[match.end() :]
    colon = _outer_token(after_name, ":")
    if kind in {"theorem", "lemma"}:
        if colon is None:
            raise GenerationError(f"`{name}` lacks a proposition delimiter")
        return after_name[:colon].rstrip(), after_name[colon + 1 :].strip()
    if kind in {"def", "abbrev"}:
        assignment = _outer_token(after_name, ":=")
        if assignment is None:
            raise GenerationError(f"`{name}` lacks a transparent value")
        return after_name[:assignment].rstrip(), ""
    raise GenerationError(f"`{name}` is not a theorem, lemma, def, or abbrev")


def _simple_binder_names(binders: str) -> list[str]:
    """Extract the ordinary named binders used by the older definitions here."""

    names: list[str] = []
    depth = 0
    start = 0
    groups: list[tuple[str, str]] = []
    for index, char in enumerate(binders):
        if char in "([{":
            if depth == 0:
                start = index
            depth += 1
        elif char in ")]}":
            depth -= 1
            if depth == 0:
                groups.append((binders[start], binders[start + 1 : index]))
    if depth:
        raise GenerationError("unbalanced direct-route binders")
    for opener, body in groups:
        if opener == "[":
            continue
        before_colon = body.split(":", maxsplit=1)[0].strip()
        for candidate in before_colon.split():
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", candidate):
                names.append(candidate)
    return names


def _definition_proposition(name: str, binders: str) -> tuple[str, str]:
    arguments = _simple_binder_names(binders)
    result_annotation = _outer_token(binders, ":")
    if result_annotation is not None:
        binders = binders[:result_annotation].rstrip()
        arguments = _simple_binder_names(binders)
    if not binders.strip():
        return f"{name}Spec", f"{name}Spec_proof"
    named = " ".join(f"({argument} := {argument})" for argument in arguments)
    universal = f"∀ {binders}, {name}Spec {named}".rstrip()
    proof = f"by\n    intro {' '.join(arguments)}\n    exact {name}Spec_proof {' '.join(arguments)}"
    return universal, proof


def _conjunction(values: list[str]) -> str:
    if len(values) == 1:
        return values[0]
    return " ∧\n    ".join(values)


def _proof_tuple(values: list[str]) -> str:
    if len(values) == 1:
        return values[0]
    return "⟨" + ", ".join(values) + "⟩"


def generate(paper: str) -> str:
    folder = ROOT / "papers" / paper
    interface_path = folder / "PaperInterface.lean"
    map_path = folder / "audit" / "paper_statement_map.json"
    try:
        source_map = json.loads(map_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise GenerationError(f"could not read {map_path}: {error}") from error
    items = source_map.get("items")
    if not isinstance(items, dict):
        raise GenerationError("source map needs an item object")
    route_users: dict[str, list[str]] = {}
    for raw_key, raw_item in items.items():
        if not isinstance(raw_item, dict):
            continue
        for raw_route in raw_item.get("lean_declarations", []):
            route_users.setdefault(str(raw_route), []).append(str(raw_key))
    text = interface_path.read_text(encoding="utf-8")
    declarations = {
        name: (kind, source)
        for kind, name, _full_name, source, _comment, _line, _path
        in parse_review_source_declarations(interface_path, source_text=text)
    }
    chunks: list[str] = []
    for raw_key, raw_item in items.items():
        if not isinstance(raw_item, dict):
            continue
        routes = raw_item.get("lean_declarations")
        if not isinstance(routes, list) or not routes:
            continue
        key = str(raw_key)
        # A shared old declaration needs an explicit source atomization or
        # consolidation before it can honestly become several one-to-one v11
        # contracts.  Model assumptions remain on the separately reviewed
        # Assumptions surface rather than becoming a paper theorem target.
        if raw_item.get("source_kind") == "assumption" or any(
            len(route_users.get(str(route), [])) > 1 for route in routes
        ):
            continue
        if key + "Spec" in declarations:
            continue
        propositions: list[str] = []
        proofs: list[str] = []
        for raw_route in routes:
            route = str(raw_route).rsplit(".", maxsplit=1)[-1]
            declaration = declarations.get(route)
            if declaration is None:
                # Assumption and implementation declarations remain in their
                # separately audited surfaces.  A v11 human claim packet only
                # contracts the paper-interface portions of a source item.
                continue
            kind, source = declaration
            binders, conclusion = _header_parts(route, kind, source)
            if kind in {"theorem", "lemma"}:
                propositions.append(f"(∀ {binders}, {conclusion})" if binders else f"({conclusion})")
                proofs.append(route)
            else:
                # A binder-free abbreviation to an explicitly polymorphic
                # constant (``:= @foo``) is an implementation packaging
                # route, not a stand-alone proposition at one universe.  Its
                # concrete formula obligations remain in the other direct
                # source routes of this source item.
                assignment = _outer_token(source.lstrip(), ":=")
                value = source.lstrip()[assignment + 2 :].lstrip() if assignment is not None else ""
                if not binders.strip() and value.startswith("@"):
                    continue
                proposition, proof = _definition_proposition(route, binders)
                propositions.append(f"({proposition})")
                proofs.append(proof)
        if not propositions:
            continue
        chunks.append(
            f"/-- Transparent v11 source-item target for `{key}`. -/\n"
            f"def {key}Spec : Prop :=\n"
            f"  {_conjunction(propositions)}\n\n"
            f"/-- Checked proof endpoint for the v11 source-item target `{key}`. -/\n"
            f"theorem {key}Spec_proof : {key}Spec := by\n"
            f"  unfold {key}Spec\n"
            f"  exact {_proof_tuple(proofs)}\n"
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
        if (
            preferred[-1] > 0
            and closing_matches[preferred[-1] - 1].group(0).strip() == "end"
        ):
            # Keep contracts inside a preceding `noncomputable section`, so their
            # declarations retain the PaperInterface namespace and scoped context.
            closing = closing_matches[preferred[-1] - 1]
        else:
            closing = interface_closing
    else:
        closing = closing_matches[-1] if closing_matches else None
    if closing is None:
        raise GenerationError("could not find the closing PaperInterface namespace")
    marker = closing.group(0)
    insertion = "\n".join(chunks)
    added = "+" + insertion.replace("\n", "\n+")
    relative = Path(ROOT.name) / interface_path.relative_to(ROOT)
    return (
        "*** Begin Patch\n"
        f"*** Update File: {relative}\n"
        "@@\n"
        f"-{marker}\n"
        f"{added}\n"
        f"+{marker}\n"
        "*** End Patch\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    args = parser.parse_args()
    try:
        patch = generate(args.paper)
    except GenerationError as error:
        print(f"v11 source-contract patch generation refused: {error}", file=sys.stderr)
        return 1
    if patch:
        print(patch, end="")
    else:
        print(f"{args.paper}: every directly routed source item already has a source-item Spec")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
