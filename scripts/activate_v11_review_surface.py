#!/usr/bin/env python3
"""Select a prepared v11 PaperInterface surface in a paper's status file.

The command makes the upgrade explicit and intentionally does not certify the
paper.  Once selected, the normal closeout gate requires current raw
source-to-Spec, paper-prerequisite, library, and atom-correspondence evidence.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
V11_PROMPT = (
    "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-supporting-declarations-v4"
)


class ActivationError(ValueError):
    """Raised when the prepared semantic surface is not well formed."""


def load_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ActivationError(f"could not read {label}: {error}") from error
    if not isinstance(value, dict):
        raise ActivationError(f"{label} must be a JSON object")
    return value


def v11_contract_specs(
    source_map: Mapping[str, Any], *, namespace: str
) -> tuple[list[str], dict[str, str]]:
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise ActivationError("source map has no items object")
    nested_prefix = namespace + ".PaperInterface."
    proof_interface_prefix = namespace + ".ProofInterface."
    root_prefix = namespace + "."
    specs: list[str] = []
    proof_endpoints: dict[str, str] = {}
    for raw_item in raw_items.values():
        if not isinstance(raw_item, Mapping):
            continue
        contract = raw_item.get("semantic_contract")
        if not isinstance(contract, Mapping):
            continue
        spec = str(contract.get("spec_declaration") or "").strip()
        if spec.startswith(nested_prefix):
            short_spec = spec[len(nested_prefix) :]
        elif spec.startswith(root_prefix):
            # Older paper modules sometimes place their review declarations
            # directly in the paper namespace rather than in a nested
            # `PaperInterface` namespace.  The source file is still the
            # designated PaperInterface module; accept that layout without
            # forcing an unrelated theorem refactor.
            short_spec = spec[len(root_prefix) :]
        else:
            raise ActivationError(
                "every selected semantic contract must name a paper-interface `...Spec`: "
                + spec
            )
        if not short_spec or "." in short_spec or not short_spec.endswith("Spec"):
            raise ActivationError(
                "every selected semantic contract must name a direct paper-interface `...Spec`: "
                + spec
            )
        evidence = str(contract.get("evidence_declaration") or "").strip()
        if evidence:
            # The current architecture deliberately separates the expanded
            # source-facing `Spec` from its exact theorem endpoint.  Prefer a
            # nested ProofInterface endpoint, retain the pre-v11
            # PaperInterface layout, and finally accept a legacy direct paper
            # namespace endpoint.  The generated status mapping stores only
            # the declaration's short navigation name.
            endpoint_prefix = next(
                (
                    prefix
                    for prefix in (
                        proof_interface_prefix,
                        nested_prefix,
                        root_prefix,
                    )
                    if evidence.startswith(prefix)
                ),
                None,
            )
            if endpoint_prefix is None:
                raise ActivationError(
                    "every selected semantic contract must name a direct "
                    "ProofInterface or legacy PaperInterface proof endpoint: " + evidence
                )
            short_evidence = evidence[len(endpoint_prefix) :]
            if not short_evidence or "." in short_evidence:
                raise ActivationError(
                    "every selected semantic contract must name a direct proof endpoint: "
                    + evidence
                )
        else:
            # Backward-compatible handling for a pre-v11 fixture; real v11
            # maps always bind an explicit theorem endpoint.
            short_evidence = short_spec[: -len("Spec")]
        specs.append(short_spec)
        proof_endpoints[short_spec] = short_evidence
    if not specs:
        raise ActivationError("source map has no v11 semantic contracts")
    if len(specs) != len(set(specs)):
        raise ActivationError("one semantic Spec is routed by multiple source items")
    return specs, proof_endpoints


def activate(status: dict[str, Any], source_map: Mapping[str, Any], *, paper: str) -> dict[str, Any]:
    source_paper = str(source_map.get("paper") or "").strip()
    if source_paper != paper:
        raise ActivationError("source map paper does not match --paper")
    namespace = str(source_map.get("paper_interface_namespace") or source_paper).strip()
    if not namespace:
        raise ActivationError("source map needs a paper-interface namespace")
    specs, proof_endpoints = v11_contract_specs(source_map, namespace=namespace)
    result = dict(status)
    surface = dict(result.get("review_surface") or {})
    surface["source_file"] = f"papers/{paper}/PaperInterface.lean"
    surface.pop("human_source_file", None)
    surface["include_names"] = specs
    surface["proposition_spec_proofs"] = proof_endpoints
    raw_slices = surface.get("slices")
    if isinstance(raw_slices, list):
        selected = set(specs)
        assigned: set[str] = set()
        current_slices: list[dict[str, Any]] = []
        for raw_slice in raw_slices:
            if not isinstance(raw_slice, Mapping):
                continue
            names = raw_slice.get("names")
            if not isinstance(names, list):
                continue
            current_names = [
                name
                for name in names
                if isinstance(name, str)
                and name in selected
                and name not in assigned
            ]
            if not current_names:
                continue
            current_slice = dict(raw_slice)
            current_slice["names"] = current_names
            current_slices.append(current_slice)
            assigned.update(current_names)
        remaining = [name for name in specs if name not in assigned]
        if remaining:
            current_slices.append(
                {
                    "id": "additional_source_results",
                    "title": "Additional source results",
                    "names": remaining,
                }
            )
        surface["slices"] = current_slices
    surface["require_v11_raw_source_spec_screening"] = True
    surface["require_source_spec_correspondence"] = True
    statement_review = dict(surface.get("llm_statement_review") or {})
    statement_review["required_prompt_version"] = V11_PROMPT
    statement_review["policy"] = (
        "For every selected source claim, compare only its exact byte-pinned raw "
        "source-anchor bundle and Lean's expanded transparent `...Spec : Prop` "
        "target. The paired proof endpoint receives separate Lean-Meta proof credit; "
        "a name, paraphrase, wrapper, or prior aggregate receipt is not a semantic "
        "match. Review every retained paper-local prerequisite and every material "
        "library prerequisite before the dependent claim."
    )
    surface["llm_statement_review"] = statement_review
    result["review_surface"] = surface
    # A new v11 claim surface is a new human-review queue.  Saved review
    # counts are displayed on the website, so retaining a legacy denominator
    # (or carry-forwarding completed rows) would falsely report review of
    # different source-to-Spec targets.
    result["human_review"] = {
        "reviewed_rows": 0,
        "total_rows": len(specs),
        "stale_rows": 0,
        "mismatch_rows": 0,
        "uncertain_rows": 0,
        "source": "v11 PaperInterface claim surface; human entries are recorded after direct review",
    }
    return result


def status_route_projection_errors(
    status: Mapping[str, Any],
    source_map: Mapping[str, Any],
    *,
    paper: str,
) -> tuple[str, ...]:
    """Report stale human-surface navigation without treating it as evidence.

    The schema-2 source map is the authority for claim routes.  ``status.json``
    repeats their short names only for the dashboard, packet, and final
    source-first review.  Keeping that projection exact is a cheap
    pre-graph consistency check: it prevents a deleted wrapper or omitted
    current Spec from confusing a human reviewer, while it cannot replace the
    typed route or Lean graph as semantic/proof authority.
    """

    try:
        expected = activate(dict(status), source_map, paper=paper)["review_surface"]
    except (ActivationError, KeyError, TypeError) as error:
        return (f"could not derive the v11 status review surface: {error}",)
    observed = status.get("review_surface")
    if not isinstance(observed, Mapping):
        return ("status.json has no review_surface to project from the typed map",)
    errors: list[str] = []
    for field in ("include_names", "proposition_spec_proofs"):
        if observed.get(field) != expected.get(field):
            errors.append(
                f"status.json review_surface.{field} is stale relative to the typed "
                "source-map routes; run activate_v11_review_surface.py --write"
            )
    return tuple(errors)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    paper_dir = ROOT / "papers" / args.paper
    try:
        status = load_object(paper_dir / "status.json", label="status.json")
        source_map = load_object(
            paper_dir / "audit" / "paper_statement_map.json", label="source map"
        )
        activated = activate(status, source_map, paper=args.paper)
    except ActivationError as error:
        print(f"v11 review-surface activation refused: {error}", file=sys.stderr)
        return 1
    count = len(activated["review_surface"]["include_names"])
    if not args.write:
        print(f"{args.paper}: would select {count} v11 semantic claim Specs; rerun with --write")
        return 0
    path = paper_dir / "status.json"
    path.write_text(json.dumps(activated, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"{args.paper}: selected {count} v11 semantic claim Specs in {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
