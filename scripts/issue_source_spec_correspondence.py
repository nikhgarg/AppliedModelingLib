#!/usr/bin/env python3
"""Issue direct-review v11 correspondence records without guessing a bridge.

The reviewer-owned ledger names every current source atom, supplies its
source-to-Spec bridge, and supplies the source basis for material terminals.
This command only obtains the current Lean closure and fills its derived
identities.  It refuses to issue a record unless the current raw-source to
expanded-Spec screening says matches and the normal v11 validators accept the
result.
"""

from __future__ import annotations

import argparse
import copy
import json
import os
import sys
import tempfile
from collections.abc import Mapping
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

try:  # Keep one canonical module identity under package and direct execution.
    from scripts import audit_evidence_integrity as integrity
    from scripts import audit_repository as repository
    from scripts import refresh_source_spec_correspondence as refresh
    from scripts.current_closeout import review_surface
    from scripts.obligation_routes import (
        EvidenceRoute,
        EvidenceRouteSet,
        ObligationRouteError,
    )
except ModuleNotFoundError:  # Direct execution from a copied scripts directory.
    import audit_evidence_integrity as integrity
    import audit_repository as repository
    import refresh_source_spec_correspondence as refresh
    from current_closeout import review_surface
    from obligation_routes import (
        EvidenceRoute,
        EvidenceRouteSet,
        ObligationRouteError,
    )


REVIEW_SCHEMA = 1
DEFAULT_LEDGER = Path("audit") / "source_spec_reissue_review.json"


def read_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError(f"could not read {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def atomic_write(path: Path, value: Mapping[str, Any]) -> None:
    # Paper statement maps contain verbatim Unicode source excerpts. Preserve
    # their human-facing representation instead of rewriting every non-ASCII
    # character as a JSON escape when adding a correspondence record.
    encoded = json.dumps(value, indent=2, sort_keys=False, ensure_ascii=False) + "\n"
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except Exception:
        temporary.unlink(missing_ok=True)
        raise


def checked_review(
    ledger: Mapping[str, Any],
    *,
    paper: str,
    key: str,
    specification: str,
    atom_ids: set[str],
) -> tuple[dict[str, Any] | None, list[str]]:
    errors: list[str] = []
    if ledger.get("schema") != REVIEW_SCHEMA:
        errors.append(f"ledger schema must be {REVIEW_SCHEMA}")
    if ledger.get("paper") != paper:
        errors.append("ledger paper does not match")
    for field in ("audit_kind", "validator", "validated_at"):
        if not str(ledger.get(field) or "").strip():
            errors.append(f"ledger.{field} must be nonempty")
    raw_items = ledger.get("items")
    raw = raw_items.get(key) if isinstance(raw_items, Mapping) else None
    if not isinstance(raw, Mapping):
        return None, [*errors, f"ledger has no item {key}"]
    if str(raw.get("spec_declaration") or "").strip() != specification:
        errors.append("ledger spec_declaration does not match source map")
    raw_bindings = raw.get("source_atom_bindings")
    if not isinstance(raw_bindings, list) or not raw_bindings:
        errors.append("ledger source_atom_bindings must be a nonempty list")
    else:
        bindings = [binding for binding in raw_bindings if isinstance(binding, Mapping)]
        ids = [str(binding.get("source_atom_id") or "").strip() for binding in bindings]
        if len(bindings) != len(raw_bindings) or set(ids) != atom_ids or len(ids) != len(atom_ids):
            errors.append("ledger source_atom_bindings must cover every current source atom once")
        if any(not str(binding.get("semantic_bridge") or "").strip() for binding in bindings):
            errors.append("every ledger source_atom_binding needs semantic_bridge text")
        if len(atom_ids) > 1 and any(
            not integrity.meaningful_semantic_text(
                binding.get("overlap_justification")
            )
            for binding in bindings
        ):
            errors.append(
                "every multi-atom ledger source_atom_binding needs a substantive "
                "overlap_justification because the issuer binds it to the complete "
                "expanded Spec surface"
            )
    terminal = raw.get("closure_terminal_disposition")
    if not isinstance(terminal, Mapping):
        errors.append("ledger closure_terminal_disposition must be an object")
    else:
        terminal_id = str(terminal.get("source_atom_id") or "").strip()
        basis = terminal.get("semantic_basis")
        if terminal_id not in atom_ids:
            errors.append("ledger terminal source_atom_id is not a current source atom")
        if not isinstance(basis, Mapping) or set(basis) != {
            "artifact_path",
            "artifact_sha256",
            "source_locator",
            "semantic_statement",
        }:
            errors.append("ledger terminal semantic_basis has the wrong shape")
    return (dict(raw) if not errors else None), errors


def _source_record_for_spec(
    source_map: Mapping[str, Any],
    specification: str,
    *,
    route_by_specification: Mapping[str, EvidenceRoute],
) -> Mapping[str, Any] | None:
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        return None
    route = route_by_specification.get(specification)
    raw = raw_items.get(route.source_item_id) if route is not None else None
    return raw if isinstance(raw, Mapping) else None


def current_matching_screening(
    paper_dir: Path,
    source_map: Mapping[str, Any],
    specification: str,
    *,
    route_by_specification: Mapping[str, EvidenceRoute] | None = None,
    semantic_targets_override: Mapping[str, Mapping[str, Any]] | None = None,
) -> str:
    """Require the current semantic screen appropriate to the source target.

    Ordinary source claims require literal ``matches``.  A false archival
    statement has a deliberately different current target, so its only
    accepted screen is the approval-pinned correction disposition.  This
    issuer must understand that exceptional lane; otherwise a fully valid
    corrected target could never receive the separate realization receipt.
    """

    if route_by_specification is None:
        try:
            route_by_specification = EvidenceRouteSet.from_source_map(
                source_map,
            ).result_route_by_specification()
        except ObligationRouteError as error:
            return f"source map has invalid typed routes: {error}"

    if semantic_targets_override is not None:
        target = semantic_targets_override.get(specification)
        if not isinstance(target, Mapping):
            return "shared Lean-expanded Spec target is unavailable"
        semantic_targets = {specification: dict(target)}
    else:
        try:
            projection = review_surface.load_current_v11_review_graph_projection(
                ROOT, paper_dir
            )
        except (OSError, RuntimeError, TypeError, ValueError) as error:
            return "could not read the current Lean-expanded Spec target: " + str(error)
        if projection is None:
            return (
                "current Lean review graph checkpoint is unavailable; run "
                f"python3 scripts/closeout_reuse_plan.py --paper {paper_dir.name} "
                "and execute its graph-preparation action"
            )
        target = projection.semantic_targets.get(specification)
        if not isinstance(target, Mapping):
            return "current Lean review graph omits the selected Spec target"
        semantic_targets = {specification: dict(target)}
    rows = review_surface.current_v11_screening_rows(
        paper_dir, source_map, semantic_targets
    )
    row = rows.get(specification)
    if not isinstance(row, Mapping):
        return "no current raw-source-to-expanded-Spec screening record"
    if row.get("current") is not True:
        return "raw-source-to-expanded-Spec screening is stale or malformed"
    verdict = str(row.get("judgment") or "").strip().lower()
    record = _source_record_for_spec(
        source_map,
        specification,
        route_by_specification=route_by_specification,
    )
    if verdict == "matches":
        if (
            isinstance(record, Mapping)
            and str(record.get("coverage_status") or "").strip()
            == integrity.CORRECTED_SOURCE_STATEMENT_STATUS
        ):
            return "corrected source statement requires approved-corrected-target screening, not matches"
        return ""
    if verdict != integrity.APPROVED_CORRECTED_TARGET_MATCH:
        return "raw-source-to-expanded-Spec screening is not matches"
    if (
        not isinstance(record, Mapping)
        or str(record.get("coverage_status") or "").strip()
        != integrity.CORRECTED_SOURCE_STATEMENT_STATUS
    ):
        return "approved-corrected-target screening has no unique corrected source-map route"
    try:
        status = read_object(paper_dir / "status.json")
    except ValueError as error:
        return "could not validate the approved corrected target: " + str(error)
    correction_findings = integrity.corrected_source_statement_map_findings(
        paper_dir, str(status.get("status") or ""), dict(source_map)
    )
    if correction_findings:
        return "approved corrected target has invalid source-map record: " + correction_findings[0].message
    return ""


def correspondence(
    item: Mapping[str, Any], review: Mapping[str, Any], closure: Mapping[str, Any]
) -> tuple[dict[str, Any] | None, list[str]]:
    contract = item.get("semantic_contract")
    atoms = item.get(integrity.SOURCE_CLAIM_ATOMS_KEY)
    if not isinstance(contract, Mapping) or not isinstance(atoms, list):
        return None, ["source item lacks semantic_contract or source_claim_atoms"]
    atom_errors = integrity.source_claim_atoms_validation_errors(atoms, require_source_quote=True)
    if atom_errors:
        return None, atom_errors
    atom_by_id = {
        str(atom.get("id") or "").strip(): atom
        for atom in atoms
        if isinstance(atom, Mapping) and str(atom.get("id") or "").strip()
    }
    surface = str(closure.get("surface_sha256") or "").strip().lower()
    closure_sha = str(closure.get("sha256") or "").strip().lower()
    environment = repository.semantic_contract_closure_environment_sha256(closure)
    if not surface or not closure_sha or not environment:
        return None, ["Lean closure has no usable receipt fields"]
    bindings = []
    for binding in review["source_atom_bindings"]:
        assert isinstance(binding, Mapping)
        atom = atom_by_id[str(binding["source_atom_id"])]
        result_binding = {
            "source_atom_sha256": integrity.source_claim_atom_semantic_sha256(atom),
            "spec_component_sha256s": [surface],
            "semantic_bridge": str(binding["semantic_bridge"]).strip(),
        }
        overlap_justification = str(
            binding.get("overlap_justification") or ""
        ).strip()
        if overlap_justification:
            result_binding["overlap_justification"] = overlap_justification
        bindings.append(result_binding)
    terminal = review["closure_terminal_disposition"]
    assert isinstance(terminal, Mapping)
    terminal_atom = atom_by_id[str(terminal["source_atom_id"])]
    basis = copy.deepcopy(dict(terminal["semantic_basis"]))
    required, errors = repository._realization_required_node_components(dict(closure))  # noqa: SLF001
    if errors:
        return None, errors
    dispositions = []
    for node in closure.get("nodes", []):
        if not isinstance(node, Mapping):
            continue
        component = repository.semantic_contract_closure_node_component_sha256(node)
        if component not in required:
            continue
        pin = str(node.get("pinned_declaration_identity_sha256") or "").strip()
        if not pin:
            return None, ["Lean closure has a required node with no pinned identity"]
        dispositions.append(
            {
                "closure_component_sha256": component,
                "source_atom_sha256": integrity.source_claim_atom_semantic_sha256(terminal_atom),
                "semantic_basis": basis,
                "pinned_declaration_identity_sha256": pin,
            }
        )
    result: dict[str, Any] = {
        "schema": integrity.SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
        "source_atoms_sha256": integrity.source_claim_atoms_semantic_sha256(atoms),
        "spec_closure_sha256": closure_sha,
        "spec_surface_sha256": surface,
        "closure_environment_sha256": environment,
        "source_atom_bindings": bindings,
        "closure_node_dispositions": dispositions,
    }
    result["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
        dict(contract), result
    )
    static = integrity.source_spec_correspondence_validation_errors(
        result, raw_atoms=atoms, raw_contract=contract
    )
    if static:
        return None, static
    candidate = copy.deepcopy(dict(item))
    candidate[integrity.SOURCE_SPEC_CORRESPONDENCE_KEY] = result
    runtime = repository.source_spec_correspondence_runtime_errors(candidate, dict(closure))
    return (result if not runtime else None), runtime


def issue(root: Path, paper: str, ledger_path: Path, keys: list[str], write: bool) -> tuple[list[str], list[str]]:
    folder = root / "papers" / paper
    map_path = folder / "audit" / "paper_statement_map.json"
    try:
        source_map, ledger = read_object(map_path), read_object(ledger_path)
    except ValueError as error:
        return [], [str(error)]
    raw_items = source_map.get("items")
    if not isinstance(raw_items, Mapping):
        return [], ["source map has no items object"]
    try:
        route_set = EvidenceRouteSet.from_source_map(
            source_map,
        )
        route_by_source_item = route_set.by_source_item()
        route_by_specification = route_set.result_route_by_specification()
    except ObligationRouteError as error:
        return [], [f"source map has invalid typed routes: {error}"]
    if not keys:
        keys = [
            route.source_item_id
            for route in route_set.result_routes()
            if isinstance((item := raw_items.get(route.source_item_id)), Mapping)
            and item.get(integrity.SOURCE_SPEC_CORRESPONDENCE_KEY) is None
            and isinstance(item.get(integrity.SOURCE_CLAIM_ATOMS_KEY), list)
            and item[integrity.SOURCE_CLAIM_ATOMS_KEY]
        ]
    selected: list[tuple[str, dict[str, Any], dict[str, Any]]] = []
    errors: list[str] = []
    for key in keys:
        item = raw_items.get(key)
        route = route_by_source_item.get(key)
        specification = route.spec_declaration if route is not None else ""
        atoms = item.get(integrity.SOURCE_CLAIM_ATOMS_KEY) if isinstance(item, Mapping) else None
        atom_ids = {
            str(atom.get("id") or "").strip()
            for atom in atoms if isinstance(atom, Mapping)
        } if isinstance(atoms, list) else set()
        if not specification or not atom_ids:
            errors.append(f"{key}: source map item lacks a strict semantic contract")
            continue
        review, review_errors = checked_review(
            ledger, paper=paper, key=key, specification=specification, atom_ids=atom_ids
        )
        if review_errors:
            errors.extend(f"{key}: {error}" for error in review_errors)
        if not review_errors:
            assert isinstance(item, Mapping) and review is not None
            selected.append((key, dict(item), review))
    if errors:
        return [], errors

    specifications = sorted(
        {
            route_by_source_item[key].spec_declaration
            for key, _item, _review in selected
        }
    )
    try:
        projection = review_surface.load_current_v11_review_graph_projection(
            root, folder
        )
    except (OSError, RuntimeError, TypeError, ValueError) as error:
        return [], [
            "could not read the current Lean-expanded Spec surface: " + str(error)
        ]
    if projection is None:
        return [], [
            "current Lean review graph checkpoint is unavailable; run "
            f"python3 scripts/closeout_reuse_plan.py --paper {paper} and execute "
            "its graph-preparation action"
        ]
    missing_targets = sorted(
        set(specifications) - set(projection.semantic_targets)
    )
    if missing_targets:
        return [], [
            "current Lean review graph omits selected Spec targets: "
            + ", ".join(missing_targets)
        ]
    semantic_targets = {
        specification: dict(projection.semantic_targets[specification])
        for specification in specifications
    }
    for key, _item, _review in selected:
        specification = route_by_source_item[key].spec_declaration
        screening_error = current_matching_screening(
            folder,
            source_map,
            specification,
            route_by_specification=route_by_specification,
            semantic_targets_override=semantic_targets,
        )
        if screening_error:
            errors.append(f"{key}: {screening_error}")
    if errors:
        return [], errors
    closures, closure_errors = refresh.current_lean_closures(
        root, folder, [(key, item) for key, item, _review in selected],
        timeout_seconds=180, build_timeout_seconds=600
    )
    if closure_errors:
        return [], closure_errors
    updated = copy.deepcopy(source_map)
    updated_items = updated["items"]
    issued = []
    for key, item, review in selected:
        specification = route_by_source_item[key].spec_declaration
        record, record_errors = correspondence(item, review, closures.get(specification, {}))
        if record_errors:
            errors.extend(f"{key}: {error}" for error in record_errors)
            continue
        assert isinstance(updated_items, dict) and record is not None
        updated_items[key][integrity.SOURCE_SPEC_CORRESPONDENCE_KEY] = record
        issued.append(key)
    if errors:
        return [], errors
    if write:
        atomic_write(map_path, updated)
    return issued, []


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--item", action="append", default=[])
    parser.add_argument("--review-ledger", type=Path, default=DEFAULT_LEDGER)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    folder = root / "papers" / args.paper
    if args.review_ledger.is_absolute() or ".." in args.review_ledger.parts:
        print("review ledger must be paper-local", file=sys.stderr)
        return 2
    ledger_path = folder / args.review_ledger
    issued, errors = issue(root, args.paper, ledger_path, args.item, args.write)
    if errors:
        print(f"{args.paper}: correspondence issuance refused:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 2
    print(f"{args.paper}: {'issued' if args.write else 'would issue'} " + ", ".join(issued))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
