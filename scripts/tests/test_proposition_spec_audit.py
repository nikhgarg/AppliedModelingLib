#!/usr/bin/env python3
"""Regression tests for proposition-spec and theorem-evidence closeout gates."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

from scripts import audit_evidence_integrity  # noqa: E402
from scripts import audit_repository  # noqa: E402
from scripts import lean_signature_manifest  # noqa: E402
from scripts import review_dashboard  # noqa: E402
from scripts import review_surface_structure  # noqa: E402
from scripts import source_claim_policy  # noqa: E402
from scripts import source_record_integrity  # noqa: E402
from scripts import sync_paper_status  # noqa: E402


def typed_fixture_declaration_index(
    folder: Path,
    declarations: dict[str, str],
) -> dict[str, list[audit_repository.LeanDeclaration]]:
    """Build synthetic Lean-environment records for current-v11 unit tests."""

    path = folder / "PaperInterface.lean"
    index: dict[str, list[audit_repository.LeanDeclaration]] = {}
    for line, (qualified_name, kind) in enumerate(declarations.items(), start=1):
        short_name = qualified_name.rsplit(".", 1)[-1]
        declaration = audit_repository.LeanDeclaration(
            path=path,
            line=line,
            kind=kind,
            name=short_name,
            source=f"{kind} {short_name}",
            qualified_name=qualified_name,
            identity_authority="lean_environment",
        )
        index.setdefault(qualified_name, []).append(declaration)
        index.setdefault(short_name, []).append(declaration)
    return index


def proposition_spec_manifest() -> dict[str, object]:
    return {
        "schema": 2,
        "declaration_kind": "definition",
        "conclusion_mode": "type_and_value",
        "atoms": [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {
                    "tag": "definition",
                    "type": {"tag": "sort", "level": {"tag": "zero"}},
                    "value": {"tag": "const", "name": "True", "levels": []},
                },
                "display": "Prop := True",
            }
        ],
    }


def theorem_manifest() -> dict[str, object]:
    return {
        "schema": 2,
        "declaration_kind": "theorem",
        "conclusion_mode": "type_only",
        "atoms": [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {"tag": "const", "name": "True", "levels": []},
                "display": "True",
            }
        ],
    }


def normalized_fixture_manifest(raw: dict[str, object]) -> dict[str, object]:
    """Attach the mandatory complete Lean-owned graph receipts to a fixture."""

    value = json.loads(json.dumps(raw))
    atoms = value.get("atoms")
    assert isinstance(atoms, list) and atoms
    result = atoms[-1]
    assert isinstance(result, dict)
    canonical = result.get("canonical")
    assert isinstance(canonical, dict)
    declaration_kind = str(value.get("declaration_kind") or "")
    root = "Fixture.endpoint"
    value["semantic_dependency_graph"] = {
        "schema": 1,
        "root_declaration": root,
        "complete": True,
        "realization_complete": True,
        "nodes": [
            {
                "declaration": root,
                "module_origin": "Fixture.Interface",
                "origin_class": "review_closure",
                "declaration_kind": declaration_kind,
                "canonical_identity": {
                    "tag": (
                        "local_theorem"
                        if declaration_kind == "theorem"
                        else "inlined_definition"
                    ),
                    "type": canonical,
                },
            }
        ],
        "edges": [],
        "failures": [],
    }
    value["elaborated_proposition_graph"] = {
        "schema": 1,
        "complete": True,
        "nodes": [
            {
                "path": "result",
                "kind": "constant",
                "canonical": canonical,
            }
        ],
        "edges": [],
        "failures": [],
    }
    normalized = lean_signature_manifest.normalize_signature_manifest(value)
    assert normalized is not None
    return normalized


def make_fixture_coverage_source_inputs_current(folder: Path) -> None:
    """Upgrade an accepted coverage fixture to the current raw-source protocol.

    Older tests exercised downstream routing rules with page labels alone.  The
    production gate now (correctly) requires every accepted source judgment to
    be bound to a verbatim byte-pinned excerpt.  Keep those downstream tests
    meaningful by supplying real fixture bytes instead of mocking or relaxing
    the source-input gate.
    """

    map_path = folder / "audit" / "paper_statement_map.json"
    coverage_path = folder / "audit" / "paper_coverage_llm.json"
    statement_map = json.loads(map_path.read_text(encoding="utf-8"))
    items = statement_map.get("items")
    assert isinstance(items, dict)

    missing_anchor_keys = [
        key
        for key, item in items.items()
        if isinstance(item, dict) and not item.get("source_anchor_evidence")
    ]
    if missing_anchor_keys:
        source_path = folder / "fixture_source.txt"
        source_lines: list[str] = []
        for key in missing_anchor_keys:
            item = items[key]
            assert isinstance(item, dict)
            quote = str(item.get("statement") or item.get("title") or key).strip()
            assert quote and "\n" not in quote
            source_lines.append(quote)
            line = len(source_lines)
            item["source_anchor_evidence"] = [
                {
                    "path": source_path.name,
                    "line_start": line,
                    "line_end": line,
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                }
            ]
        source_path.write_text("\n".join(source_lines) + "\n", encoding="utf-8")
        map_path.write_text(json.dumps(statement_map), encoding="utf-8")

    inventory = review_dashboard.paper_statement_inventory(folder)
    coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
    coverage["source_input_protocol"] = "verbatim_source_anchor_bundle_v1"
    coverage["paper_statement_inventory_sha256"] = (
        review_dashboard.paper_statement_inventory_digest(inventory)
    )
    coverage_items = coverage.get("items")
    assert isinstance(coverage_items, dict)
    for source_key, judgment in coverage_items.items():
        if source_key not in inventory or not isinstance(judgment, dict):
            continue
        identity, error = review_dashboard.source_anchor_quote_identity(
            inventory[source_key]
        )
        assert not error, error
        judgment["source_anchor_quote_identity_sha256"] = identity
    coverage_path.write_text(json.dumps(coverage), encoding="utf-8")


def semantic_contract_manifest_pair(
    predicate: str = "Fixture.P",
) -> tuple[dict[str, object], dict[str, object]]:
    """Return alpha-equivalent transparent-Spec and theorem telescopes."""

    nat = {"tag": "const", "name": "Nat", "levels": []}
    predicate_constant = {
        "tag": "const",
        "name": predicate,
        "levels": [],
    }
    specification = normalized_fixture_manifest(
        {
            "schema": 2,
            "declaration_kind": "definition",
            "conclusion_mode": "type_and_value",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {
                        "tag": "definition",
                        "type": {"tag": "sort", "level": {"tag": "zero"}},
                        "value": {
                            "tag": "forall",
                            "binder_info": "explicit",
                            "domain": nat,
                            "domain_is_proposition": False,
                            "body": {
                                "tag": "app",
                                "fn": predicate_constant,
                                "arg": {"tag": "bvar", "index": "0"},
                            },
                        },
                    },
                    "display": "Prop := forall x : Nat, Fixture.P x",
                }
            ],
        }
    )
    evidence = normalized_fixture_manifest(
        {
            "schema": 2,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "atoms": [
                {
                    "ref": "b/0",
                    "binder_info": "explicit",
                    "role": "parameter",
                    "canonical": nat,
                    "display": "x : Nat",
                },
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {
                        "tag": "app",
                        "fn": predicate_constant,
                        "arg": {"tag": "fvar", "index": "0"},
                    },
                    "display": "Fixture.P x",
                },
            ],
        }
    )
    return specification, evidence


def nontrivial_theorem_manifest() -> dict[str, object]:
    raw = {
        "schema": 2,
        "declaration_kind": "theorem",
        "conclusion_mode": "type_only",
        "atoms": [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {
                    "tag": "app",
                    "fn": {"tag": "const", "name": "Not", "levels": []},
                    "arg": {
                        "tag": "app",
                        "fn": {
                            "tag": "app",
                            "fn": {
                                "tag": "app",
                                "fn": {"tag": "const", "name": "Eq", "levels": []},
                                "arg": {"tag": "const", "name": "Nat", "levels": []},
                            },
                            "arg": {"tag": "lit", "kind": "nat", "value": "0"},
                        },
                        "arg": {"tag": "lit", "kind": "nat", "value": "1"},
                    },
                },
                "display": "0 != 1",
            }
        ],
    }
    return normalized_fixture_manifest(raw)


def proposition_inductive_manifest() -> dict[str, object]:
    return {
        "schema": 2,
        "declaration_kind": "inductive",
        "conclusion_mode": "type_only",
        "atoms": [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {
                    "tag": "inductive",
                    "type": {"tag": "sort", "level": {"tag": "zero"}},
                    "num_params": "0",
                    "num_indices": "0",
                    "constructors": [],
                },
                "display": "Prop",
            }
        ],
    }


class PropositionSpecAuditTests(unittest.TestCase):
    def test_v11_claim_surface_accepts_results_and_direct_definitions(self) -> None:
        status = {
            "review_surface": {
                "require_v11_raw_source_spec_screening": True,
                "include_names": ["resultSpec", "sourceDefinition"],
                "proposition_spec_proofs": {"resultSpec": "resultProof"},
                "source_definition_names": ["sourceDefinition"],
            }
        }

        self.assertEqual(
            audit_repository.v11_source_claim_review_names(status),
            frozenset({"resultSpec", "sourceDefinition"}),
        )

    def test_v11_claim_surface_defers_roles_to_typed_routes(self) -> None:
        status = {
            "review_surface": {
                "require_v11_raw_source_spec_screening": True,
                "include_names": ["resultSpec", "unrouted"],
                "proposition_spec_proofs": {"resultSpec": "resultProof"},
                "source_definition_names": [],
            }
        }

        self.assertEqual(
            audit_repository.v11_source_claim_review_names(status),
            frozenset({"resultSpec", "unrouted"}),
        )

    def test_v11_claim_surface_ignores_legacy_definition_vocabulary(self) -> None:
        status = {
            "review_surface": {
                "require_v11_raw_source_spec_screening": True,
                "include_names": ["resultSpec"],
                "proposition_spec_proofs": {"resultSpec": "resultProof"},
                "source_definition_names": ["notReviewed"],
            }
        }

        self.assertEqual(
            audit_repository.v11_source_claim_review_names(status),
            frozenset({"resultSpec"}),
        )

    def test_comment_stripper_preserves_nested_block_comment_semantics(self) -> None:
        source = (
            "namespace Outer /- first\n"
            "  /- nested -/ hidden -/\n"
            "theorem visible : True := by trivial -- trailing\n"
            "/- inline -/ lemma second : True := by trivial\n"
            "end Outer\n"
        )
        self.assertEqual(
            audit_repository.lean_code_lines_from_text(source),
            [
                (1, "namespace Outer "),
                (2, ""),
                (3, "theorem visible : True := by trivial "),
                (4, " lemma second : True := by trivial"),
                (5, "end Outer"),
            ],
        )
        self.assertEqual(
            audit_repository.lean_code_text(source),
            "namespace Outer \n\ntheorem visible : True := by trivial \n"
            " lemma second : True := by trivial\nend Outer",
        )

    def test_declaration_index_scans_namespace_state_once_per_file(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace Outer\n"
                "theorem first : True := by trivial\n"
                "namespace Inner\n"
                "def second : Prop := True\n"
                "end Inner\n"
                "end Outer\n"
                "namespace Other\n"
                "lemma third : True := by trivial\n"
                "end Other\n",
                encoding="utf-8",
            )
            original = audit_repository.lean_code_lines_from_text
            with mock.patch.object(
                audit_repository,
                "lean_code_lines_from_text",
                wraps=original,
            ) as code_lines:
                declarations = audit_repository.paper_lean_declaration_index(folder)

        self.assertEqual(code_lines.call_count, 1)
        self.assertIn("Outer.first", declarations)
        self.assertIn("Outer.Inner.second", declarations)
        self.assertIn("Other.third", declarations)

    def test_declaration_index_keeps_namespace_through_anonymous_section_end(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace Outer\n"
                "namespace Interface\n"
                "section\n"
                "local instance : Inhabited Nat := ⟨0⟩\n"
                "end\n"
                "abbrev reviewedSpec : Prop := True\n"
                "theorem reviewed : reviewedSpec := by trivial\n"
                "end Interface\n"
                "end Outer\n",
                encoding="utf-8",
            )
            declarations = audit_repository.paper_lean_declaration_index(folder)

        self.assertIn("Outer.Interface.reviewedSpec", declarations)
        self.assertIn("Outer.Interface.reviewed", declarations)
        self.assertNotIn("Outer.reviewedSpec", declarations)

    def test_thin_review_alias_requires_a_paper_local_proof_target(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            source = folder / "PaperInterface.lean"
            source.write_text(
                "namespace Example\n"
                "theorem proved_target : True := by trivial\n"
                "abbrev review_alias := @proved_target\n"
                "def review_predicate : Prop := True\n"
                "end Example\n",
                encoding="utf-8",
            )
            declarations = audit_repository.paper_lean_declaration_index(folder)
            alias = audit_repository.resolve_declaration_name(declarations, "review_alias")
            predicate = audit_repository.resolve_declaration_name(declarations, "review_predicate")

            self.assertEqual(len(alias), 1)
            self.assertEqual(len(predicate), 1)
            self.assertTrue(
                audit_repository.is_thin_review_alias_to_proved_theorem(
                    declarations, alias[0]
                )
            )
            self.assertFalse(
                audit_repository.is_thin_review_alias_to_proved_theorem(
                    declarations, predicate[0]
                )
            )

    def fixture(self, folder: Path) -> tuple[list[review_dashboard.ReviewItem], dict[str, object]]:
        (folder / "PaperInterface.lean").write_text(
            "namespace Example\n"
            "def spec : Prop := True\n"
            "theorem proof : spec := by trivial\n"
            "def notProof : Prop := True\n"
            "end Example\n",
            encoding="utf-8",
        )
        items = [
            review_dashboard.ReviewItem(
                name="spec",
                kind="def",
                lean_statement="def spec : Prop := True",
                paper_statement="spec",
                agent_statement="spec",
                lean_signature_manifest=proposition_spec_manifest(),
            ),
            review_dashboard.ReviewItem(
                name="proof",
                kind="theorem",
                lean_statement="theorem proof : spec",
                paper_statement="spec",
                agent_statement="spec",
                lean_signature_manifest=theorem_manifest(),
            ),
            review_dashboard.ReviewItem(
                name="notProof",
                kind="def",
                lean_statement="def notProof : Prop := True",
                paper_statement="spec",
                agent_statement="spec",
                lean_signature_manifest=proposition_spec_manifest(),
            ),
        ]
        review_surface: dict[str, object] = {
            "include_names": ["spec", "proof"],
            "assumption_names": [],
            "source_definition_names": [],
            "proposition_spec_proofs": {},
        }
        return items, review_surface

    def semantic_contract_coverage_fixture(
        self,
        *,
        evidence_predicate: str = "Fixture.P",
        evidence_is_proof: bool = True,
    ) -> tuple[
        dict[str, object],
        review_dashboard.ReviewItem,
        review_dashboard.ReviewItem,
        dict[str, review_dashboard.ReviewItem],
    ]:
        specification_manifest, _matching_evidence = semantic_contract_manifest_pair()
        if evidence_is_proof:
            _unused_specification, evidence_manifest = semantic_contract_manifest_pair(
                evidence_predicate
            )
            evidence_kind = "theorem"
        else:
            evidence_manifest = normalized_fixture_manifest(
                proposition_spec_manifest()
            )
            evidence_kind = "def"
        spec_declaration = "Fixture.PaperInterface.claimSpec"
        evidence_declaration = "Fixture.PaperInterface.claimProof"
        source_statement = "For every natural number x, P x holds."
        source_digest = review_dashboard.statement_digest(source_statement)
        source_location = "Fixture.txt:10-12"
        owner = review_dashboard.ReviewItem(
            name="claimSpec",
            full_name=spec_declaration,
            kind="def",
            lean_statement="def claimSpec : Prop := forall x : Nat, P x",
            paper_statement=source_statement,
            agent_statement=source_statement,
            lean_signature_manifest=specification_manifest,
            lean_signature_sha256=str(specification_manifest["sha256"]),
            is_proposition_spec=True,
            proposition_spec_role="proof_routed",
            proposition_spec_proof="claimProof",
            semantic_contract_lean_match_verified=True,
            semantic_contract_lean_transparency_verified=True,
            llm_match_judgment="matches",
            llm_match_source_routes=[
                {
                    "source_statement_sha256": source_digest,
                    "source_location": source_location,
                    "route_kind": "direct",
                }
            ],
        )
        evidence = review_dashboard.ReviewItem(
            name="claimProof",
            full_name=evidence_declaration,
            kind=evidence_kind,
            lean_statement="theorem claimProof (x : Nat) : P x",
            paper_statement=source_statement,
            agent_statement=source_statement,
            lean_signature_manifest=evidence_manifest,
            lean_signature_sha256=str(evidence_manifest["sha256"]),
        )
        source_item: dict[str, object] = {
            "source_kind": "theorem",
            "statement": source_statement,
            "statement_sha256": source_digest,
            "source_location": source_location,
            "lean_declarations": [evidence_declaration],
            "semantic_contract": {
                "spec_declaration": spec_declaration,
                "evidence_declaration": evidence_declaration,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        rows = {owner.name: owner, evidence.name: evidence}
        return source_item, owner, evidence, rows

    def test_coverage_spec_owner_uses_exact_proved_lean_contract(self) -> None:
        source_item, owner, evidence, rows = self.semantic_contract_coverage_fixture()

        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertEqual(error, "")
        self.assertIs(resolved, evidence)
        credited, credit_error = review_dashboard._coverage_proof_evidence_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertEqual(credit_error, "")
        self.assertIs(credited, evidence)
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "opaque_source_identity",
                source_item,
                owner,
                row_items=rows,
                semantic_contract_schema=1,
            ),
            "",
        )

    def test_current_v11_root_owns_recursive_closure_once(self) -> None:
        """Coverage reuses v11 closure but still checks the exact Spec root."""

        source_item, owner, evidence, rows = self.semantic_contract_coverage_fixture()
        manifest = json.loads(json.dumps(owner.lean_signature_manifest))
        dependency_graph = manifest["semantic_dependency_graph"]
        dependency_graph["complete"] = False
        dependency_graph["realization_complete"] = False
        dependency_graph["failures"] = [
            {"tag": "historical_schema2_closure_failure"}
        ]
        manifest.pop("sha256", None)
        manifest["sha256"] = review_dashboard.signature_manifest_digest(manifest)
        owner.lean_signature_manifest = manifest
        owner.lean_signature_sha256 = str(manifest["sha256"])
        owner.llm_match_source = Path(
            review_dashboard.V11_RAW_SOURCE_SPEC_SCREENING_FILE
        ).name
        owner.llm_match_stale = False

        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertEqual(error, "")
        self.assertIs(resolved, evidence)

        # Without a current v11 transaction, the legacy row must still own its
        # complete recursive dependency receipt and therefore fails closed.
        owner.llm_match_source = "legacy_review.json"
        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertIsNone(resolved)
        self.assertIn("proposition/dependency receipt", error)

    def test_definition_coverage_accepts_exact_definitionally_realized_spec(self) -> None:
        source_item, owner, evidence, rows = self.semantic_contract_coverage_fixture()
        source_item["source_kind"] = "definition"
        source_item["semantic_contract"]["evidence_mode"] = (
            "definitionally_realizes"
        )

        self.assertEqual(
            review_dashboard._definitionally_realized_spec_coverage_error(
                source_item,
                owner,
                semantic_contract_schema=1,
            ),
            "",
        )
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "opaque_source_identity",
                source_item,
                owner,
                row_items=rows,
                semantic_contract_schema=1,
            ),
            "",
        )

    def test_dashboard_attaches_batched_lean_contract_verdicts(self) -> None:
        _source_item, owner, evidence, _rows = self.semantic_contract_coverage_fixture()
        owner.semantic_contract_lean_match_verified = None
        owner.semantic_contract_lean_transparency_verified = None
        route = (owner.full_name, evidence.full_name, "proves")
        with (
            mock.patch.object(
                review_dashboard,
                "review_source_module",
                return_value="Fixture.PaperInterface",
            ),
            mock.patch.object(
                review_dashboard,
                "paper_owned_module_names_in_import_closure",
                return_value=("Fixture.PaperInterface",),
            ),
            mock.patch.object(
                review_dashboard,
                "run_lean_semantic_contract_matches",
                return_value={route: True},
            ) as matches,
            mock.patch.object(
                review_dashboard,
                "run_lean_semantic_contract_transparency_checks",
                return_value={owner.full_name: {"passes": True}},
            ) as transparency,
        ):
            review_dashboard.attach_current_lean_semantic_contract_results(
                Path("Fixture"),
                Path("Fixture/PaperInterface.lean"),
                [owner, evidence],
                build_input_provider=mock.Mock(),
            )

        self.assertTrue(owner.semantic_contract_lean_match_verified)
        self.assertTrue(owner.semantic_contract_lean_transparency_verified)
        self.assertEqual(matches.call_args.args[2], [route])
        self.assertEqual(transparency.call_args.args[2], [owner.full_name])

    def test_dashboard_attaches_definitional_source_contract_verdict(self) -> None:
        _source_item, owner, evidence, _rows = self.semantic_contract_coverage_fixture()
        owner.proposition_spec_role = "unproved_spec"
        owner.proposition_spec_proof = ""
        route = (owner.full_name, evidence.full_name, "definitionally_realizes")
        source_map = {
            "items": {
                "source_definition": {
                    "semantic_contract": {
                        "spec_declaration": owner.full_name,
                        "evidence_declaration": evidence.full_name,
                        "evidence_mode": "definitionally_realizes",
                        "semantic_shape": "plain",
                    }
                }
            }
        }
        with (
            mock.patch.object(
                review_dashboard,
                "paper_statement_map_payload",
                return_value=source_map,
            ),
            mock.patch.object(
                review_dashboard,
                "review_source_module",
                return_value="Fixture.PaperInterface",
            ),
            mock.patch.object(
                review_dashboard,
                "paper_owned_module_names_in_import_closure",
                return_value=("Fixture.PaperInterface",),
            ),
            mock.patch.object(
                review_dashboard,
                "run_lean_semantic_contract_matches",
                return_value={route: True},
            ) as matches,
            mock.patch.object(
                review_dashboard,
                "run_lean_semantic_contract_transparency_checks",
                return_value={owner.full_name: {"passes": True}},
            ),
        ):
            review_dashboard.attach_current_lean_semantic_contract_results(
                Path("Fixture"),
                Path("Fixture/PaperInterface.lean"),
                [owner],
                build_input_provider=mock.Mock(),
            )

        self.assertTrue(owner.semantic_contract_lean_match_verified)
        self.assertTrue(owner.semantic_contract_lean_transparency_verified)
        self.assertEqual(matches.call_args.args[2], [route])

    def test_dashboard_routes_hidden_proof_relative_to_spec_namespace(self) -> None:
        """An excluded proof still receives Lean-Meta credit at its exact name."""

        _source_item, owner, evidence, _rows = self.semantic_contract_coverage_fixture()
        owner.semantic_contract_lean_match_verified = None
        owner.semantic_contract_lean_transparency_verified = None
        route = (owner.full_name, evidence.full_name, "proves")
        with (
            mock.patch.object(
                review_dashboard,
                "review_source_module",
                return_value="Fixture.PaperInterface",
            ),
            mock.patch.object(
                review_dashboard,
                "paper_owned_module_names_in_import_closure",
                return_value=("Fixture.PaperInterface",),
            ),
            mock.patch.object(
                review_dashboard,
                "run_lean_semantic_contract_matches",
                return_value={route: True},
            ) as matches,
            mock.patch.object(
                review_dashboard,
                "run_lean_semantic_contract_transparency_checks",
                return_value={owner.full_name: {"passes": True}},
            ),
        ):
            review_dashboard.attach_current_lean_semantic_contract_results(
                Path("Fixture"),
                Path("Fixture/PaperInterface.lean"),
                [owner],
                build_input_provider=mock.Mock(),
            )

        self.assertTrue(owner.semantic_contract_lean_match_verified)
        self.assertTrue(owner.semantic_contract_lean_transparency_verified)
        self.assertEqual(matches.call_args.args[2], [route])

    def test_coverage_spec_owner_credits_configured_hidden_proof(self) -> None:
        """A v11 Spec card need not duplicate its paired proof as a review row."""

        source_item, owner, evidence, _rows = self.semantic_contract_coverage_fixture()
        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            {owner.name: owner},
            semantic_contract_schema=1,
        )

        self.assertEqual(error, "")
        self.assertIsNotNone(resolved)
        assert resolved is not None
        self.assertEqual(resolved.full_name, evidence.full_name)
        self.assertEqual(resolved.kind, "theorem")
        self.assertNotEqual(resolved.name, owner.name)
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "opaque_source_identity",
                source_item,
                owner,
                row_items={owner.name: owner},
                semantic_contract_schema=1,
            ),
            "",
        )

    def test_coverage_spec_owner_uses_lean_verdict_not_python_telescope(self) -> None:
        source_item, owner, _evidence, rows = self.semantic_contract_coverage_fixture(
            evidence_predicate="Fixture.Q"
        )

        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertIsNotNone(resolved)
        self.assertEqual(error, "")

    def test_coverage_spec_owner_rejects_failed_lean_contract(self) -> None:
        source_item, owner, _evidence, rows = self.semantic_contract_coverage_fixture()
        owner.semantic_contract_lean_match_verified = False

        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertIsNone(resolved)
        self.assertIn("Lean Meta did not establish", error)

    def test_coverage_spec_owner_rejects_failed_lean_transparency(self) -> None:
        source_item, owner, _evidence, rows = self.semantic_contract_coverage_fixture()
        owner.semantic_contract_lean_transparency_verified = False

        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertIsNone(resolved)
        self.assertIn("transparency proof", error)

    def test_coverage_spec_owner_rejects_absent_semantic_contract(self) -> None:
        source_item, owner, _evidence, rows = self.semantic_contract_coverage_fixture()
        source_item.pop("semantic_contract")

        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertIsNone(resolved)
        self.assertIn("no explicit Spec/evidence semantic contract", error)

    def test_coverage_spec_owner_rejects_nonproof_evidence(self) -> None:
        source_item, owner, _evidence, rows = self.semantic_contract_coverage_fixture(
            evidence_is_proof=False
        )

        resolved, error = review_dashboard._semantic_contract_spec_coverage_proof_row(
            source_item,
            owner,
            rows,
            semantic_contract_schema=1,
        )
        self.assertIsNone(resolved)
        self.assertIn("not an actual proved theorem", error)

    def run_gate(
        self,
        folder: Path,
        items: list[review_dashboard.ReviewItem],
        review_surface: dict[str, object],
        *,
        meta_results: dict[tuple[str, str], bool] | None = None,
    ) -> list[audit_repository.Finding]:
        include_names = list(review_surface["include_names"])
        with (
            mock.patch.object(
                review_dashboard, "review_items_for_paper", return_value=items
            ),
            mock.patch.object(
                lean_signature_manifest,
                "run_lean_proposition_spec_proof_matches",
                return_value=meta_results or {},
            ),
        ):
            return audit_repository.check_proposition_spec_routes(
                "Example",
                folder,
                review_surface,
                include_names,
                set(),
                "formalized",
                paper_closeout=False,
            )

    def test_diagnostic_rejects_unproved_uncertified_and_missing_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            items, surface = self.fixture(folder)
            findings = self.run_gate(folder, items, surface)
            self.assertTrue(any("unproved proposition specification" in f.message for f in findings))

            surface["source_definition_names"] = ["spec"]
            findings = self.run_gate(folder, items, surface)
            self.assertTrue(any("without pinned bytes" in f.message for f in findings))

            surface["source_definition_names"] = []
            surface["proposition_spec_proofs"] = {"spec": "proof"}
            surface["include_names"] = ["spec"]
            findings = self.run_gate(folder, items, surface)
            self.assertTrue(
                any("Lean Meta did not establish" in f.message for f in findings)
            )

    def test_diagnostic_uses_lean_meta_type_equality_and_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            items, surface = self.fixture(folder)
            surface["proposition_spec_proofs"] = {"spec": "proof"}
            route = ("Example.spec", "Example.proof")
            wrong = self.run_gate(folder, items, surface, meta_results={route: False})
            self.assertTrue(any("Lean Meta did not establish" in f.message for f in wrong))

            absent = self.run_gate(folder, items, surface, meta_results={})
            self.assertTrue(any("Lean Meta did not establish" in f.message for f in absent))

            exact = self.run_gate(folder, items, surface, meta_results={route: True})
            self.assertEqual(exact, [])

    def test_closeout_rejects_parser_and_per_pair_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            items, surface = self.fixture(folder)
            findings = audit_repository.check_proposition_spec_routes(
                "Example",
                folder,
                surface,
                list(surface["include_names"]),
                set(),
                "formalized",
                paper_closeout=True,
                review_items_provider=lambda: tuple(items),
            )
        self.assertTrue(
            any("diagnostic only" in finding.message for finding in findings)
        )

    def test_current_v11_closeout_checks_typed_graph_without_dashboard(
        self,
    ) -> None:
        """Current v11 checks each typed relation without presentation replay."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            _items, surface = self.fixture(folder)
            surface["include_names"] = ["spec"]
            surface["proposition_spec_proofs"] = {
                "spec": "proof",
                "internalSpec": "internalProof",
            }
            source_item = {
                "semantic_contract": {
                    "spec_declaration": "Example.spec",
                    "evidence_declaration": "Example.proof",
                    "evidence_mode": "proves",
                    "semantic_shape": "plain",
                }
            }
            source_map = {"items": {"source_claim": source_item}}
            status_payload = {"review_surface": surface}
            receipt = audit_repository.StrictSourceSpecCorrespondenceReceipt(
                source_item_key="source_claim",
                spec_declaration="Example.spec",
                evidence_declaration="Example.proof",
                evidence_mode="proves",
                semantic_shape="plain",
                source_atoms_sha256="1" * 64,
                item_identity_sha256="2" * 64,
                spec_closure_sha256="3" * 64,
                spec_surface_sha256="4" * 64,
                closure_environment_sha256="5" * 64,
            )
            context = mock.Mock()
            context.issued_by_builder = True
            context.selected_v11_closeout = True
            context.current_v11_closeout = True
            context.v11_direct_semantic_review_current = True
            context.exact_json_payload.side_effect = lambda path: (
                source_map if path.name == "paper_statement_map.json" else status_payload
            )
            context.paper_declaration_index.return_value = (
                typed_fixture_declaration_index(
                    folder,
                    {"Example.spec": "def", "Example.proof": "theorem"},
                )
            )
            context.v11_lean_review_surface = mock.Mock(
                semantic_contracts={
                    ("Example.spec", "Example.proof", "proves"): {
                        "specification": "Example.spec",
                        "evidence": "Example.proof",
                        "mode": "proves",
                        "matches": True,
                    }
                }
            )
            context.current_strict_source_spec_correspondence_receipts.return_value = (
                receipt,
            )
            context.current_strict_source_spec_correspondence_scope_keys.return_value = (
                "source_claim",
            )
            context.current_v11_primary_gate_result.return_value = mock.Mock(
                proof_errors=()
            )
            review_items = mock.Mock(
                side_effect=AssertionError("direct v11 proof check should avoid dashboard replay")
            )
            with (
                mock.patch.object(
                    audit_repository,
                    "v11_source_claim_review_names",
                    return_value={"spec"},
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "run_lean_proposition_spec_proof_matches",
                    side_effect=AssertionError("retained graph should own proof equality"),
                ) as direct_lean,
            ):
                findings = audit_repository.check_proposition_spec_routes(
                    "Example",
                    folder,
                    surface,
                    ["spec"],
                    set(),
                    "formalized",
                    paper_closeout=True,
                    review_items_provider=review_items,
                    run_context=context,
                )

            self.assertEqual(findings, [])
            review_items.assert_not_called()
            direct_lean.assert_not_called()

    def test_current_v11_axiom_gate_consumes_spec_and_proof_graph_rows(self) -> None:
        """One retained graph owns both semantic-root and endpoint proof debt."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            _items, surface = self.fixture(folder)
            surface["include_names"] = ["spec"]
            surface["proposition_spec_proofs"] = {"spec": "proof"}
            declarations = typed_fixture_declaration_index(
                folder,
                {"Example.spec": "def", "Example.proof": "theorem"},
            )
            source_map = {
                "items": {
                    "source_claim": {
                        "semantic_contract": {
                            "spec_declaration": "Example.spec",
                            "evidence_declaration": "Example.proof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        }
                    }
                }
            }
            context = mock.Mock()
            context.paper_declaration_index.return_value = declarations
            context.exact_json_payload.return_value = source_map
            context.v11_lean_review_surface = mock.Mock(
                declaration_inventory={
                    "declarations": [
                        {
                            "declaration": "Example.spec",
                            "axiom_closure_checked": True,
                            "axiom_closure": [],
                            "is_unsafe": False,
                            "value_has_sorry": False,
                        }
                    ]
                },
                semantic_contracts={
                    ("Example.spec", "Example.proof", "proves"): {
                        "specification": "Example.spec",
                        "evidence": "Example.proof",
                        "mode": "proves",
                        "matches": True,
                        "evidence_axiom_closure_checked": True,
                        "evidence_axiom_closure": ["Example.unapproved"],
                        "evidence_is_unsafe": False,
                        "evidence_value_has_sorry": False,
                    }
                },
            )
            context.current_v11_primary_gate_result.return_value = mock.Mock(
                axiom_errors=(
                    "`Example` Lean declaration `proof` depends on unapproved "
                    "axiom(s): Example.unapproved",
                )
            )

            findings = audit_repository.current_v11_direct_axiom_closure_findings(
                "Example",
                folder,
                surface,
                ["spec"],
                set(),
                run_context=context,
            )

            self.assertEqual(len(findings), 1)
            self.assertIn("Example.unapproved", findings[0].message)

    def test_current_v11_direct_definition_has_no_fake_proof_obligation(self) -> None:
        """A source definition is checked as its exact declaration, once."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            _items, surface = self.fixture(folder)
            surface["include_names"] = ["notProof"]
            # A stale presentation mapping must not turn the definition into
            # an alias-equivalence proof obligation.
            surface["proposition_spec_proofs"] = {"notProof": "proof"}
            source_map = {
                "items": {
                    "source_definition": {
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                        "lean_declarations": ["Example.notProof"],
                    }
                }
            }
            context = mock.Mock()
            context.paper_declaration_index.return_value = (
                typed_fixture_declaration_index(
                    folder,
                    {
                        "Example.notProof": "def",
                        "Example.proof": "theorem",
                    },
                )
            )
            context.exact_json_payload.return_value = source_map
            context.v11_lean_review_surface = mock.Mock(
                declaration_inventory={
                    "declarations": [
                        {
                            "declaration": "Example.notProof",
                            "axiom_closure_checked": True,
                            "axiom_closure": [],
                            "is_unsafe": False,
                            "value_has_sorry": False,
                        }
                    ]
                },
                semantic_contracts={},
            )
            context.current_v11_primary_gate_result.return_value = mock.Mock(
                proof_errors=(),
                axiom_errors=(),
            )

            proof_findings = audit_repository.current_v11_direct_proof_pair_findings(
                "Example",
                folder,
                surface,
                surface["proposition_spec_proofs"],
                {"notProof"},
                run_context=context,
            )
            axiom_findings = audit_repository.current_v11_direct_axiom_closure_findings(
                "Example",
                folder,
                surface,
                ["notProof"],
                set(),
                run_context=context,
            )

            self.assertEqual(proof_findings, [])
            self.assertEqual(axiom_findings, [])

    def test_prop_structure_is_a_specification_until_routed_to_a_theorem(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace Example\n"
                "structure Claim : Prop where\n"
                "  evidence : True\n"
                "theorem claimProof : Claim := by exact Claim.mk True.intro\n"
                "end Example\n",
                encoding="utf-8",
            )
            items = [
                review_dashboard.ReviewItem(
                    name="Claim",
                    kind="structure",
                    lean_statement="structure Claim : Prop",
                    paper_statement="claim",
                    agent_statement="claim",
                    lean_signature_manifest=proposition_inductive_manifest(),
                ),
                review_dashboard.ReviewItem(
                    name="claimProof",
                    kind="theorem",
                    lean_statement="theorem claimProof : Claim",
                    paper_statement="claim",
                    agent_statement="claim",
                    lean_signature_manifest=theorem_manifest(),
                ),
            ]
            surface: dict[str, object] = {
                "include_names": ["Claim", "claimProof"],
                "assumption_names": [],
                "source_definition_names": [],
                "proposition_spec_proofs": {},
            }
            unproved = self.run_gate(folder, items, surface)
            self.assertTrue(
                any("unproved proposition specification" in finding.message for finding in unproved)
            )
            surface["proposition_spec_proofs"] = {"Claim": "claimProof"}
            route = ("Example.Claim", "Example.claimProof")
            proved = self.run_gate(
                folder, items, surface, meta_results={route: True}
            )
            self.assertEqual(proved, [])

    def test_certified_pinned_source_definition_is_not_treated_as_a_proof(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            items, surface = self.fixture(folder)
            artifact = folder / "source-audited.txt"
            artifact.write_text("Definition 1. Let spec be true.\n", encoding="utf-8")
            digest = hashlib.sha256(artifact.read_bytes()).hexdigest()
            audit = folder / "audit"
            audit.mkdir()
            source_map = {
                        "source_curated": True,
                        "seed_scaffold": False,
                        "source_curator": "source-curator",
                        "source_curated_at": "2026-07-10T10:00:00Z",
                        "source_artifact_path": artifact.name,
                        "source_artifact_sha256": digest,
                        "items": {
                            "definition_1": {
                                "source_kind": "definition",
                                "source_kind_validator": "source-kind-judge",
                                "source_kind_validated_at": "2026-07-10T11:00:00Z",
                                "source_kind_human_approved": True,
                                "source_kind_human_reviewer": "human-reviewer",
                                "source_kind_human_reviewed_at": "2026-07-10T12:00:00Z",
                                "source_location": "Definition 1, p. 2",
                                "lean_declarations": ["spec"],
                            }
                        },
                    }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(
                json.dumps(source_map),
                encoding="utf-8",
            )
            surface["source_definition_names"] = ["spec"]
            self.assertEqual(self.run_gate(folder, items, surface), [])

            del source_map["items"]["definition_1"]["source_kind_human_approved"]
            map_path.write_text(json.dumps(source_map), encoding="utf-8")
            findings = self.run_gate(folder, items, surface)
            self.assertTrue(any("human-approved" in f.message for f in findings))

            source_map["items"]["definition_1"]["source_kind_human_approved"] = True
            map_path.write_text(json.dumps(source_map), encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps({"formalizer": "human-reviewer"}), encoding="utf-8"
            )
            findings = self.run_gate(folder, items, surface)
            self.assertTrue(any("human-approved" in f.message for f in findings))

    def test_curated_definition_wording_stays_on_translation_lane(self) -> None:
        """Source-kind semantics outrank incidental result-like definition prose."""

        for source_kind in ("definition", "predicate_vocabulary"):
            item = {
                "source": review_dashboard.PAPER_STATEMENT_MAP_FILE,
                "source_kind": source_kind,
                "claim_bearing": True,
                "statement": (
                    "The definition specifies a mechanism that is optimal on every legal "
                    "profile."
                ),
            }
            self.assertTrue(
                review_dashboard._source_text_has_general_result_assertion(
                    item["statement"]
                )
            )
            self.assertFalse(
                review_dashboard._source_inventory_item_requires_proof_evidence(
                    "arbitrary_navigation_key",
                    item,
                )
            )

    def test_explicit_named_source_support_is_not_a_second_direct_proof_obligation(self) -> None:
        item = {
            "source": review_dashboard.PAPER_STATEMENT_MAP_FILE,
            "source_kind": "lemma",
            "source_status": "support_only",
            "claim_bearing": True,
            "statement": "The named intermediate lemma supplies a source proof step.",
        }
        self.assertFalse(
            review_dashboard._source_inventory_item_requires_proof_evidence(
                "source_support", item
            )
        )

    def test_theorem_like_source_item_requires_reviewed_theorem_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            self.fixture(folder)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["notProof", "proof"],
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            statement_map = audit / "paper_statement_map.json"

            def findings_for(
                routed_name: str, source_kind: str | None = "theorem"
            ) -> list[audit_repository.Finding]:
                source_item: dict[str, object] = {
                    "lean_declarations": [routed_name]
                }
                if source_kind is not None:
                    source_item["source_kind"] = source_kind
                if source_kind == "theorem":
                    source_item["title"] = "Theorem 2. Fixture result"
                statement_map.write_text(
                    json.dumps(
                        {
                            "items": {
                                "theorem_2": source_item
                            }
                        }
                    ),
                    encoding="utf-8",
                )
                with mock.patch.object(
                    audit_repository, "library_lean_declaration_index", return_value={}
                ):
                    return audit_repository.paper_statement_map_declaration_findings(
                        "Example", folder, "formalized"
                    )

            definition_route = findings_for("notProof")
            self.assertTrue(
                any("do not route to a unique reviewed Lean theorem" in f.message for f in definition_route)
            )
            theorem_route = findings_for("proof")
            self.assertFalse(
                any("do not route to a unique reviewed Lean theorem" in f.message for f in theorem_route)
            )
            missing_kind = findings_for("notProof", None)
            self.assertTrue(
                any("omit required `source_kind`" in f.message for f in missing_kind)
            )
            unknown_kind = findings_for("notProof", "theorm")
            self.assertTrue(
                any("unknown `source_kind`" in f.message for f in unknown_kind)
            )
            condition_kind = findings_for("notProof", "condition")
            self.assertFalse(
                any("unknown `source_kind`" in f.message for f in condition_kind)
            )

    def test_direct_result_routes_follow_semantic_source_scope(self) -> None:
        """An unlabelled proof step is ordinary support, not a named result."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            self.fixture(folder)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["proof"],
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            statement_map = audit / "paper_statement_map.json"

            def findings_for(
                mode: str,
                *,
                title: str | None = None,
                correction_field: str | None = None,
            ) -> list[audit_repository.Finding]:
                item: dict[str, object] = {
                    "source_kind": "claim",
                    "statement": (
                        "The proof next observes an intermediate inequality before "
                        "establishing the named theorem."
                    ),
                    "lean_declarations": ["Missing.intermediate"],
                }
                if title is not None:
                    item["title"] = title
                if correction_field is not None:
                    item[correction_field] = "corrected_source_statement"
                statement_map.write_text(
                    json.dumps(
                        {
                            "source_coverage_mode": mode,
                            "items": {"opaque_navigation_key": item},
                        }
                    ),
                    encoding="utf-8",
                )
                with mock.patch.object(
                    audit_repository, "library_lean_declaration_index", return_value={}
                ):
                    return audit_repository.paper_statement_map_declaration_findings(
                        "Example", folder, "formalized"
                    )

            def direct_route_messages(
                findings: list[audit_repository.Finding],
            ) -> list[str]:
                return [
                    finding.message
                    for finding in findings
                    if "do not route to a unique reviewed Lean theorem" in finding.message
                    or "Lean declaration(s) that do not resolve" in finding.message
                ]

            ordinary = findings_for("named_theoretical_statements")
            self.assertEqual(direct_route_messages(ordinary), [])

            deep = findings_for("deep_paper_with_all_prose_claims")
            self.assertTrue(direct_route_messages(deep), [f.message for f in deep])

            named = findings_for(
                "named_theoretical_statements",
                title="Claim 7. Intermediate inequality",
            )
            self.assertTrue(direct_route_messages(named), [f.message for f in named])

            for correction_field in ("coverage_status", "source_status"):
                corrected = findings_for(
                    "named_theoretical_statements",
                    correction_field=correction_field,
                )
                self.assertTrue(
                    direct_route_messages(corrected),
                    [f.message for f in corrected],
                )

    def test_result_proof_routes_use_declaration_kind_and_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace First\n"
                "theorem firstEndpoint : True := True.intro\n"
                "end First\n"
                "namespace Second\n"
                "theorem endpoint : True := True.intro\n"
                "def vocabulary : Prop := True\n"
                "abbrev shorthand : Prop := True\n"
                "end Second\n",
                encoding="utf-8",
            )
            (folder / "Other.lean").write_text(
                "namespace Second\n"
                "theorem endpoint : True := True.intro\n"
                "def vocabulary : Prop := True\n"
                "abbrev shorthand : Prop := True\n"
                "end Second\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": [
                                "First.firstEndpoint",
                                "Second.vocabulary",
                                "Second.shorthand",
                            ],
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            statement_map = audit / "paper_statement_map.json"

            def findings_for(item: dict[str, object]) -> list[audit_repository.Finding]:
                item = dict(item)
                title_prefix = {
                    "runtime_claim": "Claim",
                    "claim": "Claim",
                    "theorem": "Theorem",
                    "lemma": "Lemma",
                    "corollary": "Corollary",
                }.get(str(item.get("source_kind") or ""))
                if title_prefix is not None:
                    item.setdefault("title", f"{title_prefix} 1. Fixture result")
                statement_map.write_text(
                    json.dumps({"items": {"opaque_source_item": item}}),
                    encoding="utf-8",
                )
                with mock.patch.object(
                    audit_repository, "library_lean_declaration_index", return_value={}
                ):
                    return audit_repository.paper_statement_map_declaration_findings(
                        "Example", folder, "formalized"
                    )

            invalid_explicit_proof = findings_for(
                {
                    "source_kind": "claim",
                    "protocol_role": "runtime_claim",
                    "lean_declarations": ["First.firstEndpoint"],
                    "proof_lean_declarations": ["Second.vocabulary"],
                }
            )
            self.assertTrue(
                any(
                    "proof_lean_declarations` must each resolve" in finding.message
                    for finding in invalid_explicit_proof
                )
            )
            self.assertFalse(
                any("unknown `source_kind`" in finding.message for finding in invalid_explicit_proof)
            )

            qualified_name_collision = findings_for(
                {
                    "source_kind": "theorem",
                    "proof_lean_declarations": ["Second.endpoint"],
                }
            )
            self.assertTrue(
                any(
                    "do not route to a unique reviewed Lean theorem" in finding.message
                    for finding in qualified_name_collision
                )
            )

            missing_qualified_route = findings_for(
                {
                    "source_kind": "lemma",
                    "proof_lean_declarations": ["Missing.endpoint"],
                }
            )
            self.assertTrue(
                any(
                    "Missing.endpoint:unresolved" in finding.message
                    for finding in missing_qualified_route
                )
            )

            valid_explicit_proof = findings_for(
                {
                    "source_kind": "corollary",
                    "proof_lean_declarations": ["First.firstEndpoint"],
                }
            )
            self.assertFalse(
                any(
                    "proof_lean_declarations` must each resolve" in finding.message
                    or "do not route to a unique reviewed Lean theorem" in finding.message
                    for finding in valid_explicit_proof
                )
            )

            vocabulary = findings_for(
                {
                    "source_kind": "predicate_vocabulary",
                    "lean_declarations": ["Second.shorthand"],
                }
            )
            self.assertFalse(
                any("unknown `source_kind`" in finding.message for finding in vocabulary)
            )
            self.assertFalse(
                any("do not route to a unique reviewed Lean theorem" in finding.message
                    for finding in vocabulary)
            )

    def test_short_review_name_prefers_configured_paper_interface_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace PaperSurface\n"
                "theorem endpoint : True := True.intro\n"
                "end PaperSurface\n",
                encoding="utf-8",
            )
            (folder / "AuditInterface.lean").write_text(
                "namespace LegacyAudit\n"
                "theorem endpoint : True := True.intro\n"
                "end LegacyAudit\n",
                encoding="utf-8",
            )
            (folder / "Assumptions.lean").write_text("", encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "source_file": str(folder / "PaperInterface.lean"),
                            "assumption_source_file": str(folder / "Assumptions.lean"),
                            "include_names": ["endpoint"],
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_theorem": {
                                "source_kind": "theorem",
                                "lean_declarations": ["PaperSurface.endpoint"],
                                "proof_lean_declarations": ["PaperSurface.endpoint"],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                audit_repository, "library_lean_declaration_index", return_value={}
            ):
                findings = audit_repository.paper_statement_map_declaration_findings(
                    "Example", folder, "formalized"
                )
            self.assertFalse(
                any(
                    "proof_lean_declarations` must each resolve" in finding.message
                    or "do not route to a unique reviewed Lean theorem" in finding.message
                    for finding in findings
                ),
                [finding.message for finding in findings],
            )

    def test_coverage_credit_requires_proof_rows_for_result_items(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OpaquePaper"
            folder.mkdir()
            audit = folder / "audit"
            audit.mkdir()
            statement = "A source-facing semantic assertion."
            map_items: dict[str, dict[str, object]] = {
                "opaque_legacy": {
                    "title": "Theorem 1: Source-facing semantic assertion",
                    "statement": statement,
                    "source_kind": "theorem",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "p. 1",
                },
                "opaque_runtime": {
                    "title": "Claim 2: Runtime guarantee",
                    "statement": statement,
                    "source_kind": "claim",
                    "protocol_role": "runtime_claim",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "p. 2",
                },
                "opaque_vocabulary": {
                    "statement": statement,
                    "source_kind": "predicate_vocabulary",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "p. 3",
                },
                "opaque_definition": {
                    "statement": statement,
                    "source_kind": "definition",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "p. 4",
                },
                "opaque_claim_bearing_spec": {
                    "title": "Claim 4: Source-facing property",
                    "statement": statement,
                    "source_kind": "claim",
                    "claim_bearing": True,
                    "lean_declarations": ["opaqueProofRow"],
                    "source_url": "https://example.invalid/paper",
                    "source_location": "p. 4",
                },
                "opaque_proved": {
                    "statement": statement,
                    "source_kind": "theorem",
                    "lean_declarations": ["opaqueProofRow"],
                    "source_url": "https://example.invalid/paper",
                    "source_location": "p. 5",
                },
                "opaque_mixed_match": {
                    "title": "Claim 6: Source-facing property",
                    "statement": statement,
                    "source_kind": "claim",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "p. 6",
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": map_items,
                    }
                ),
                encoding="utf-8",
            )
            paper_digest = review_dashboard.statement_digest(statement)
            rows = [
                review_dashboard.ReviewItem(
                    name="opaqueDefRow",
                    kind="def",
                    lean_statement="def opaqueDefRow : Prop := True",
                    paper_statement=statement,
                    agent_statement=statement,
                    llm_match_judgment="matches",
                    llm_match_paper_statement_sha256=paper_digest,
                ),
                review_dashboard.ReviewItem(
                    name="opaqueAbbrevRow",
                    kind="abbrev",
                    lean_statement="abbrev opaqueAbbrevRow : Prop := True",
                    paper_statement=statement,
                    agent_statement=statement,
                    llm_match_judgment="matches",
                    llm_match_paper_statement_sha256=paper_digest,
                ),
                review_dashboard.ReviewItem(
                    name="opaqueProofRow",
                    kind="theorem",
                    lean_statement="theorem opaqueProofRow : True",
                    paper_statement=statement,
                    agent_statement=statement,
                    llm_match_judgment="matches",
                    llm_match_paper_statement_sha256=paper_digest,
                ),
                review_dashboard.ReviewItem(
                    name="opaqueUnmatchedProofRow",
                    kind="theorem",
                    lean_statement="theorem opaqueUnmatchedProofRow : True",
                    paper_statement=statement,
                    agent_statement=statement,
                    llm_match_paper_statement_sha256=paper_digest,
                ),
            ]
            linked_rows = {
                "opaque_legacy": "opaqueDefRow",
                "opaque_runtime": "opaqueAbbrevRow",
                "opaque_vocabulary": "opaqueDefRow",
                "opaque_definition": "opaqueAbbrevRow",
                "opaque_claim_bearing_spec": "opaqueDefRow",
                "opaque_proved": "opaqueProofRow",
            }
            inventory = review_dashboard.paper_statement_inventory(folder)
            coverage_items = {
                key: {
                    "coverage": "covered",
                    "review_rows": [row],
                    "reason": "Semantic source-to-row comparison.",
                    "source_evidence": "Pinned source span.",
                    "statement_sha256": inventory[key]["statement_sha256"],
                    "validator": "independent-test-agent",
                    "validated_at": "2026-07-15T12:00:00Z",
                }
                for key, row in linked_rows.items()
            }
            coverage_items["opaque_mixed_match"] = {
                "coverage": "covered",
                "review_rows": ["opaqueDefRow", "opaqueUnmatchedProofRow"],
                "reason": "Semantic source-to-row comparison.",
                "source_evidence": "Pinned source span.",
                "statement_sha256": inventory["opaque_mixed_match"]["statement_sha256"],
                "validator": "independent-test-agent",
                "validated_at": "2026-07-15T12:00:00Z",
            }
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "independent-test-agent",
                        "validated_at": "2026-07-15T12:00:00Z",
                        "items": coverage_items,
                    }
                ),
                encoding="utf-8",
            )

            summary = review_dashboard.paper_coverage_audit_summary(folder, rows)
            expected_rejected = [
                "opaque_legacy",
                "opaque_runtime",
                "opaque_claim_bearing_spec",
            ]
            self.assertEqual(
                summary["result_covered_without_proof_rows"], expected_rejected
            )
            self.assertEqual(
                summary["result_covered_only_by_definition_rows"], expected_rejected
            )
            self.assertEqual(
                summary["result_matched_only_by_definition_rows"],
                [*expected_rejected, "opaque_mixed_match"],
            )
            self.assertTrue(summary["source_to_lean_needs_attention"])
            parsed_statements = review_dashboard.parse_paper_statement_map(folder)
            self.assertEqual(parsed_statements["opaqueProofRow"], statement)

    def test_nonformal_computational_observation_scope_is_source_based(self) -> None:
        """Only source-presented observations may be scoped out of theorem review."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ComputationalScopePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_artifact = folder / "source.txt"
            source_artifact.write_text("fixture source\n", encoding="utf-8")
            source_artifact_sha256 = hashlib.sha256(
                source_artifact.read_bytes()
            ).hexdigest()
            map_items = {
                "figure_simulation": {
                    "statement": (
                        "Example 2 reports the simulated welfare estimates for the "
                        "three parameter settings."
                    ),
                    "source_kind": "example",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                    "scope_reason": (
                        "The source presents this as a numerical illustration, not a "
                        "named formal statement."
                    ),
                    "source_evidence": "source.txt:1 describes simulated estimates.",
                },
                "theorem_named_internal_helper": {
                    "statement": "Figure 2 plots the simulated welfare estimates.",
                    "source_kind": "example",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                    "scope_reason": (
                        "The source presents this as a plotted numerical illustration, "
                        "not a named formal statement."
                    ),
                    "source_evidence": (
                        "source.txt:1 reports simulated estimates, unlike Theorem 4."
                    ),
                },
                "named_runtime": {
                    "statement": "Theorem 4 proves that Algorithm 2 runs in polynomial time.",
                    "source_kind": "runtime_claim",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                },
                "misclassified_theorem": {
                    "statement": "Proposition 5 establishes the exact enumerated optimum.",
                    "source_kind": "example",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                },
                "ordinary_language_runtime": {
                    "statement": (
                        "Example 6 reports that Algorithm 3 runs in polynomial time "
                        "for every input."
                    ),
                    "source_kind": "example",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                    "scope_reason": "The passage is presented under an example heading.",
                    "source_evidence": "source.txt:1 gives the claimed running time.",
                },
                "runtime_hidden_in_evidence": {
                    "statement": "Figure 7 reports implementation diagnostics.",
                    "source_kind": "example",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                    "scope_reason": "The row title describes a figure.",
                    "source_evidence": (
                        "Algorithm 3 runs in polynomial time for every input."
                    ),
                },
                "efficient_simulation_hidden_in_evidence": {
                    "statement": "Figure 8 reports a simulation output.",
                    "source_kind": "remark",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                    "scope_reason": "The row title describes a simulation figure.",
                    "source_evidence": (
                        "The condition can be tested efficiently via simulation."
                    ),
                },
                "missing_scope_evidence": {
                    "statement": "Example 7 reports a simulated welfare value.",
                    "source_kind": "example",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1",
                    "scope_reason": "The source presents the passage as an example.",
                },
            }
            source_lines = [str(item["statement"]) for item in map_items.values()]
            source_artifact.write_text("\n".join(source_lines) + "\n", encoding="utf-8")
            source_artifact_sha256 = hashlib.sha256(
                source_artifact.read_bytes()
            ).hexdigest()
            for line_number, item in enumerate(map_items.values(), start=1):
                quoted_text = str(item["statement"])
                item["source_location"] = f"source.txt:{line_number}"
                item["source_anchor_evidence"] = [
                    {
                        "path": "source.txt",
                        "line_start": line_number,
                        "line_end": line_number,
                        "quoted_text": quoted_text,
                        "quoted_text_sha256": hashlib.sha256(
                            quoted_text.encode("utf-8")
                        ).hexdigest(),
                    }
                ]
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_artifact_path": "source.txt",
                        "source_artifact_sha256": source_artifact_sha256,
                        "source_coverage_mode": "deep_paper_with_all_prose_claims",
                        "source_prose_inventory_review": {
                            "complete": True,
                            "validator": "fixture source reviewer",
                            "validated_at": "2026-07-26T00:00:00Z",
                            "method": "full-prose fixture coverage",
                            "source_artifact_sha256": source_artifact_sha256,
                        },
                        "items": map_items,
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            self.assertEqual(
                inventory["figure_simulation"]["canonical_source_artifact_path"],
                "source.txt",
            )
            self.assertEqual(
                inventory["figure_simulation"]["canonical_source_artifact_sha256"],
                source_artifact_sha256,
            )
            quote_digests = {}
            for key, item in inventory.items():
                quote, quote_error = review_dashboard._source_inventory_anchor_quote_text(
                    item
                )
                self.assertEqual(quote_error, "")
                quote_digests[key] = hashlib.sha256(quote.encode("utf-8")).hexdigest()
            coverage_items = {
                key: {
                    "coverage": "not_a_theorem_statement",
                    "review_rows": [],
                    "support_declarations": [],
                    "reason": (
                        "The pinned source passage is a numerical illustration, "
                        "not a named formal theorem statement."
                    ),
                    "source_evidence": "Pinned source excerpt at the exact listed locator.",
                    "source_scope_judgment": "finite_nonclaim_observation",
                    "source_anchor_quote_sha256": quote_digests[key],
                    "statement_sha256": inventory[key]["statement_sha256"],
                    "validator": "independent-test-agent",
                    "validated_at": "2026-07-24T12:00:00Z",
                }
                for key in map_items
            }
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "independent-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-07-24T12:00:00Z",
                        "items": coverage_items,
                    }
                ),
                encoding="utf-8",
            )

            make_fixture_coverage_source_inputs_current(folder)

            summary = review_dashboard.paper_coverage_audit_summary(folder, [])
            self.assertCountEqual(
                summary["required_out_of_scope"],
                [
                    "misclassified_theorem",
                    "efficient_simulation_hidden_in_evidence",
                    "missing_scope_evidence",
                    "named_runtime",
                    "ordinary_language_runtime",
                    "runtime_hidden_in_evidence",
                ],
            )
            self.assertNotIn("figure_simulation", summary["required_out_of_scope"])
            self.assertNotIn(
                "theorem_named_internal_helper", summary["required_out_of_scope"]
            )
            self.assertCountEqual(
                summary["source_scope_classification_errors"],
                [
                    "misclassified_theorem: non_named_computational_illustration "
                    "cannot label a named formal statement or theorem reference",
                    "ordinary_language_runtime: non_named_computational_illustration "
                    "cannot label a general algorithmic, runtime, complexity, or "
                    "performance assertion",
                    "runtime_hidden_in_evidence: non_named_computational_illustration "
                    "cannot label a general algorithmic, runtime, complexity, or "
                    "performance assertion",
                    "efficient_simulation_hidden_in_evidence: "
                    "non_named_computational_illustration cannot label a general "
                    "algorithmic, runtime, complexity, or performance assertion",
                    "named_runtime: non_named_computational_illustration requires "
                    "source_kind `example` or `remark`",
                    "missing_scope_evidence: non_named_computational_illustration "
                    "requires source_evidence",
                ],
            )
            self.assertTrue(summary["source_to_lean_needs_attention"])

    def test_user_approved_scope_exclusion_is_distinct_from_nonclaim_scope(self) -> None:
        """A user-scoped source claim remains visible without blocking closeout."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "UserScopePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source_text = "The condition can be tested efficiently by simulation.\n"
            source.write_text(source_text, encoding="utf-8")
            source_sha256 = hashlib.sha256(source.read_bytes()).hexdigest()
            quote = source_text.rstrip("\n")
            quote_sha256 = hashlib.sha256(quote.encode("utf-8")).hexdigest()
            approval = {
                "schema": 1,
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "User instruction recorded for this formalization pass.",
                "approved_at": "2026-07-25",
                "reason": "The user expressly excluded this standalone simulation-efficiency assertion from formalization scope.",
                "source_locator": "source.txt:1",
                "source_evidence": "The byte-pinned source line states the broad simulation assertion.",
                "source_anchor_quote_sha256": quote_sha256,
            }
            statement = "The source asserts that the condition can be tested efficiently by simulation."
            map_item = {
                "statement": statement,
                "source_kind": "prose_assertion",
                "claim_bearing": True,
                "source_url": "https://example.invalid/paper",
                "source_location": "source.txt:1",
                "source_anchor_evidence": [
                    {
                        "path": "source.txt",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": quote,
                        "quoted_text_sha256": quote_sha256,
                    }
                ],
                "user_approved_scope_exclusion": approval,
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_artifact_path": "source.txt",
                        "source_artifact_sha256": source_sha256,
                        "source_coverage_mode": "deep_paper_with_all_prose_claims",
                        "source_prose_inventory_review": {
                            "complete": True,
                            "validator": "fixture source reviewer",
                            "validated_at": "2026-07-26T00:00:00Z",
                            "method": "full-prose fixture coverage",
                            "source_artifact_sha256": source_sha256,
                        },
                        "items": {"renamed_navigation_key": map_item},
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "independent-test-agent",
                        "validated_at": "2026-07-25T12:00:00Z",
                        "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(inventory),
                        "items": {
                            "renamed_navigation_key": {
                                "coverage": "user_approved_scope_exclusion",
                                "review_rows": [],
                                "support_declarations": [],
                                "statement_sha256": inventory["renamed_navigation_key"]["statement_sha256"],
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            make_fixture_coverage_source_inputs_current(folder)
            summary = review_dashboard.paper_coverage_audit_summary(folder, [])
            self.assertEqual(summary["user_approved_scope_exclusions"], ["renamed_navigation_key"])
            self.assertEqual(summary["required_out_of_scope"], [])
            self.assertEqual(summary["user_approved_scope_exclusion_errors"], [])
            # A current aggregate legacy sidecar remains reusable when it has
            # not claimed an artifact pin.  A later migration can add the
            # narrower item-level identities without reopening this judgment.
            self.assertEqual(summary["legacy_unpinned_items"], [])
            self.assertFalse(summary["needs_attention"])

            coverage_path = audit / "paper_coverage_llm.json"
            coverage_payload = json.loads(coverage_path.read_text(encoding="utf-8"))
            coverage_payload["source_artifact_path"] = "source.txt"
            coverage_payload["source_artifact_sha256"] = "0" * 64
            coverage_path.write_text(json.dumps(coverage_payload), encoding="utf-8")
            mismatched_source = review_dashboard.paper_coverage_audit_summary(folder, [])
            self.assertEqual(
                mismatched_source["legacy_unpinned_items"], ["renamed_navigation_key"]
            )
            self.assertTrue(mismatched_source["needs_attention"])

            # A partial or malformed map pin is not an absent legacy pin.  A
            # sidecar which itself claims artifact freshness must fail closed
            # instead of falling back to the aggregate-only compatibility lane.
            malformed_map = json.loads(map_path.read_text(encoding="utf-8"))
            malformed_map["source_artifact_sha256"] = ""
            map_path.write_text(json.dumps(malformed_map), encoding="utf-8")
            malformed_source = review_dashboard.paper_coverage_audit_summary(folder, [])
            self.assertEqual(
                malformed_source["legacy_unpinned_items"], ["renamed_navigation_key"]
            )
            self.assertTrue(malformed_source["needs_attention"])

            approval["approval_reference"] = ""
            map_item["user_approved_scope_exclusion"] = approval
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_artifact_path": "source.txt",
                        "source_artifact_sha256": source_sha256,
                        "source_coverage_mode": "deep_paper_with_all_prose_claims",
                        "source_prose_inventory_review": {
                            "complete": True,
                            "validator": "fixture source reviewer",
                            "validated_at": "2026-07-26T00:00:00Z",
                            "method": "full-prose fixture coverage",
                            "source_artifact_sha256": source_sha256,
                        },
                        "items": {"renamed_navigation_key": map_item},
                    }
                ),
                encoding="utf-8",
            )
            malformed = review_dashboard.paper_coverage_audit_summary(folder, [])
            self.assertTrue(malformed["user_approved_scope_exclusion_errors"])
            self.assertTrue(malformed["needs_attention"])

    def test_computational_scope_semantics_cover_formal_refs_algorithms_and_complexity(
        self,
    ) -> None:
        """Scope routing follows source assertions, not labels or bare adjectives."""

        source_sha256 = hashlib.sha256(b"fixture source\n").hexdigest()

        def scoped_item(statement: str, **overrides: object) -> dict[str, object]:
            quote_sha256 = hashlib.sha256(statement.encode("utf-8")).hexdigest()
            return {
                "statement": statement,
                "source_kind": "example",
                "claim_bearing": False,
                "source_scope_classification": "non_named_computational_illustration",
                "source_location": "source.txt:1",
                "source_evidence": "source.txt:1 gives the source presentation.",
                "scope_reason": "The source presents a finite numerical illustration.",
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": source_sha256,
                "source_anchor_evidence": [
                    {
                        "path": "source.txt",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": statement,
                        "quoted_text_sha256": quote_sha256,
                    }
                ],
                **overrides,
            }

        for source_text in (
            r"By Theorem~\ref{thm:main}, the conclusion follows.",
            r"\begin{proposition} The displayed inequality holds.\end{proposition}",
            r"\begin{thm} The displayed inequality holds.\end{thm}",
            r"See \cref{lem:bound} for the stated inequality.",
            r"See \eqref{prop:bound} for the stated inequality.",
            r"\textbf{Proposition A.1.} The displayed inequality holds.",
        ):
            item = scoped_item(source_text)
            self.assertTrue(
                review_dashboard._source_inventory_item_is_named_claim(
                    "arbitrary_navigation_key", item
                )
            )
            self.assertIn(
                "named formal statement or theorem reference",
                review_dashboard._source_inventory_item_scope_classification_error(item),
            )

        mislabelled_result = scoped_item(
            "The source's Theorem 4 establishes the exact source endpoint."
        )
        theorem_reference = scoped_item(
            r"By Theorem~\ref{thm:main}, the conclusion follows."
        )
        self.assertTrue(
            source_claim_policy.source_inventory_item_is_named_result_presentation(
                mislabelled_result
            )
        )
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_proof_evidence(
                "arbitrary_navigation_key", mislabelled_result
            )
        )
        self.assertFalse(
            source_claim_policy.source_inventory_item_is_named_result_presentation(
                theorem_reference
            )
        )

        named_algorithm_items = (
            scoped_item(
                "The source gives Algorithm 3 for the optimization problem."
            ),
            scoped_item(r"\begin{algorithm} \caption{Construction} \end{algorithm}"),
            scoped_item(
                "A pseudocode block is shown.", source_kind="algorithm"
            ),
        )
        for item in named_algorithm_items:
            self.assertTrue(
                review_dashboard._source_inventory_item_is_named_algorithm_block(item)
            )
            self.assertTrue(
                review_dashboard._source_inventory_item_requires_review_row(
                    "arbitrary_navigation_key", item
                )
            )
            scope_error = review_dashboard._source_inventory_item_scope_classification_error(
                item
            )
            if item["source_kind"] == "algorithm":
                self.assertIn("requires source_kind `example` or `remark`", scope_error)
            else:
                self.assertIn("named Algorithm, Procedure, or Method block", scope_error)

        for source_text in (
            r"The algorithm takes O(n^2) operations.",
            r"The procedure requires \mathcal{O}(n^2) steps.",
            r"The procedure requires \mathcal O(n^2) steps.",
            "The method terminates for every input.",
            "Algorithm A outputs a feasible solution for every instance.",
            "The method produces a matching for every input.",
            "The running time is polynomial in the instance size.",
        ):
            item = scoped_item(source_text)
            self.assertTrue(
                review_dashboard._source_text_has_general_computational_claim(
                    source_text
                )
            )
            self.assertIn(
                "general algorithmic, runtime, complexity, or performance assertion",
                review_dashboard._source_inventory_item_scope_classification_error(item),
            )

        # Mathematical uses of the same adjectives are not automatically
        # computational claims, but neither are they eligible for the narrow
        # finite-observation exception without an actual source presentation.
        for source_text in (
            "An exponential distribution has a quadratic utility.",
            "The polynomial regression has a linear predictor.",
        ):
            item = scoped_item(source_text)
            self.assertFalse(
                review_dashboard._source_text_has_general_computational_claim(
                    source_text
                )
            )
            self.assertIn(
                "requires a literal finite observation/report",
                review_dashboard._source_inventory_item_scope_classification_error(item),
            )

        self.assertIn(
            "general correctness, existence, optimality, or mathematical assertion",
            review_dashboard._source_inventory_item_scope_classification_error(
                scoped_item("The allocation is efficient under the stated condition.")
            ),
        )
        finite_observation = scoped_item(
            "Figure 1 reports one numerical simulation with a 2.1-second observation."
        )
        self.assertEqual(
            review_dashboard._source_inventory_item_scope_classification_error(
                finite_observation
            ),
            "",
        )

        # Every exclusion is screened against all source-facing fields, including
        # a title, and its positive finite-observation evidence comes from the
        # anchored quote rather than a curator's summary.
        titled_general_claim = scoped_item(
            "Figure 1 reports a finite simulated welfare estimate.",
            title="The algorithm is correct for every input and runs in polynomial time.",
        )
        self.assertIn(
            "general algorithmic, runtime, complexity, or performance assertion",
            review_dashboard._source_inventory_item_scope_classification_error(
                titled_general_claim
            ),
        )

        def anchored_quote(text: str) -> list[dict[str, object]]:
            return [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": text,
                    "quoted_text_sha256": hashlib.sha256(
                        text.encode("utf-8")
                    ).hexdigest(),
                }
            ]

        for source_quote in (
            "Figure 1 shows our scheme is strongly polynomial.",
            "Figure 1 illustrates that the approach guarantees a winner under all preferences.",
            "Figure 1 shows the mechanism satisfies anonymity.",
            "Figure 1 shows Pseudocode 1 elects the Condorcet winner.",
        ):
            item = scoped_item(
                "Figure 1 reports a finite simulated welfare estimate.",
                source_anchor_evidence=anchored_quote(source_quote),
            )
            self.assertIn(
                "cannot label a general",
                review_dashboard._source_inventory_item_scope_classification_error(item),
            )

        # General source claims must remain review targets even when an
        # inventory key or Lean declaration tries to make them look local.
        for source_text in (
            "The mechanism is strategyproof.",
            "An equilibrium exists for every instance.",
            "The proposed allocation is optimal.",
            "The method has optimal performance.",
            "The algorithm runs in O(n^2) time.",
            "Figure 6 reports that if theta > 0, the welfare gap is positive.",
            (
                "For every admissible profile satisfying condition C, an optimal "
                "allocation exists."
            ),
        ):
            item = scoped_item(
                source_text,
                aliases=["figure_navigation_alias"],
                lean_declarations=["Fixture.internal_plot_helper"],
                support_lean_declarations=["Fixture.theorem_like_name"],
            )
            scope_error = review_dashboard._source_inventory_item_scope_classification_error(
                item
            )
            if review_dashboard._source_text_has_general_computational_claim(source_text):
                self.assertIn(
                    "general algorithmic, runtime, complexity, or performance assertion",
                    scope_error,
                )
            else:
                self.assertIn(
                    "general correctness, existence, optimality, or mathematical assertion",
                    scope_error,
                )
            self.assertTrue(
                review_dashboard._source_inventory_item_requires_review_row(
                    "finite_figure_navigation_key", item
                )
            )

        # Omitting the explicit, evidence-bearing exception cannot downgrade the
        # same source claim just by calling it an example in the map.
        for source_text in (
            "A stable matching exists for every input.",
            "The proposed solution is optimal.",
            "The algorithm runs in O(n^2) time.",
            "For every parameter satisfying C, the mechanism is strategyproof.",
        ):
            item = {
                key: value
                for key, value in scoped_item(
                    source_text,
                    source=review_dashboard.PAPER_STATEMENT_MAP_FILE,
                    aliases=["figure_navigation_alias"],
                    lean_declarations=["Fixture.internal_plot_helper"],
                ).items()
                if key != "source_scope_classification"
            }
            self.assertTrue(
                review_dashboard._source_inventory_item_requires_proof_evidence(
                    "figure_navigation_key", item
                )
            )
            self.assertTrue(
                review_dashboard._source_inventory_item_requires_review_row(
                    "figure_navigation_key", item
                )
            )

        # Returning a non-eligible figure/example passage to `source_kind:
        # claim` keeps it review-required even without an explicit
        # claim_bearing boolean or a theorem-shaped map/declaration name.
        for returned_claim in (
            "Figure 3 states that equilibrium behavior is human, algorithmic, or mixed and that a shaded region has lower welfare.",
            "A centered-uniform Gaussian example asserts there exist parameters with approximately four percent lower welfare.",
        ):
            item = {
                "statement": returned_claim,
                "source": review_dashboard.PAPER_STATEMENT_MAP_FILE,
                "source_kind": "claim",
            }
            self.assertTrue(
                review_dashboard._source_inventory_item_requires_proof_evidence(
                    "renamed_navigation_key", item
                )
            )
            self.assertTrue(
                review_dashboard._source_inventory_item_requires_review_row(
                    "renamed_navigation_key", item
                )
            )

        unclassified_finite_observation = {
            key: value
            for key, value in scoped_item(
                "Figure 5 reports a finite simulated welfare estimate.",
                source=review_dashboard.PAPER_STATEMENT_MAP_FILE,
            ).items()
            if key != "source_scope_classification"
        }
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "figure_navigation_key", unclassified_finite_observation
            )
        )

        finite_with_theorem_shaped_lean_names = scoped_item(
            "Figure 5 reports a finite simulated welfare estimate.",
            aliases=["Theorem_99_navigation_only"],
            lean_declarations=["Fixture.PaperInterface.theorem_named_plot"],
            support_lean_declarations=["Fixture.proof_helper"],
        )
        self.assertEqual(
            review_dashboard._source_inventory_item_scope_classification_error(
                finite_with_theorem_shaped_lean_names
            ),
            "",
        )

        # A map key and a contextual theorem citation in the evidence are not
        # semantic source claims.  The citation remains detectable for ordinary
        # source inventory routing, but it does not invalidate a real figure.
        contextual_reference = scoped_item(
            "Figure 2 reports a simulated welfare estimate.",
            source_evidence="source.txt:1 compares the plot with Theorem 4.",
        )
        self.assertFalse(
            review_dashboard._source_inventory_item_is_named_claim(
                "Theorem_99_navigation_only", scoped_item("Figure 2 reports a plot.")
            )
        )
        self.assertTrue(
            review_dashboard._source_inventory_item_is_named_claim(
                "arbitrary_navigation_key", contextual_reference
            )
        )
        self.assertEqual(
            review_dashboard._source_inventory_item_scope_classification_error(
                contextual_reference
            ),
            "",
        )

    def test_finite_observation_scope_needs_concrete_cue_and_no_lean_route(
        self,
    ) -> None:
        """A display label cannot hide a result or retain Lean coverage credit."""

        source_sha256 = hashlib.sha256(b"fixture source\n").hexdigest()

        def scoped_item(quote: str, **overrides: object) -> dict[str, object]:
            return {
                "statement": quote,
                "source_kind": "example",
                "claim_bearing": False,
                "source_scope_classification": "non_named_computational_illustration",
                "source_location": "source.txt:1",
                "source_evidence": "source.txt:1 gives the source presentation.",
                "scope_reason": "The source presents a finite numerical illustration.",
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": source_sha256,
                "source_anchor_evidence": [
                    {
                        "path": "source.txt",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": quote,
                        "quoted_text_sha256": hashlib.sha256(
                            quote.encode("utf-8")
                        ).hexdigest(),
                    }
                ],
                **overrides,
            }

        display_result = scoped_item(
            "Figure 1 shows the system has a unique equilibrium.",
            aliases=["arbitrary_navigation_alias"],
            lean_declarations=["Fixture.unrelated_helper"],
        )
        self.assertIn(
            "requires a literal finite observation/report",
            review_dashboard._source_inventory_item_scope_classification_error(
                display_result
            ),
        )
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "arbitrary_navigation_key", display_result
            )
        )

        finite_observation = scoped_item(
            "Figure 1 reports one numerical simulation with n = 100.",
            aliases=["another_navigation_alias"],
            lean_declarations=["Fixture.theorem_shaped_name"],
        )
        self.assertEqual(
            review_dashboard._source_inventory_item_scope_classification_error(
                finite_observation
            ),
            "",
        )
        quote_digest = hashlib.sha256(
            finite_observation["statement"].encode("utf-8")
        ).hexdigest()
        covered_with_lean_route = {
            "coverage": "not_a_theorem_statement",
            "source_scope_judgment": "finite_nonclaim_observation",
            "source_anchor_quote_sha256": quote_digest,
            "review_rows": ["Fixture.PaperInterface.any_name"],
            "review_row_signature_sha256": "f" * 64,
            "support_declarations": ["Fixture.any_support_name"],
        }
        route_errors = review_dashboard._source_scope_classification_errors(
            {"unrelated_navigation_key": finite_observation},
            {"unrelated_navigation_key": covered_with_lean_route},
        )
        self.assertTrue(
            any("cannot claim review_rows or review-row signature pins" in error for error in route_errors)
        )
        self.assertTrue(
            any("cannot claim support_declarations" in error for error in route_errors)
        )

        clean_coverage = {
            **covered_with_lean_route,
            "review_rows": [],
            "review_row_signature_sha256": "",
            "support_declarations": [],
        }
        self.assertEqual(
            review_dashboard._source_scope_classification_errors(
                {"renamed_navigation_key": finite_observation},
                {"renamed_navigation_key": clean_coverage},
            ),
            [],
        )

    def test_computational_scope_requires_pinned_artifact_and_anchor(self) -> None:
        """A free-form source-evidence string cannot create an audit exemption."""

        valid_sha256 = hashlib.sha256(b"fixture source\n").hexdigest()
        quote = "Figure 1 reports a finite simulated welfare estimate.\nCaption continues."
        base = {
            "statement": "Figure 1 reports a finite simulated welfare estimate.",
            "source_kind": "example",
            "claim_bearing": False,
            "source_scope_classification": "non_named_computational_illustration",
            "source_location": "source.txt:1-2",
            "source_evidence": "source.txt:1-2 is the Figure 1 caption.",
            "scope_reason": "The source identifies a finite numerical example.",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": valid_sha256,
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 2,
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                }
            ],
        }
        self.assertEqual(
            review_dashboard._source_inventory_item_scope_classification_error(base),
            "",
        )
        inventory_digest = review_dashboard.paper_statement_inventory_digest(
            {"finite_figure": base}
        )
        for changed_item in (
            {**base, "source_scope_classification": ""},
            {**base, "scope_reason": "A different source-grounded reason."},
            {**base, "source_evidence": "source.txt:1-2 is a different passage."},
            {**base, "source_artifact_sha256": "1" * 64},
        ):
            self.assertNotEqual(
                review_dashboard.paper_statement_inventory_digest(
                    {"finite_figure": changed_item}
                ),
                inventory_digest,
            )
        self.assertEqual(
            review_dashboard._source_inventory_item_scope_classification_error(
                {**base, "source_artifact_path": "papers/FixturePaper/source.txt"}
            ),
            "",
        )

        missing_artifact = {key: value for key, value in base.items() if key != "source_artifact_path"}
        self.assertIn(
            "pinned source_artifact_path",
            review_dashboard._source_inventory_item_scope_classification_error(
                missing_artifact
            ),
        )
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "figure_navigation_key", missing_artifact
            )
        )
        bad_digest = {**base, "source_artifact_sha256": "not-a-sha256"}
        self.assertIn(
            "valid pinned source_artifact_sha256",
            review_dashboard._source_inventory_item_scope_classification_error(bad_digest),
        )
        different_artifact = {
            **base,
            "source_artifact_path": "other.txt",
            "source_artifact_sha256": "1" * 64,
            "canonical_source_artifact_path": "source.txt",
            "canonical_source_artifact_sha256": valid_sha256,
        }
        self.assertIn(
            "canonical pinned source artifact",
            review_dashboard._source_inventory_item_scope_classification_error(
                different_artifact
            ),
        )
        different_digest = {
            **base,
            "source_artifact_sha256": "1" * 64,
            "canonical_source_artifact_path": "source.txt",
            "canonical_source_artifact_sha256": valid_sha256,
        }
        self.assertIn(
            "canonical source_artifact_sha256",
            review_dashboard._source_inventory_item_scope_classification_error(
                different_digest
            ),
        )
        wrong_file_anchor = {**base, "source_location": "other.txt:1"}
        self.assertIn(
            "must name the pinned source artifact",
            review_dashboard._source_inventory_item_scope_classification_error(
                wrong_file_anchor
            ),
        )
        page_only_text_anchor = {**base, "source_location": "Example 1, p. 3"}
        self.assertIn(
            "file:line anchor into the pinned source artifact",
            review_dashboard._source_inventory_item_scope_classification_error(
                page_only_text_anchor
            ),
        )
        byte_verified_without_quote = {
            key: value for key, value in base.items() if key != "source_anchor_evidence"
        }
        self.assertIn(
            "requires a nonempty byte-verified source_anchor_evidence list",
            review_dashboard._source_inventory_item_scope_classification_error(
                byte_verified_without_quote
            ),
        )
        self.assertEqual(
            review_dashboard._source_scope_classification_errors(
                {"finite_figure": base}, {}
            ),
            [
                "finite_figure: non_named_computational_illustration requires an "
                "explicit out-of-theorem-scope coverage judgment"
            ],
        )
        self.assertEqual(
            review_dashboard._source_scope_classification_errors(
                {"finite_figure": base},
                {
                    "finite_figure": {
                        "coverage": "not_a_theorem_statement",
                        "source_scope_judgment": "finite_nonclaim_observation",
                        "source_anchor_quote_sha256": hashlib.sha256(
                            quote.encode("utf-8")
                        ).hexdigest(),
                    }
                },
            ),
            [],
        )
        semantic_judgment_errors = review_dashboard._source_scope_classification_errors(
            {"finite_figure": base},
            {"finite_figure": {"coverage": "not_a_theorem_statement"}},
        )
        self.assertTrue(
            any("independent source_scope_judgment" in error for error in semantic_judgment_errors)
        )
        self.assertTrue(
            any("source_anchor_quote_sha256" in error for error in semantic_judgment_errors)
        )

    def test_source_declared_open_scope_is_byte_pinned_and_has_no_lean_credit(self) -> None:
        """A source-declared open problem remains catalogued without proof credit."""

        source_quote = (
            "We do not know a proof for this fact, and leave the characterization "
            "as an open question."
        )
        source_digest = hashlib.sha256(b"fixture source\n").hexdigest()
        quote_digest = hashlib.sha256(source_quote.encode("utf-8")).hexdigest()
        open_item = {
            "statement": "The source explicitly leaves this characterization open.",
            "source_kind": "remark",
            "claim_bearing": False,
            "coverage_status": "source_declared_open",
            "protocol_role": "source_declared_open",
            "source_scope_classification": (
                "source_declared_open_nonresult_observation"
            ),
            "source_location": "source.txt:1",
            "source_evidence": "The byte-pinned source remark says the issue is open.",
            "scope_reason": "The exact source remark records an unresolved issue.",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_digest,
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": source_quote,
                    "quoted_text_sha256": quote_digest,
                }
            ],
        }
        self.assertEqual(
            review_dashboard._source_inventory_item_scope_classification_error(open_item),
            "",
        )
        self.assertTrue(
            review_dashboard._source_inventory_item_is_catalogued_nonformal_observation(
                open_item
            )
        )
        self.assertFalse(
            review_dashboard._source_inventory_item_requires_review_row(
                "navigation_only", open_item
            )
        )
        self.assertEqual(
            review_dashboard._source_scope_classification_errors(
                {"open_item": open_item},
                {
                    "open_item": {
                        "coverage": "not_a_theorem_statement",
                        "source_scope_judgment": (
                            "source_declared_open_nonresult_observation"
                        ),
                        "source_anchor_quote_sha256": quote_digest,
                    }
                },
            ),
            [],
        )

        self.assertIn(
            "coverage_status `source_declared_open`",
            review_dashboard._source_inventory_item_scope_classification_error(
                {**open_item, "coverage_status": "covered"}
            ),
        )
        self.assertIn(
            "claim_bearing: false",
            review_dashboard._source_inventory_item_scope_classification_error(
                {**open_item, "claim_bearing": True}
            ),
        )
        credit_errors = review_dashboard._source_scope_classification_errors(
            {"open_item": open_item},
            {
                "open_item": {
                    "coverage": "covered",
                    "source_scope_judgment": (
                        "source_declared_open_nonresult_observation"
                    ),
                    "source_anchor_quote_sha256": quote_digest,
                    "review_rows": ["unrelated_proof"],
                    "review_row_signature_sha256": {"unrelated_proof": "0" * 64},
                    "support_declarations": ["unrelated_support"],
                }
            },
        )
        self.assertTrue(
            any("out-of-theorem-scope coverage judgment" in error for error in credit_errors),
            credit_errors,
        )
        self.assertTrue(
            any("cannot claim review_rows" in error for error in credit_errors),
            credit_errors,
        )
        self.assertTrue(
            any("cannot claim support_declarations" in error for error in credit_errors),
            credit_errors,
        )

    def test_source_to_lean_uses_assumption_provenance_for_assumption_rows(self) -> None:
        """Model conditions must not need a duplicate theorem-match judgment."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ConditionPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            statement = "The model requires its predictor to be measurable."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_url": "https://example.invalid/paper",
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {
                            "source_model_measurability": {
                                "title": "Assumption 1",
                                "statement": statement,
                                "source_kind": "assumption",
                                "claim_bearing": True,
                                "source_url": "https://example.invalid/paper",
                                "source_location": "p. 1",
                                "support_lean_declarations": ["model_measurability"],
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            paper_digest = review_dashboard.statement_digest(statement)
            manifest = normalized_fixture_manifest(proposition_spec_manifest())
            row = review_dashboard.ReviewItem(
                name="model_measurability",
                kind="abbrev",
                lean_statement="abbrev model_measurability : Prop := True",
                paper_statement=statement,
                agent_statement=statement,
                lean_signature_manifest=manifest,
                lean_signature_sha256=str(manifest["sha256"]),
                is_assumption=True,
                llm_assumption_judgment="paper_condition",
                llm_assumption_source="assumption_match_llm.json",
                llm_assumption_validator="independent-test-agent",
                llm_assumption_validated_at="2026-07-24T12:00:00Z",
                llm_assumption_lean_statement_sha256=review_dashboard.statement_digest(
                    "abbrev model_measurability : Prop := True"
                ),
                llm_assumption_paper_statement_sha256=paper_digest,
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "independent-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-07-24T12:00:00Z",
                        "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(
                            inventory
                        ),
                        "review_surface_sha256": review_dashboard.review_surface_digest([row]),
                        "items": {
                            "source_model_measurability": {
                                "coverage": "covered",
                                "review_rows": ["model_measurability"],
                                "review_row_signature_sha256": {
                                    "model_measurability": manifest["sha256"]
                                },
                                "reason": "The explicit model condition is the same measurable-predictor requirement.",
                                "source_evidence": "The condition is stated at the pinned source location.",
                                "statement_sha256": paper_digest,
                                "validator": "independent-test-agent",
                                "validated_at": "2026-07-24T12:00:00Z",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            make_fixture_coverage_source_inputs_current(folder)

            summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertFalse(summary["source_to_lean_needs_attention"])
            self.assertEqual(summary["row_statement_match_missing"], [])
            self.assertEqual(summary["row_statement_match_missing_statement_digest"], [])
            self.assertEqual(summary["row_assumption_provenance_missing"], [])
            self.assertEqual(
                summary["row_statement_match_links"][0]["row_correctness_lane"],
                "assumption_provenance",
            )

            row.llm_assumption_judgment = ""
            missing_summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertEqual(
                missing_summary["row_assumption_provenance_missing"],
                ["source_model_measurability -> model_measurability"],
            )
            self.assertTrue(missing_summary["source_to_lean_needs_attention"])

    def test_direct_coverage_requires_the_row_exact_source_route(self) -> None:
        """A green row for source B cannot silently cover source A."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "RoutePinnedPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_a = "Theorem A. This is the paper-facing source result."
            source_b = "Theorem B. This is a different paper-facing source result."
            location_a = "source.txt:10-10"
            location_b = "source.txt:11-11"
            digest_a = review_dashboard.statement_digest(source_a)
            digest_b = review_dashboard.statement_digest(source_b)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "llm_statement_review": {
                                "require_explicit_source_routes": True
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_url": "https://example.invalid/paper",
                        "items": {
                            "source_a": {
                                "statement": source_a,
                                "source_kind": "theorem",
                                "source_url": "https://example.invalid/paper",
                                "source_location": location_a,
                                "lean_declarations": ["row"],
                            },
                            "source_b": {
                                "statement": source_b,
                                "source_kind": "theorem",
                                "source_url": "https://example.invalid/paper",
                                "source_location": location_b,
                                "lean_declarations": ["row"],
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )
            row = review_dashboard.ReviewItem(
                name="row",
                kind="theorem",
                lean_statement="theorem row : True",
                paper_statement=source_b,
                agent_statement=source_b,
                llm_match_judgment="matches",
                llm_match_source_routes=[
                    {
                        "source_item": "source_b",
                        "source_statement_sha256": digest_b,
                        "source_location": location_b,
                        "route_kind": "direct",
                    }
                ],
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "independent-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-07-24T12:00:00Z",
                        "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(
                            inventory
                        ),
                        "review_surface_sha256": review_dashboard.review_surface_digest([row]),
                        "items": {
                            "source_a": {
                                "coverage": "covered",
                                "review_rows": ["row"],
                                "reason": "The row supposedly covers source A.",
                                "source_evidence": "Theorem A is in the pinned source span.",
                                "statement_sha256": digest_a,
                                "validator": "independent-test-agent",
                                "validated_at": "2026-07-24T12:00:00Z",
                            },
                            "source_b": {
                                "coverage": "covered",
                                "review_rows": ["row"],
                                "reason": "The row directly covers source B.",
                                "source_evidence": "Theorem B is in the pinned source span.",
                                "statement_sha256": digest_b,
                                "validator": "independent-test-agent",
                                "validated_at": "2026-07-24T12:00:00Z",
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )

            summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertTrue(summary["source_to_lean_needs_attention"])
            self.assertEqual(summary["coverage_route_mismatch_count"], 1)
            self.assertIn("source_a -> row", summary["coverage_route_mismatch"][0])

    def test_direct_coverage_uses_only_explicit_paper_facing_declarations(self) -> None:
        """KR21-style proof helpers cannot become source-coverage endpoints."""

        kr21_style_item = {
            "lean_declarations": ["equation8_source_concrete_mallows_probability"],
            "proof_lean_declarations": ["mallowsSpec_law_formula"],
            "semantic_bridge_declarations": ["mallows_law_semantic_bridge"],
            "paper_equivalence_declarations": ["mallows_law_equivalence"],
            "aliases": ["mallowsSpec_law_formula"],
        }
        self.assertEqual(
            review_dashboard.source_item_direct_coverage_declarations(kr21_style_item),
            ["equation8_source_concrete_mallows_probability"],
        )

        # Legacy maps without an explicit paper-facing route may still use an
        # alias, but proof and bridge metadata alone are never source routes.
        legacy_item = {
            "proof_lean_declarations": ["definition1_concreteMallowsSpec_atom_continuity"],
            "semantic_bridge_declarations": [
                "definition1_concreteMallowsSpec_asymptotic_first_dominance"
            ],
            "aliases": ["legacy_paper_facing_endpoint"],
        }
        self.assertEqual(
            review_dashboard.source_item_direct_coverage_declarations(legacy_item),
            ["legacy_paper_facing_endpoint"],
        )
        self.assertEqual(
            review_dashboard.source_item_direct_coverage_declarations(
                {
                    "proof_lean_declarations": ["partial_proof_step"],
                    "semantic_bridge_declarations": ["partial_semantic_bridge"],
                }
            ),
            [],
        )

    def test_corrected_target_coverage_requires_the_repaired_row_statement(self) -> None:
        """A special route cannot pair a repaired target with archival review text."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CorrectedTargetCoveragePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            archival = "The printed theorem has the unrestricted conclusion."
            corrected = "Under the explicit three-point condition, the repaired theorem holds."
            archival_location = "source.txt:20-21"
            target = {
                "schema": 1,
                "statement": corrected,
                "governing_defect_ids": ["FIXTURE-CORRECTION"],
                "archival_equivalence_claimed": False,
                "archival_source_locator": archival_location,
                "archival_source_quote_sha256": "a" * 64,
                "approval": {
                    "kind": "explicit_user_instruction",
                    "recorded_at": "2026-07-25",
                    "reference": "The repaired target is explicitly approved without archival equivalence.",
                    "target_statement_sha256": review_dashboard.statement_digest(corrected),
                    "artifact_path": "docs/approval.md",
                    "artifact_sha256": "b" * 64,
                },
            }
            target["corrected_target_sha256"] = review_dashboard.corrected_target_digest(
                target
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "llm_statement_review": {
                                "require_explicit_source_routes": True
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_url": "https://example.invalid/paper",
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {
                            "opaque_source_key": {
                                "title": "Theorem 1: Printed result",
                                "statement": archival,
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "source_location": "source.txt:1-99",
                                "source_defect_ids": ["FIXTURE-CORRECTION"],
                                "coverage_status": "corrected_source_statement",
                                "lean_declarations": ["unrelated_review_row"],
                                "corrected_target": target,
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            manifest = nontrivial_theorem_manifest()
            row = review_dashboard.ReviewItem(
                name="unrelated_review_row",
                kind="theorem",
                lean_statement="theorem unrelated_review_row : 0 != 1",
                paper_statement=archival,
                agent_statement=archival,
                lean_signature_manifest=manifest,
                lean_signature_sha256=str(manifest["sha256"]),
                llm_match_judgment="matches",
                llm_match_resolution="approved_corrected_target",
                llm_match_paper_statement_sha256=review_dashboard.statement_digest(
                    archival
                ),
                llm_match_source_routes=[
                    {
                        "source_item": "opaque_source_key",
                        "source_statement_sha256": review_dashboard.statement_digest(
                            corrected
                        ),
                        "source_location": archival_location,
                        "route_kind": "approved_corrected_target",
                    }
                ],
            )

            def write_coverage() -> None:
                inventory = review_dashboard.paper_statement_inventory(folder)
                (audit / "paper_coverage_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                            "audit_kind": "source_to_dashboard_agent",
                            "source_grounded": True,
                            "validator": "independent-test-agent",
                            "validator_type": "agent",
                            "validated_at": "2026-07-25T12:00:00Z",
                            "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(
                                inventory
                            ),
                            "review_surface_sha256": review_dashboard.review_surface_digest(
                                [row]
                            ),
                            "items": {
                                "opaque_source_key": {
                                    "coverage": "covered_corrected_target",
                                    "target_kind": "approved_corrected_target",
                                    "review_rows": ["unrelated_review_row"],
                                    "review_row_signature_sha256": {
                                        "unrelated_review_row": manifest["sha256"]
                                    },
                                    "reason": "The reviewed theorem proves the explicit corrected target with its visible restriction.",
                                    "source_evidence": "The archived theorem and its corrected target are pinned in the source-map record.",
                                    "statement_sha256": inventory["opaque_source_key"][
                                        "corrected_target"
                                    ]["approval"]["target_statement_sha256"],
                                    "archival_statement_sha256": inventory["opaque_source_key"][
                                        "statement_sha256"
                                    ],
                                    "corrected_target_sha256": target[
                                        "corrected_target_sha256"
                                    ],
                                    "governing_defect_ids": ["FIXTURE-CORRECTION"],
                                    "archival_equivalence_claimed": False,
                                    "validator": "independent-test-agent",
                                    "validated_at": "2026-07-25T12:00:00Z",
                                }
                            },
                        }
                    ),
                    encoding="utf-8",
                )
                make_fixture_coverage_source_inputs_current(folder)

            write_coverage()
            archival_summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertTrue(archival_summary["source_to_lean_needs_attention"])
            self.assertEqual(
                archival_summary["row_statement_match_mismatch"],
                ["opaque_source_key -> unrelated_review_row"],
            )

            row.paper_statement = corrected
            row.agent_statement = corrected
            row.llm_match_paper_statement_sha256 = review_dashboard.statement_digest(
                corrected
            )
            write_coverage()
            corrected_summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertEqual(corrected_summary["row_statement_match_mismatch"], [])
            self.assertFalse(corrected_summary["source_to_lean_needs_attention"])

    def test_corrected_target_coverage_uses_only_the_declared_primary_endpoint(self) -> None:
        """A second correct-looking theorem cannot share corrected-target credit."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CorrectedTargetPrimaryEndpointPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            archival = "The archival theorem has an unrestricted conclusion."
            corrected = "Under the explicit finite condition, the repaired theorem holds."
            archival_location = "source.txt:30-31"
            target = {
                "schema": 1,
                "statement": corrected,
                "governing_defect_ids": ["FIXTURE-CORRECTION"],
                "archival_equivalence_claimed": False,
                "archival_source_locator": archival_location,
                "archival_source_quote_sha256": "a" * 64,
                "approval": {
                    "kind": "explicit_user_instruction",
                    "recorded_at": "2026-07-25",
                    "reference": "Only the explicit repaired target is approved.",
                    "target_statement_sha256": review_dashboard.statement_digest(
                        corrected
                    ),
                    "artifact_path": "docs/approval.md",
                    "artifact_sha256": "b" * 64,
                },
            }
            target["corrected_target_sha256"] = review_dashboard.corrected_target_digest(
                target
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "paper_coverage_required": True,
                            "llm_statement_review": {
                                "require_explicit_source_routes": True
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_url": "https://example.invalid/paper",
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {
                            "opaque_source_key": {
                                "title": "Theorem 1: Printed result",
                                "statement": archival,
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "source_location": archival_location,
                                "source_defect_ids": ["FIXTURE-CORRECTION"],
                                "coverage_status": "corrected_source_statement",
                                "lean_declarations": ["primary_endpoint"],
                                "corrected_target": target,
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            manifest = nontrivial_theorem_manifest()

            def row(name: str) -> review_dashboard.ReviewItem:
                return review_dashboard.ReviewItem(
                    name=name,
                    kind="theorem",
                    lean_statement=f"theorem {name} : 0 != 1",
                    paper_statement=corrected,
                    agent_statement=corrected,
                    lean_signature_manifest=manifest,
                    lean_signature_sha256=str(manifest["sha256"]),
                    llm_match_judgment="matches",
                    llm_match_resolution="approved_corrected_target",
                    llm_match_paper_statement_sha256=review_dashboard.statement_digest(
                        corrected
                    ),
                    llm_match_source_routes=[
                        {
                            "source_item": "opaque_source_key",
                            "source_statement_sha256": review_dashboard.statement_digest(
                                corrected
                            ),
                            "source_location": archival_location,
                            "route_kind": "approved_corrected_target",
                        }
                    ],
                )

            primary = row("primary_endpoint")
            extra = row("extra_endpoint")
            rows = [primary, extra]

            def write_coverage(row_names: list[str]) -> None:
                inventory = review_dashboard.paper_statement_inventory(folder)
                (audit / "paper_coverage_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                            "audit_kind": "source_to_dashboard_agent",
                            "source_grounded": True,
                            "validator": "independent-test-agent",
                            "validator_type": "agent",
                            "validated_at": "2026-07-25T12:00:00Z",
                            "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(
                                inventory
                            ),
                            "review_surface_sha256": review_dashboard.review_surface_digest(
                                rows
                            ),
                            "items": {
                                "opaque_source_key": {
                                    "coverage": "covered_corrected_target",
                                    "target_kind": "approved_corrected_target",
                                    "review_rows": row_names,
                                    "review_row_signature_sha256": {
                                        name: manifest["sha256"] for name in row_names
                                    },
                                    "reason": "The designated theorem proves the full explicit repaired target.",
                                    "source_evidence": "The archival source span and approved repair are pinned.",
                                    "statement_sha256": target["approval"][
                                        "target_statement_sha256"
                                    ],
                                    "archival_statement_sha256": inventory[
                                        "opaque_source_key"
                                    ]["statement_sha256"],
                                    "corrected_target_sha256": target[
                                        "corrected_target_sha256"
                                    ],
                                    "governing_defect_ids": ["FIXTURE-CORRECTION"],
                                    "archival_equivalence_claimed": False,
                                    "validator": "independent-test-agent",
                                    "validated_at": "2026-07-25T12:00:00Z",
                                }
                            },
                        }
                    ),
                    encoding="utf-8",
                )
                make_fixture_coverage_source_inputs_current(folder)

            write_coverage(["primary_endpoint"])
            accepted = review_dashboard.paper_coverage_audit_summary(folder, rows)
            self.assertFalse(accepted["source_to_lean_needs_attention"])

            write_coverage(["extra_endpoint"])
            extra_only = review_dashboard.paper_coverage_audit_summary(folder, rows)
            self.assertTrue(extra_only["source_to_lean_needs_attention"])
            self.assertEqual(extra_only["corrected_target_coverage_error_count"], 1)
            self.assertIn(
                "opaque_source_key: covered_corrected_target must link exactly",
                extra_only["corrected_target_coverage_errors"][0],
            )

            write_coverage(["primary_endpoint", "extra_endpoint"])
            mixed = review_dashboard.paper_coverage_audit_summary(folder, rows)
            self.assertTrue(mixed["source_to_lean_needs_attention"])
            self.assertEqual(mixed["corrected_target_coverage_error_count"], 1)
            self.assertIn(
                "opaque_source_key: covered_corrected_target must link exactly",
                mixed["corrected_target_coverage_errors"][0],
            )

    def test_corrected_target_coverage_accepts_only_unique_paper_interface_short_row(
        self,
    ) -> None:
        """FQN map routes may use one unique dashboard-local row component."""

        archival = "The archival theorem is too broad."
        corrected = "Under the approved finite condition, the theorem holds."
        target = {
            "schema": 1,
            "statement": corrected,
            "governing_defect_ids": ["FIXTURE-CORRECTION"],
            "archival_equivalence_claimed": False,
            "archival_source_locator": "source.txt:10-11",
            "archival_source_quote_sha256": "a" * 64,
            "approval": {
                "kind": "explicit_user_instruction",
                "recorded_at": "2026-07-26",
                "reference": "The repaired target is approved without archival equivalence.",
                "target_statement_sha256": review_dashboard.statement_digest(
                    corrected
                ),
                "artifact_path": "docs/approval.md",
                "artifact_sha256": "b" * 64,
            },
        }
        target["corrected_target_sha256"] = review_dashboard.corrected_target_digest(
            target
        )
        source_item = {
            "coverage_status": "corrected_source_statement",
            "statement": archival,
            "statement_sha256": review_dashboard.statement_digest(archival),
            "source_defect_ids": ["FIXTURE-CORRECTION"],
            "lean_declarations": [
                "FixturePaper.PaperInterface.complete_endpoint"
            ],
            "corrected_target": target,
        }
        coverage = {
            "coverage": "covered_corrected_target",
            "target_kind": "approved_corrected_target",
            "review_rows": ["complete_endpoint"],
            "statement_sha256": review_dashboard.statement_digest(corrected),
            "archival_statement_sha256": review_dashboard.statement_digest(archival),
            "corrected_target_sha256": target["corrected_target_sha256"],
            "governing_defect_ids": ["FIXTURE-CORRECTION"],
            "archival_equivalence_claimed": False,
        }
        inventory = {"source": source_item}
        coverage["review_rows"] = [
            "FixturePaper.PaperInterface.complete_endpoint"
        ]
        self.assertEqual(
            review_dashboard._corrected_target_coverage_error(
                source_item,
                coverage,
                "covered_corrected_target",
                source_inventory=inventory,
                paper_name="FixturePaper",
            ),
            "",
        )
        coverage["review_rows"] = ["complete_endpoint"]
        self.assertEqual(
            review_dashboard._corrected_target_coverage_error(
                source_item,
                coverage,
                "covered_corrected_target",
                source_inventory=inventory,
                paper_name="FixturePaper",
            ),
            "",
        )

        inventory["other"] = {
            "lean_declarations": [
                "FixturePaper.PaperInterface.Nested.complete_endpoint"
            ]
        }
        self.assertIn(
            "must link exactly the sole corrected-target endpoint",
            review_dashboard._corrected_target_coverage_error(
                source_item,
                coverage,
                "covered_corrected_target",
                source_inventory=inventory,
                paper_name="FixturePaper",
            ),
        )

    def test_direct_coverage_requires_current_elaborated_row_signature_pin(self) -> None:
        """A stable row name cannot retain coverage after its theorem type changes."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SignaturePinnedCoveragePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_statement = "Every declared instance has the checked source property."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {
                            "source_claim": {
                                "title": "Theorem 1",
                                "statement": source_statement,
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "source_url": "https://example.invalid/paper",
                                "source_location": "source.txt:1-1",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            source_digest = review_dashboard.statement_digest(source_statement)
            manifest = nontrivial_theorem_manifest()
            row = review_dashboard.ReviewItem(
                name="stable_row_name",
                kind="theorem",
                lean_statement="theorem stable_row_name : 0 != 1",
                paper_statement=source_statement,
                agent_statement=source_statement,
                lean_signature_manifest=manifest,
                lean_signature_sha256=str(manifest["sha256"]),
                llm_match_judgment="matches",
                llm_match_paper_statement_sha256=source_digest,
            )

            def write_coverage(pins: object) -> None:
                inventory = review_dashboard.paper_statement_inventory(folder)
                (audit / "paper_coverage_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                            "audit_kind": "source_to_dashboard_agent",
                            "source_grounded": True,
                            "validator": "independent-test-agent",
                            "validator_type": "agent",
                            "validated_at": "2026-07-25T12:00:00Z",
                            "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(
                                inventory
                            ),
                            "review_surface_sha256": review_dashboard.review_surface_digest(
                                [row]
                            ),
                            "items": {
                                "source_claim": {
                                    "coverage": "covered",
                                    "review_rows": ["stable_row_name"],
                                    "review_row_signature_sha256": pins,
                                    "reason": "The checked theorem establishes the exact source property.",
                                    "source_evidence": "The source claim is recorded at the pinned source location.",
                                    "statement_sha256": inventory["source_claim"]["statement_sha256"],
                                    "validator": "independent-test-agent",
                                    "validated_at": "2026-07-25T12:00:00Z",
                                }
                            },
                        }
                    ),
                    encoding="utf-8",
                )
                make_fixture_coverage_source_inputs_current(folder)

            write_coverage({})
            missing_summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertEqual(missing_summary["coverage_row_signature_error_count"], 2)
            self.assertTrue(missing_summary["needs_attention"])
            self.assertTrue(missing_summary["source_to_lean_needs_attention"])

            write_coverage({"stable_row_name": manifest["sha256"]})
            current_summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertEqual(current_summary["coverage_row_signature_errors"], [])
            self.assertFalse(current_summary["source_to_lean_needs_attention"])

            changed_manifest = normalized_fixture_manifest(theorem_manifest())
            row.lean_statement = "theorem stable_row_name : True"
            row.lean_signature_manifest = changed_manifest
            row.lean_signature_sha256 = str(changed_manifest["sha256"])
            write_coverage({"stable_row_name": manifest["sha256"]})
            stale_summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertEqual(stale_summary["coverage_row_signature_error_count"], 1)
            self.assertIn(
                "source_claim -> stable_row_name",
                stale_summary["coverage_row_signature_errors"][0],
            )
            self.assertIn(
                "missing or stale",
                stale_summary["coverage_row_signature_errors"][0],
            )

    def test_source_component_coverage_requires_the_exact_component_pin(self) -> None:
        """Component coverage is valid only for the exact pinned source component."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ComponentRoutePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_a = "The first finite component preserves the agent transport equation."
            source_b = "The second finite component preserves the strategy transport equation."
            location_a = "source.txt:30-30"
            location_b = "source.txt:31-31"
            digest_a = review_dashboard.statement_digest(source_a)
            digest_b = review_dashboard.statement_digest(source_b)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "partially formalized",
                        "review_surface": {
                            "paper_coverage_required": True,
                            "llm_statement_review": {
                                "require_explicit_source_routes": True
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_url": "https://example.invalid/paper",
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {
                            "source_component_a": {
                                "title": "Theorem 30",
                                "statement": source_a,
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "source_url": "https://example.invalid/paper",
                                "source_location": location_a,
                            },
                            "source_component_b": {
                                "title": "Theorem 31",
                                "statement": source_b,
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "source_url": "https://example.invalid/paper",
                                "source_location": location_b,
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )
            paper_statement = "The reviewed row proves the two finite transport components."
            manifest = normalized_fixture_manifest(theorem_manifest())
            row = review_dashboard.ReviewItem(
                name="component_row",
                kind="theorem",
                lean_statement="theorem component_row : True",
                paper_statement=paper_statement,
                agent_statement=paper_statement,
                lean_signature_manifest=manifest,
                lean_signature_sha256=str(manifest["sha256"]),
                llm_match_judgment="matches",
                llm_match_paper_statement_sha256=review_dashboard.statement_digest(
                    paper_statement
                ),
                llm_match_source_routes=[
                    {
                        "source_item": "source_component_a",
                        "source_statement_sha256": digest_a,
                        "source_location": location_a,
                        "route_kind": "source_component",
                        "semantic_relation": "lean_implies_source_component",
                    },
                    {
                        "source_item": "source_component_b",
                        "source_statement_sha256": digest_b,
                        "source_location": location_b,
                        "route_kind": "source_component",
                        "semantic_relation": "equivalent_source_component",
                    },
                ],
            )
            inventory = review_dashboard.paper_statement_inventory(folder)

            def write_coverage() -> None:
                (audit / "paper_coverage_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                            "audit_kind": "source_to_dashboard_agent",
                            "source_grounded": True,
                            "validator": "independent-test-agent",
                            "validator_type": "agent",
                            "validated_at": "2026-07-24T12:00:00Z",
                            "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(
                                inventory
                            ),
                            "review_surface_sha256": review_dashboard.review_surface_digest(
                                [row]
                            ),
                            "items": {
                                "source_component_a": {
                                    "coverage": "covered",
                                    "review_rows": ["component_row"],
                                    "review_row_signature_sha256": {
                                        "component_row": manifest["sha256"]
                                    },
                                    "reason": "The row establishes the first finite transport component.",
                                    "source_evidence": "The first component appears in the pinned source formula.",
                                    "statement_sha256": digest_a,
                                    "validator": "independent-test-agent",
                                    "validated_at": "2026-07-24T12:00:00Z",
                                },
                                "source_component_b": {
                                    "coverage": "covered",
                                    "review_rows": ["component_row"],
                                    "review_row_signature_sha256": {
                                        "component_row": manifest["sha256"]
                                    },
                                    "reason": "The row establishes the second finite transport component.",
                                    "source_evidence": "The second component appears in the pinned source formula.",
                                    "statement_sha256": digest_b,
                                    "validator": "independent-test-agent",
                                    "validated_at": "2026-07-24T12:00:00Z",
                                },
                            },
                        }
                    ),
                    encoding="utf-8",
                )
                make_fixture_coverage_source_inputs_current(folder)

            write_coverage()
            accepted = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertFalse(accepted["source_to_lean_needs_attention"])
            self.assertEqual(accepted["coverage_route_mismatch"], [])

            # Keep the B component exact, but remove A. The coverage ledger may
            # not use B as a semantic substitute merely because both are components.
            row.llm_match_source_routes = [row.llm_match_source_routes[1]]
            write_coverage()
            rejected = review_dashboard.paper_coverage_audit_summary(folder, [row])
            self.assertTrue(rejected["source_to_lean_needs_attention"])
            self.assertEqual(rejected["coverage_route_mismatch_count"], 1)
            self.assertIn(
                "source_component_a -> component_row",
                rejected["coverage_route_mismatch"][0],
            )

    def test_inventory_digest_includes_route_and_status_policy(self) -> None:
        """The cheap precheck must go stale when routing policy changes."""

        base = {
            "source": "audit/paper_statement_map.json",
            "statement": "Every legal input has a witness.",
            "aliases": [],
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_status": "",
            "source_note": "",
            "source_defect_ids": [],
            "lean_declarations": ["source_result"],
            "proof_lean_declarations": ["source_result"],
            "support_lean_declarations": [],
            "source_location": "source.txt:7-8",
            "source_url": "https://example.invalid/paper",
        }
        baseline = review_dashboard.paper_statement_inventory_digest({"result": base})
        route_changed = dict(base)
        route_changed["lean_declarations"] = ["different_row"]
        status_changed = dict(base)
        status_changed["source_status"] = "quarantined_source_defect"
        protocol_changed = dict(base)
        protocol_changed["protocol_role"] = "source_declared_open"
        note_changed = dict(base)
        note_changed["source_note"] = "This route now needs explicit support."
        self.assertNotEqual(
            baseline,
            review_dashboard.paper_statement_inventory_digest({"result": route_changed}),
        )
        self.assertNotEqual(
            baseline,
            review_dashboard.paper_statement_inventory_digest({"result": status_changed}),
        )
        self.assertNotEqual(
            baseline,
            review_dashboard.paper_statement_inventory_digest(
                {"result": protocol_changed}
            ),
        )
        self.assertNotEqual(
            baseline,
            review_dashboard.paper_statement_inventory_digest({"result": note_changed}),
        )

    def test_quarantined_defects_require_exact_semantic_support(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OpaquePaper"
            folder.mkdir()
            audit = folder / "audit"
            audit.mkdir()
            source_text = "First source assertion.\nSecond source assertion.\n"
            (folder / "source.txt").write_text(source_text, encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "partially formalized",
                        "review_surface": {
                            "paper_coverage_required": True,
                            "source_proof_fidelity_review": {
                                "ledger_file": "audit/source_proof_fidelity.json"
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )

            def defect(defect_id: str, line: int) -> dict[str, object]:
                return {
                    "id": defect_id,
                    "source_locator": f"source.txt:{line}",
                    "source_claim": "The printed source assertion claims the stated outcome for every admissible instance.",
                    "defect_kind": "logical_dependency",
                    "affected_source_locators": [f"source.txt:{line}"],
                    "statement_impact": "source_statement",
                    "repair_obligation": "Replace the universal printed assertion with the mathematically correct restricted conclusion.",
                    "acceptance_condition": "A concrete checked witness refutes the printed universal claim and the replacement excludes it.",
                    "resolution": "corrected_source_statement",
                    "resolution_evidence": "The recorded finite witness satisfies the model conditions and contradicts the printed conclusion.",
                }

            defects = [defect("OPAQUE-DEFECT-1", 1), defect("OPAQUE-DEFECT-2", 2)]
            defects_by_id = {str(value["id"]): value for value in defects}
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "source_artifact_path": "source.txt",
                        "source_artifact_sha256": hashlib.sha256(
                            source_text.encode("utf-8")
                        ).hexdigest(),
                        "review_status": "defects_recorded",
                        "reviewed_proof_scopes": [
                            {
                                "source_locator": "source.txt:1-2",
                                "semantic_scope": "The two printed universal assertions and their finite counterexamples.",
                                "outcome": "defect_recorded",
                            }
                        ],
                        "defects": defects,
                    }
                ),
                encoding="utf-8",
            )

            statement = "An opaque source-facing assertion."
            paper_digest = review_dashboard.statement_digest(statement)
            valid_manifest = nontrivial_theorem_manifest()
            valid_statement = "theorem route7 : 0 != 1"
            true_manifest = normalized_fixture_manifest(theorem_manifest())
            rows = [
                review_dashboard.ReviewItem(
                    name="route0",
                    kind="theorem",
                    lean_statement="def route0 : Prop := True",
                    paper_statement=statement,
                    agent_statement=statement,
                    lean_signature_manifest=proposition_spec_manifest(),
                ),
                review_dashboard.ReviewItem(
                    name="route7",
                    kind="def",
                    lean_statement=valid_statement,
                    paper_statement=statement,
                    agent_statement=statement,
                    lean_signature_manifest=valid_manifest,
                    lean_signature_sha256=str(valid_manifest["sha256"]),
                    llm_match_judgment="matches",
                    llm_match_paper_statement_sha256=paper_digest,
                ),
                review_dashboard.ReviewItem(
                    name="route8",
                    kind="theorem",
                    lean_statement="theorem route8 : True",
                    paper_statement=statement,
                    agent_statement=statement,
                    lean_signature_manifest=true_manifest,
                    lean_signature_sha256=str(true_manifest["sha256"]),
                ),
            ]
            base_source = {
                "statement": statement,
                "claim_bearing": True,
                "source_url": "https://example.invalid/paper",
                "source_location": "p. 1",
            }
            map_items: dict[str, dict[str, object]] = {
                "item0": {
                    **base_source,
                    "title": "Claim 1: Runtime guarantee",
                    "source_kind": "claim",
                    "protocol_role": "runtime_claim",
                },
                "item7": {
                    **base_source,
                    "title": "Theorem 7: Printed assertion",
                    "source_kind": "theorem",
                    "source_status": "quarantined_source_defect",
                    "source_defect_ids": ["OPAQUE-DEFECT-1"],
                    "support_lean_declarations": ["Fixture.route7"],
                },
                "item8": {
                    **base_source,
                    "title": "Corollary 8: Printed assertion",
                    "source_kind": "corollary",
                    "source_status": "quarantined_source_defect",
                    "source_defect_ids": ["OPAQUE-DEFECT-2"],
                    "support_lean_declarations": ["route8"],
                },
                "item9": {
                    **base_source,
                    "title": "Lemma 9: Printed assertion",
                    "source_kind": "lemma",
                    "source_status": "quarantined_source_defect",
                    "source_defect_ids": ["UNKNOWN-DEFECT"],
                    "support_lean_declarations": ["route7"],
                },
                "item10": {
                    **base_source,
                    "title": "Proposition 10: Printed assertion",
                    "source_kind": "proposition",
                    "source_status": "quarantined_source_defect",
                    "source_defect_ids": ["OPAQUE-DEFECT-1"],
                    "support_lean_declarations": ["route7"],
                },
                "item11": {
                    **base_source,
                    "title": "Claim 11: Source-facing property",
                    "source_kind": "claim",
                },
            }

            def write_map(values: dict[str, dict[str, object]]) -> None:
                (audit / "paper_statement_map.json").write_text(
                    json.dumps(
                        {
                            "source_curated": True,
                            "source_inventory_kind": "curated_test",
                            "source_coverage_mode": "named_theoretical_statements",
                            "items": values,
                        }
                    ),
                    encoding="utf-8",
                )

            def write_coverage(values: dict[str, dict[str, object]]) -> None:
                inventory = review_dashboard.paper_statement_inventory(folder)
                normalized_items = {
                    key: {
                        **value,
                        "reason": "Semantic source and defect-support classification.",
                        "source_evidence": "Pinned source span with explicit mathematical claim.",
                        "statement_sha256": inventory[key]["statement_sha256"],
                    }
                    for key, value in values.items()
                }
                (audit / "paper_coverage_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                            "audit_kind": "source_to_dashboard_agent",
                            "source_grounded": True,
                            "validator": "coverage-test-agent",
                            "validator_type": "agent",
                            "validated_at": "2026-07-15T12:00:00Z",
                            "source_coverage_mode": "named_theoretical_statements",
                            "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(
                                inventory
                            ),
                            "items": normalized_items,
                        }
                    ),
                    encoding="utf-8",
                )
                make_fixture_coverage_source_inputs_current(folder)

            def support_judgment(
                source_key: str,
                defect_id: str,
                row: review_dashboard.ReviewItem,
            ) -> dict[str, object]:
                inventory = review_dashboard.paper_statement_inventory(folder)
                source_defect = defects_by_id[defect_id]
                manifest = row.lean_signature_manifest
                assert isinstance(manifest, dict)
                atom = manifest["atoms"][0]
                return {
                    "source_item": source_key,
                    "source_statement_sha256": inventory[source_key]["statement_sha256"],
                    "defect_id": defect_id,
                    "source_defect": review_dashboard.source_proof_defect_snapshot(
                        source_defect
                    ),
                    "source_defect_sha256": review_dashboard.source_proof_defect_digest(
                        source_defect
                    ),
                    "support_declaration": row.name,
                    "lean_statement": row.lean_statement,
                    "lean_statement_sha256": review_dashboard.statement_digest(
                        row.lean_statement
                    ),
                    "lean_signature_sha256": manifest["sha256"],
                    "judgment": "valid_counterexample",
                    "reason": "The checked finite witness contradicts the exact universal source claim.",
                    "lean_obligations": [
                        {
                            "signature_ref": "result",
                            "role": "conclusion",
                            "signature_atom_sha256": review_dashboard.signature_manifest_atom_digest(
                                atom
                            ),
                            "defect_relevance": "counterexample_conclusion",
                            "semantic_explanation": "The conclusion records the contradictory outcome for the concrete witness.",
                        }
                    ],
                    "obligation_alignment": [
                        {
                            "source_defect_field": "source_claim",
                            "lean_signature_ref": "result",
                            "relation": "counterexample_to",
                            "semantic_basis": "The source quantifies universally, while this admissible witness has the opposite outcome.",
                            "witness_or_derivation": "The closed arithmetic proposition checks the two distinct finite values directly.",
                        }
                    ],
                }

            def write_support(values: dict[str, dict[str, object]]) -> None:
                (audit / "defect_support_match_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": review_dashboard.REQUIRED_LLM_DEFECT_SUPPORT_PROMPT_VERSION,
                            "audit_kind": "source_defect_to_lean_agent",
                            "source_grounded": True,
                            "validator": "defect-test-agent",
                            "validator_type": "agent",
                            "validated_at": "2026-07-15T12:05:00Z",
                            "items": values,
                        }
                    ),
                    encoding="utf-8",
                )

            write_map(map_items)
            write_coverage(
                {
                    "item0": {"coverage": "support_only", "support_declarations": ["route0"]},
                    "item7": {"coverage": "support_only", "support_declarations": ["route7"]},
                    "item8": {"coverage": "support_only", "support_declarations": ["route8"]},
                    "item9": {"coverage": "support_only", "support_declarations": ["route7"]},
                    "item10": {"coverage": "covered", "review_rows": ["route7"]},
                    "item11": {"coverage": "out_of_scope"},
                }
            )
            write_support(
                {
                    "judgment0": support_judgment("item7", "OPAQUE-DEFECT-1", rows[1]),
                    "judgment1": support_judgment("item8", "OPAQUE-DEFECT-2", rows[2]),
                }
            )
            summary = review_dashboard.paper_coverage_audit_summary(folder, rows)
            self.assertEqual(summary["support_only_named_claims"], ["item0"])
            self.assertEqual(summary["quarantined_defect_support"], ["item7"])
            self.assertEqual(
                summary["invalid_quarantined_defect_support"], ["item8", "item9"]
            )
            self.assertTrue(
                any(
                    "tautology" in error
                    for error in summary["defect_support_judgment_errors"]
                )
            )
            self.assertEqual(summary["quarantined_defect_direct_coverage"], ["item10"])
            self.assertEqual(summary["covered_count"], 0)
            self.assertEqual(summary["required_out_of_scope"], ["item11"])
            self.assertTrue(summary["source_to_lean_needs_attention"])

            write_map({"item7": map_items["item7"]})
            write_coverage(
                {"item7": {"coverage": "support_only", "support_declarations": ["route7"]}}
            )
            valid_judgment = support_judgment("item7", "OPAQUE-DEFECT-1", rows[1])
            write_support({"judgment0": valid_judgment})
            valid_summary = review_dashboard.paper_coverage_audit_summary(folder, rows)
            self.assertEqual(valid_summary["quarantined_defect_support_count"], 1)
            self.assertEqual(valid_summary["defect_support_judgment_error_count"], 0)
            self.assertFalse(valid_summary["source_to_lean_needs_attention"])

            valid_judgment["source_defect_sha256"] = "0" * 64
            write_support({"judgment0": valid_judgment})
            stale_summary = review_dashboard.paper_coverage_audit_summary(folder, rows)
            self.assertEqual(stale_summary["quarantined_defect_support_count"], 0)
            self.assertTrue(
                any(
                    "defect digest" in error
                    for error in stale_summary["defect_support_judgment_errors"]
                )
            )

    def test_unknown_source_kind_fails_closed_in_paper_coverage(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "UnknownKindPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            statement = "A source-facing mathematical assertion."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {
                            "item13": {
                                "statement": statement,
                                "source_url": "https://example.invalid/paper",
                                "source_location": "p. 13",
                                "source_kind": "neutral_result_shape",
                                "claim_bearing": True,
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "coverage-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-07-15T12:00:00Z",
                        "items": {
                            "item13": {
                                "coverage": "covered",
                                "review_rows": ["route13"],
                                "reason": "The elaborated proposition has the same quantified mathematical content.",
                                "source_evidence": "The complete source assertion appears at page 13.",
                                "statement_sha256": inventory["item13"]["statement_sha256"],
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            manifest = nontrivial_theorem_manifest()
            rows = [
                review_dashboard.ReviewItem(
                    name="route13",
                    kind="theorem",
                    lean_statement="theorem route13 : 0 != 1",
                    paper_statement=statement,
                    agent_statement=statement,
                    lean_signature_manifest=manifest,
                    lean_signature_sha256=str(manifest["sha256"]),
                )
            ]
            summary = review_dashboard.paper_coverage_audit_summary(folder, rows)
            self.assertEqual(summary["inventory_unknown_source_kind"], [])
            self.assertEqual(summary["inventory_unknown_source_kind_count"], 0)
            errors = summary["source_presentation_classification_errors"]
            self.assertEqual(len(errors), 1)
            self.assertIn(
                "unknown source_kind `neutral_result_shape`", errors[0]
            )
            self.assertEqual(
                summary["source_presentation_classification_error_count"], 1
            )
            self.assertTrue(summary["needs_attention"])
            self.assertTrue(summary["source_to_lean_needs_attention"])

    def test_source_inventory_precheck_catches_key_drift_without_lean_rows(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "InventoryOnlyPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            statement = "Every feasible instance has a checked witness."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_url": "https://example.invalid/paper",
                        "items": {
                            "source_result": {
                                "title": "Theorem 7: Checked witness",
                                "statement": statement,
                                "source_location": "p. 7",
                                "source_kind": "theorem",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "coverage-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-07-24T12:00:00Z",
                        "paper_statement_inventory_sha256": review_dashboard.paper_statement_inventory_digest(inventory),
                        "items": {
                            "orphaned_source_result": {
                                "coverage": "covered",
                                "review_rows": ["would_require_lean_later"],
                                "reason": "This entry intentionally tests source-map key drift.",
                                "source_evidence": "The source proof appears at page 7.",
                                "statement_sha256": "0" * 64,
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            with mock.patch.object(
                review_dashboard,
                "parse_interface_items",
                side_effect=AssertionError("inventory precheck must not parse Lean"),
            ):
                summary = review_dashboard.source_inventory_precheck_summary(folder)

            self.assertTrue(summary["needs_attention"])
            self.assertEqual(summary["missing_coverage"], ["source_result"])
            self.assertEqual(summary["extra_coverage"], ["orphaned_source_result"])
            self.assertFalse(summary["stale_inventory"])

    def test_source_map_semantic_contract_uses_meta_and_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Example"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "namespace Example\n"
                "def auditedShape (n : Nat) : Prop := n = n\n"
                "theorem renamedEvidence (value : Nat) : auditedShape value := rfl\n"
                "end Example\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["auditedShape", "renamedEvidence"],
                            "assumption_names": [],
                            "source_proof_fidelity_review": {
                                "ledger_file": "proof-ledger.json"
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            (folder / "proof-ledger.json").write_text(
                json.dumps(
                    {
                        "defects": [
                            {"id": "FIX-1", "resolution": "repaired_in_lean"}
                        ]
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "semantic_contract_schema": 1,
                        "items": {
                            "renamed_source_claim": {
                                "source_kind": "theorem",
                                "title": "Theorem 1. Repaired source result",
                                "claim_bearing": True,
                                "source_defect_ids": ["FIX-1"],
                                "lean_declarations": ["renamedEvidence"],
                                "semantic_contract": {
                                    "spec_declaration": "auditedShape",
                                    "evidence_declaration": "renamedEvidence",
                                    "evidence_mode": "proves",
                                    "semantic_shape": "plain",
                                },
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            route = ("Example.auditedShape", "Example.renamedEvidence", "proves")

            transparent = {
                "Example.auditedShape": {
                    "passes": True,
                    "failure_tag": "",
                    "failure_declaration": "",
                    "expanded": 1,
                }
            }

            def findings(
                meta_results: dict[tuple[str, str, str], bool],
                transparency_results: dict[str, dict[str, object]] | None = None,
            ) -> list[object]:
                with (
                    mock.patch.object(
                        audit_repository,
                        "library_lean_declaration_index",
                        return_value={},
                    ),
                    mock.patch.object(
                        lean_signature_manifest,
                        "run_lean_semantic_contract_matches",
                        return_value=meta_results,
                    ),
                    mock.patch.object(
                        lean_signature_manifest,
                        "run_lean_semantic_contract_transparency_checks",
                        return_value=(
                            transparent
                            if transparency_results is None
                            else transparency_results
                        ),
                    ),
                ):
                    return audit_repository.paper_statement_map_declaration_findings(
                        "Example", folder, "formalized"
                    )

            accepted = findings({route: True})
            self.assertFalse(
                any("semantic contract" in finding.message.lower() for finding in accepted),
                [finding.message for finding in accepted],
            )
            rejected = findings({route: False})
            self.assertTrue(
                any("Lean Meta did not establish semantic contract" in finding.message
                    for finding in rejected)
            )
            self.assertTrue(
                any("without a successfully Lean-checked" in finding.message
                    for finding in rejected)
            )
            opaque = findings({route: True}, {})
            self.assertTrue(
                any(
                    "transitive transparency proof" in finding.message
                    for finding in opaque
                ),
                [finding.message for finding in opaque],
            )

    def test_legacy_semantic_surface_signature_checks_are_presentation_only(self) -> None:
        """Schema-1 vocabulary is diagnostic, never default semantic credit."""

        surface = {
            "schema": 1,
            "required_structural_tokens": ["∀", "∃", "="],
            "required_terms": ["Nat"],
            "forbidden_opaque_terms": ["OpaqueBundle"],
        }
        cases = (
            (
                "literal source surface",
                "theorem route_7z : ∀ x : Nat, ∃ y : Nat, x = y := by\n"
                "  intro x\n"
                "  exact ⟨x, rfl⟩\n",
                None,
            ),
            (
                "opaque wrapper surface",
                "def OpaqueBundle : Prop := True\n"
                "theorem route_7z : OpaqueBundle := by trivial\n",
                "forbidden opaque wrapper",
            ),
            (
                "proof-body decoy",
                "theorem route_7z : True := by\n"
                "  have decoy : ∀ x : Nat, ∃ y : Nat, x = y := by\n"
                "    intro x\n"
                "    exact ⟨x, rfl⟩\n"
                "  trivial\n",
                "missing required structural",
            ),
        )
        for label, declaration, expected_failure in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir)
                (folder / "PaperInterface.lean").write_text(
                    "namespace ArbitraryFixture\n"
                    + declaration
                    + "end ArbitraryFixture\n",
                    encoding="utf-8",
                )
                (folder / "status.json").write_text(
                    json.dumps(
                        {
                            "review_surface": {
                                "include_names": ["route_7z"],
                                "assumption_names": [],
                            }
                        }
                    ),
                    encoding="utf-8",
                )
                audit = folder / "audit"
                audit.mkdir()
                (audit / "paper_statement_map.json").write_text(
                    json.dumps(
                        {
                            "items": {
                                "source_claim": {
                                    "source_kind": "theorem",
                                    "title": "Theorem 1. Fixture claim",
                                    "lean_declarations": ["route_7z"],
                                    "semantic_surface": surface,
                                }
                            }
                        }
                    ),
                    encoding="utf-8",
                )
                with mock.patch.object(
                    audit_repository, "library_lean_declaration_index", return_value={}
                ):
                    default_findings = audit_repository.paper_statement_map_declaration_findings(
                        "Example", folder, "formalized"
                    )
                    deep_findings = audit_repository.paper_statement_map_declaration_findings(
                        "Example",
                        folder,
                        "formalized",
                        presentation_hygiene=True,
                    )

                default_surface_messages = [
                    finding.message
                    for finding in default_findings
                    if "semantic_surface route" in finding.message
                ]
                deep_surface_messages = [
                    finding.message
                    for finding in deep_findings
                    if "semantic_surface route" in finding.message
                ]
                self.assertEqual(default_surface_messages, [])
                self.assertEqual(
                    bool(deep_surface_messages), expected_failure is not None
                )
                if expected_failure is not None:
                    self.assertTrue(
                        any(expected_failure in message for message in deep_surface_messages),
                        deep_surface_messages,
                    )
                else:
                    declarations = audit_repository.paper_lean_declaration_index(folder)
                    route = audit_repository.resolve_declaration_name(declarations, "route_7z")
                    self.assertEqual(len(route), 1)
                    signature = audit_repository.declaration_semantic_surface_signature(
                        route[0].source
                    )
                    self.assertIn("<declaration>", signature)
                    self.assertNotIn("route_7z", signature)

    def test_legacy_lexical_surface_cannot_supply_default_semantic_credit(self) -> None:
        """An exact source contract remains mandatory for a claim-bearing row."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace Example\n"
                "theorem evidence : True := by trivial\n"
                "end Example\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["evidence"],
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_coverage_mode": "named_theoretical_statements",
                        "semantic_contract_schema": 1,
                        "items": {
                            "source_claim": {
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "title": "Theorem 1. Fixture claim",
                                "statement": "Theorem 1. The fixture claim holds.",
                                "lean_declarations": ["evidence"],
                                "proof_lean_declarations": ["evidence"],
                                "semantic_surface": {
                                    "schema": 1,
                                    "required_structural_tokens": ["∀", "="],
                                    "required_terms": ["Nat"],
                                    "forbidden_opaque_terms": ["OpaqueBundle"],
                                },
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            with mock.patch.object(
                audit_repository, "library_lean_declaration_index", return_value={}
            ):
                findings = audit_repository.paper_statement_map_declaration_findings(
                    "Example", folder, "formalized"
                )

        messages = [finding.message for finding in findings]
        self.assertFalse(
            any("missing required structural token" in message for message in messages),
            messages,
        )
        self.assertTrue(
            any(
                "claim-bearing source item `source_claim` lacks semantic_contract"
                in message
                for message in messages
            ),
            messages,
        )

    def test_semantic_surface_reads_transparent_definition_body(self) -> None:
        declaration = audit_repository.LeanDeclaration(
            Path("Surface.lean"),
            1,
            "def",
            "arbitrary_label",
            "def arbitrary_label : Prop := ∀ x : Nat, ∃ y : Nat, x = y\n",
        )
        surface = {
            "schema": 1,
            "required_structural_tokens": ["∀", "∃", "="],
            "required_terms": ["Nat"],
            "forbidden_opaque_terms": ["OpaqueBundle"],
        }
        self.assertEqual(
            audit_repository.semantic_surface_signature_mismatches(declaration, surface),
            [],
        )

    def test_semantic_surface_keeps_result_type_lets_out_of_the_proof_boundary(self) -> None:
        """A `let ... :=` in a theorem type is not the theorem proof delimiter."""

        declaration = audit_repository.LeanDeclaration(
            Path("Surface.lean"),
            1,
            "theorem",
            "arbitrary_label",
            "theorem arbitrary_label : let model : Nat := 0; ∀ x : Nat, x = model := by\n"
            "  intro x\n"
            "  have proof_decoy : Real.exp x = Real.exp x := rfl\n"
            "  sorry\n",
        )
        surface = {
            "schema": 1,
            "required_structural_tokens": ["∀", "="],
            "required_terms": ["Nat"],
            "forbidden_opaque_terms": ["OpaqueBundle"],
        }
        signature = audit_repository.declaration_semantic_surface_signature(
            declaration.source, declaration.kind
        )
        self.assertIn("∀ x : Nat, x = model", signature)
        self.assertNotIn("proof_decoy", signature)
        self.assertEqual(
            audit_repository.semantic_surface_signature_mismatches(declaration, surface),
            [],
        )

    def test_schema2_conclusion_surface_rejects_premise_and_ratio_smuggling(self) -> None:
        """Schema 2 matches the elaborated result's terminal formula, never its route or premises."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def lit_zero() -> dict[str, object]:
            return {"tag": "lit", "value": "Lean.Literal.natVal 0"}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        zero = apply("OfNat.ofNat", const("Real"), lit_zero(), const("Zero.toOfNat0"))
        erf = apply("Fixture.erf", const("x"))
        derivative = apply(
            "HSub.hSub",
            apply("HMul.hMul", apply("Real.exp", const("x")), erf),
            apply("MeasureTheory.integral", const("measure"), const("integrand")),
        )
        terminal = apply("LT.lt", const("Real"), const("Real.instLT"), zero, derivative)
        denominator_positive = apply("LT.lt", const("Real"), const("Real.instLT"), zero, const("denominator"))
        ratio = apply("Eq", const("Real"), const("ratio"), apply("Fixture.erfRatio", const("x")))
        conclusion = {
            "tag": "let",
            "type": const("Measure"),
            "value": const("model"),
            "body": apply("And", denominator_positive, apply("And", ratio, terminal)),
            "nondep": False,
        }
        manifest = {
            "schema": 2,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "atoms": [
                {
                    "ref": "b/0",
                    "role": "assumption",
                    "binder_info": "explicit",
                    "canonical": terminal,
                    "display": "xj < xi",
                },
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": conclusion,
                    "display": "...",
                },
            ],
        }
        surface = {
            "schema": 2,
            "required_structural_tokens": ["∧", "<"],
            "required_terms": ["erf"],
            "forbidden_opaque_terms": ["C5Certificate"],
            "required_conclusion_components": [
                {
                    "selector": "rightmost_top_level_conjunct",
                    "relation": "lt",
                    "left_operand": "zero",
                    "required_semantic_features": [
                        "integral",
                        "exponential",
                        "subtraction",
                        "multiplication",
                    ],
                    "required_constant_suffixes": ["erf"],
                }
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(surface), []
        )
        self.assertEqual(
            audit_repository.semantic_surface_conclusion_component_mismatches(
                manifest, surface
            ),
            [],
        )

        ratio_only = dict(manifest)
        ratio_only["atoms"] = [
            manifest["atoms"][0],
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": apply("And", denominator_positive, ratio),
                "display": "...",
            },
        ]
        self.assertTrue(
            audit_repository.semantic_surface_conclusion_component_mismatches(
                ratio_only, surface
            )
        )

        premise_only = dict(manifest)
        premise_only["atoms"] = [
            manifest["atoms"][0],
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": ratio,
                "display": "ratio = ...",
            },
        ]
        self.assertTrue(
            audit_repository.semantic_surface_conclusion_component_mismatches(
                premise_only, surface
            )
        )

        wrong_orientation = dict(manifest)
        wrong_orientation["atoms"] = [
            manifest["atoms"][0],
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": apply("LT.lt", const("Real"), const("Real.instLT"), derivative, zero),
                "display": "derivative < 0",
            },
        ]
        self.assertTrue(
            audit_repository.semantic_surface_conclusion_component_mismatches(
                wrong_orientation, surface
            )
        )

    def test_schema2_conclusion_surface_requires_both_family_components(self) -> None:
        """A paired theorem cannot hide one distribution family's D2/D3 conditions."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        zero = apply(
            "OfNat.ofNat",
            const("Real"),
            {"tag": "lit", "value": "Lean.Literal.natVal 0"},
            const("Zero.toOfNat0"),
        )

        def d2_event(family: str) -> dict[str, object]:
            return apply(
                "LT.lt",
                const("Real"),
                const("Real.instLT"),
                zero,
                apply(
                    "MeasureTheory.integral",
                    const(f"{family}.outerIndependentPairJointLaw"),
                    apply("ite", apply(f"{family}.disagreementEvent", const("x")), const("one"), const("zero")),
                ),
            )

        def d2_gain(family: str) -> dict[str, object]:
            return apply(
                "LT.lt",
                const("Real"),
                const("Real.instLT"),
                zero,
                apply(f"{family}.jointLawDisagreementConditionalGain", const("D")),
            )

        def d3(family: str) -> dict[str, object]:
            return apply(
                "LT.lt",
                const("Real"),
                const("Real.instLT"),
                apply(
                    "MeasureTheory.integral",
                    apply("Expected.expectedSecondMoverIndependent", const(family)),
                ),
                apply(
                    "MeasureTheory.integral",
                    apply("Expected.expectedSecondMoverIndependent", const(family)),
                ),
            )

        components = [
            d2_event("Gaussian"),
            d2_gain("Gaussian"),
            d3("Gaussian"),
            d2_event("Laplace"),
            d2_gain("Laplace"),
            d3("Laplace"),
        ]
        conclusion: dict[str, object] = components[-1]
        for component in reversed(components[:-1]):
            conclusion = apply("And", component, conclusion)
        manifest = {
            "schema": 2,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": conclusion,
                    "display": "...",
                }
            ],
        }
        surface = {
            "schema": 2,
            "required_structural_tokens": ["∀", "∧", "<"],
            "required_terms": ["outerIndependentPairJointLaw"],
            "forbidden_opaque_terms": ["D2Bundle"],
            "required_conclusion_components": [
                {
                    "selector": "any_result_component",
                    "relation": "lt",
                    "left_operand": "zero",
                    "required_semantic_features": ["integral", "conditional"],
                    "required_constant_suffixes": ["disagreementEvent", "outerIndependentPairJointLaw"],
                    "min_matches": 2,
                },
                {
                    "selector": "any_result_component",
                    "relation": "lt",
                    "left_operand": "zero",
                    "required_constant_suffixes": ["jointLawDisagreementConditionalGain"],
                    "min_matches": 2,
                },
                {
                    "selector": "any_result_component",
                    "relation": "lt",
                    "required_semantic_features": ["integral"],
                    "required_constant_suffixes": ["expectedSecondMoverIndependent"],
                    "min_matches": 2,
                },
            ],
        }
        self.assertEqual(
            audit_repository.semantic_surface_conclusion_component_mismatches(
                manifest, surface
            ),
            [],
        )
        missing_laplace = dict(manifest)
        missing_laplace["atoms"] = [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": apply("And", d2_event("Gaussian"), apply("And", d2_gain("Gaussian"), d3("Gaussian"))),
                "display": "...",
            }
        ]
        self.assertTrue(
            audit_repository.semantic_surface_conclusion_component_mismatches(
                missing_laplace, surface
            )
        )

    def test_schema3_uses_exact_primitives_not_suffixes(self) -> None:
        """A locally named lookalike cannot satisfy a result-only feature."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "raw_score_map",
                    "relation": "eq",
                    "all_features": ["measure_map", "pmf_map"],
                    "quantifier_shape": {"forall": 0, "exists": 0},
                }
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(surface), []
        )

        def manifest(result: object) -> dict[str, object]:
            return {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": result,
                        "display": "result",
                    }
                ],
            }

        trusted = equality(
            apply(
                "MeasureTheory.Measure.map",
                const("raw"),
                apply("PMF.map", const("law"), const("ranking")),
            ),
            const("target"),
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(trusted), surface
            ),
            [],
        )
        spoofed_pmf_map = equality(
            apply(
                "MeasureTheory.Measure.map",
                const("raw"),
                apply("Fixture.PMF.map", const("law"), const("ranking")),
            ),
            const("target"),
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(spoofed_pmf_map), surface
            )
        )
        spoofed_map = equality(
            apply(
                "Fixture.Measure.map",
                const("raw"),
                apply("PMF.map", const("law"), const("ranking")),
            ),
            const("target"),
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(spoofed_map), surface
            )
        )

    def test_schema3_result_only_capture_reuse_and_zeta(self) -> None:
        """Bridged laws must occur in the selected result comparison itself."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def bvar(index: int) -> dict[str, object]:
            return {"tag": "bvar", "index": str(index)}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        def less_equal(left: object, right: object) -> dict[str, object]:
            return apply("LE.le", const("Fixture.Type"), const("Fixture.instLE"), left, right)

        def conjunction(left: object, right: object) -> dict[str, object]:
            return apply("And", left, right)

        def raw(label: str) -> dict[str, object]:
            return apply(
                "MeasureTheory.Measure.map",
                const(f"noise_{label}"),
                const(f"score_{label}"),
            )

        def law(label: str) -> dict[str, object]:
            return apply("PMF.map", const(f"base_{label}"), const(f"rank_{label}"))

        def bridge(law_term: object, raw_term: object) -> dict[str, object]:
            return equality(apply("PMF.toMeasure", law_term), raw_term)

        law_a, law_h, other_law = law("a"), law("h"), law("other")
        bridge_a, bridge_h = bridge(law_a, raw("a")), bridge(law_h, raw("h"))
        surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "law_a",
                    "relation": "eq",
                    "all_features": ["pmf_to_measure", "measure_map"],
                    "capture": {"feature": "pmf_law", "as": "law_a"},
                    "quantifier_shape": {"forall": 0, "exists": 0},
                },
                {
                    "id": "law_h",
                    "relation": "eq",
                    "all_features": ["pmf_to_measure", "measure_map"],
                    "capture": {
                        "feature": "pmf_law",
                        "as": "law_h",
                        "distinct_from": ["law_a"],
                    },
                    "quantifier_shape": {"forall": 0, "exists": 0},
                },
                {
                    "id": "comparison",
                    "relation": "le",
                    "requires_captures": ["law_a", "law_h"],
                    "operand_patterns": [
                        {"side": "left", "requires_captures": ["law_a"]},
                        {"side": "right", "requires_captures": ["law_h"]},
                    ],
                    "quantifier_shape": {"forall": 0, "exists": 0},
                },
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(surface), []
        )

        def manifest(result: object, *premises: object) -> dict[str, object]:
            atoms: list[dict[str, object]] = [
                {
                    "ref": f"b/{index}",
                    "role": "assumption",
                    "binder_info": "explicit",
                    "canonical": premise,
                    "display": "premise",
                }
                for index, premise in enumerate(premises)
            ]
            atoms.append(
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": result,
                    "display": "result",
                }
            )
            return {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": atoms,
            }

        passing = conjunction(bridge_a, conjunction(bridge_h, less_equal(law_a, law_h)))
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(passing), surface
            ),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(less_equal(law_a, law_h), bridge_a, bridge_h), surface
            )
        )
        missing_reuse = conjunction(
            bridge_a, conjunction(bridge_h, less_equal(other_law, law_h))
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(missing_reuse), surface
            )
        )

        let_result = {
            "tag": "let",
            "type": const("Fixture.PMF"),
            "value": law_a,
            "body": conjunction(
                bridge(bvar(0), raw("a")),
                conjunction(bridge_h, less_equal(bvar(0), law_h)),
            ),
            "nondep": False,
        }
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(let_result), surface
            ),
            [],
        )

    def test_schema3_equality_alias_capture_requires_unique_same_scope_use(self) -> None:
        """An equality alias is directional, unique, and reused without rewriting."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def bvar(index: int) -> dict[str, object]:
            return {"tag": "bvar", "index": str(index)}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        def conjunction(left: object, right: object) -> dict[str, object]:
            return apply("And", left, right)

        def exists(body: object) -> dict[str, object]:
            domain = const("Fixture.Law")
            return apply(
                "Exists",
                domain,
                {
                    "tag": "lam",
                    "binder_info": "explicit",
                    "domain": domain,
                    "body": body,
                },
            )

        def joint(label: str) -> dict[str, object]:
            return apply("Fixture.joint", const(f"parameter_{label}"))

        def construction(label: str) -> dict[str, object]:
            return apply(
                "MeasureTheory.Measure.compProd",
                const(f"left_{label}"),
                const(f"right_{label}"),
            )

        def bridge(alias: object, law: object) -> dict[str, object]:
            return equality(alias, law)

        def uses_joint(alias: object) -> dict[str, object]:
            return equality(
                apply("MeasureTheory.integral", alias, const("integrand")),
                const("target"),
            )

        def manifest(result: object) -> dict[str, object]:
            return {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": result,
                        "display": "result",
                    }
                ],
            }

        def surface(exists_count: int = 0) -> dict[str, object]:
            return {
                "schema": 3,
                "outer_binder_sha256": "0" * 64,
                "required_result_patterns": [
                    {
                        "id": "bind_joint_law",
                        "relation": "eq",
                        "all_features": ["measure_comp_prod"],
                        "operand_patterns": [
                            {
                                "side": "right",
                                "all_features": ["measure_comp_prod"],
                            }
                        ],
                        "require_distinct_operands": True,
                        "equality_alias_capture": {
                            "alias_side": "left",
                            "construction_feature": "measure_comp_prod",
                            "as": "joint_law",
                        },
                        "quantifier_shape": {"forall": 0, "exists": exists_count},
                    },
                    {
                        "id": "uses_joint_law",
                        "relation": "eq",
                        "all_features": ["integral"],
                        "requires_equality_aliases": ["joint_law"],
                        "operand_patterns": [
                            {
                                "side": "left",
                                "all_features": ["integral"],
                                "requires_equality_aliases": ["joint_law"],
                            }
                        ],
                        "quantifier_shape": {"forall": 0, "exists": exists_count},
                    },
                ],
            }

        direct_surface = surface()
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(direct_surface),
            [],
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        uses_joint(joint("a")),
                    )
                ),
                direct_surface,
            ),
            [],
        )

        # The binding is directional but not hard-coded to a particular side.
        right_alias_surface = surface()
        right_alias_surface["required_result_patterns"][0]["operand_patterns"][0][
            "side"
        ] = "left"
        right_alias_surface["required_result_patterns"][0][
            "equality_alias_capture"
        ]["alias_side"] = "right"
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(
                right_alias_surface
            ),
            [],
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(construction("right"), joint("right")),
                        uses_joint(joint("right")),
                    )
                ),
                right_alias_surface,
            ),
            [],
        )

        # A different result term cannot borrow credit through equality
        # transitivity or a separately named but structurally similar law.
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        uses_joint(joint("other")),
                    )
                ),
                direct_surface,
            )
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        conjunction(
                            equality(joint("chain"), joint("a")),
                            uses_joint(joint("chain")),
                        ),
                    )
                ),
                direct_surface,
            )
        )

        # Two candidate equality bindings are ambiguous even if only one is
        # later reused.  The surface must identify the binding uniquely.
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        conjunction(
                            bridge(joint("b"), construction("b")),
                            uses_joint(joint("a")),
                        ),
                    )
                ),
                direct_surface,
            )
        )

        # Quantifier counts remain exact, and de Bruijn index 0 from separate
        # existential branches is not a shared alias.
        scoped_surface = surface(exists_count=1)
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(scoped_surface),
            [],
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    exists(
                        conjunction(
                            bridge(bvar(0), construction("scoped")),
                            uses_joint(bvar(0)),
                        )
                    )
                ),
                scoped_surface,
            ),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        exists(bridge(bvar(0), construction("scoped"))),
                        exists(uses_joint(bvar(0))),
                    )
                ),
                scoped_surface,
            )
        )

        invalid_reuse = surface()
        invalid_reuse["required_result_patterns"][0]["allow_leaf_reuse"] = True
        self.assertTrue(
            any(
                "equality_alias_capture forbids allow_leaf_reuse" in error
                for error in audit_evidence_integrity.semantic_surface_validation_errors(
                    invalid_reuse
                )
            )
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        uses_joint(joint("a")),
                    )
                ),
                invalid_reuse,
            )
        )

        # An equality alias is not evidence by itself: a later pattern must
        # explicitly consume it from a distinct result leaf.
        unconsumed_alias = surface()
        unconsumed_alias["required_result_patterns"].pop()
        self.assertTrue(
            any(
                "must be required by a later distinct result pattern" in error
                for error in audit_evidence_integrity.semantic_surface_validation_errors(
                    unconsumed_alias
                )
            )
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(bridge(joint("a"), construction("a"))),
                unconsumed_alias,
            )
        )

        # Alias placement alone is not substantive content, and a consumer
        # cannot opt back into its producer leaf.
        alias_only_consumer = surface()
        alias_only_consumer["required_result_patterns"][1].pop("all_features")
        alias_only_consumer["required_result_patterns"][1]["operand_patterns"][0].pop(
            "all_features"
        )
        self.assertTrue(
            any(
                "requires independent semantic feature content outside the alias"
                in error
                for error in audit_evidence_integrity.semantic_surface_validation_errors(
                    alias_only_consumer
                )
            )
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        uses_joint(joint("a")),
                    )
                ),
                alias_only_consumer,
            )
        )
        reused_alias_consumer = surface()
        reused_alias_consumer["required_result_patterns"][1][
            "allow_leaf_reuse"
        ] = True
        self.assertTrue(
            any(
                "requires_equality_aliases forbids allow_leaf_reuse" in error
                for error in audit_evidence_integrity.semantic_surface_validation_errors(
                    reused_alias_consumer
                )
            )
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        uses_joint(joint("a")),
                    )
                ),
                reused_alias_consumer,
            )
        )

        # Even a syntactically valid consumer with a named feature cannot turn
        # `f alias = f alias` into a semantic use of the alias.
        self_integral = apply(
            "MeasureTheory.integral", joint("a"), const("integrand")
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(
                    conjunction(
                        bridge(joint("a"), construction("a")),
                        equality(self_integral, self_integral),
                    )
                ),
                direct_surface,
            )
        )

        # Capture identifiers form one namespace regardless of whether a
        # structural capture or equality alias appears first.
        alias_then_capture = surface()
        alias_then_capture["required_result_patterns"].append(
            {
                "id": "capture_after_alias",
                "relation": "eq",
                "all_features": ["integral"],
                "capture": {"feature": "integral", "as": "joint_law"},
                "quantifier_shape": {"forall": 0, "exists": 0},
            }
        )
        capture_then_alias = surface()
        capture_then_alias["required_result_patterns"].insert(
            0,
            {
                "id": "capture_before_alias",
                "relation": "eq",
                "all_features": ["measure_comp_prod"],
                "capture": {
                    "feature": "measure_comp_prod",
                    "as": "joint_law",
                },
                "quantifier_shape": {"forall": 0, "exists": 0},
            },
        )
        for colliding_surface in (alias_then_capture, capture_then_alias):
            self.assertTrue(
                any(
                    "must not repeat" in error
                    for error in audit_evidence_integrity.semantic_surface_validation_errors(
                        colliding_surface
                    )
                )
            )
            self.assertTrue(
                audit_repository.semantic_surface_result_pattern_mismatches(
                    manifest(
                        conjunction(
                            bridge(joint("a"), construction("a")),
                            uses_joint(joint("a")),
                        )
                    ),
                    colliding_surface,
                )
            )

    def test_schema3_descends_into_exists_and_rejects_legacy_evidence_fields(self) -> None:
        """Existential witness bodies are result structure; lexical fields are not."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def bvar(index: int) -> dict[str, object]:
            return {"tag": "bvar", "index": str(index)}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        def less_equal(left: object, right: object) -> dict[str, object]:
            return apply("LE.le", const("Fixture.Type"), const("Fixture.instLE"), left, right)

        def conjunction(left: object, right: object) -> dict[str, object]:
            return apply("And", left, right)

        def exists(body: object) -> dict[str, object]:
            domain = const("Fixture.PMF")
            return apply(
                "Exists",
                domain,
                {"tag": "lam", "binder_info": "explicit", "domain": domain, "body": body},
            )

        raw = apply(
            "MeasureTheory.Measure.map",
            const("noise"),
            const("score"),
        )
        law_h = apply("PMF.map", const("base_h"), const("rank_h"))
        bridge_a = equality(apply("PMF.toMeasure", bvar(0)), raw)
        bridge_h = equality(apply("PMF.toMeasure", law_h), raw)
        surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "witness_law",
                    "relation": "eq",
                    "all_features": ["pmf_to_measure", "measure_map"],
                    "capture": {"feature": "pmf_law", "as": "law_a"},
                    "quantifier_shape": {"forall": 0, "exists": 1},
                },
                {
                    "id": "human_law",
                    "relation": "eq",
                    "all_features": ["pmf_to_measure", "measure_map"],
                    "capture": {
                        "feature": "pmf_law",
                        "as": "law_h",
                        "distinct_from": ["law_a"],
                    },
                    "quantifier_shape": {"forall": 0, "exists": 1},
                },
                {
                    "id": "comparison",
                    "relation": "le",
                    "requires_captures": ["law_a", "law_h"],
                    "operand_patterns": [
                        {"side": "left", "requires_captures": ["law_a"]},
                        {"side": "right", "requires_captures": ["law_h"]},
                    ],
                    "quantifier_shape": {"forall": 0, "exists": 1},
                },
            ],
        }
        manifest = {
            "schema": 2,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": exists(
                        conjunction(bridge_a, conjunction(bridge_h, less_equal(bvar(0), law_h)))
                    ),
                    "display": "exists",
                }
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(surface), []
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(manifest, surface),
            [],
        )
        malformed = dict(surface)
        malformed["required_terms"] = ["rankByScore"]
        self.assertTrue(
            audit_evidence_integrity.semantic_surface_validation_errors(malformed)
        )

    def test_schema3_requires_visible_guards_and_blocks_disjuncts(self) -> None:
        """A conditional or disjunctive occurrence is not an asserted result law."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        def implication(condition: object, body: object) -> dict[str, object]:
            return {
                "tag": "forall",
                "binder_info": "explicit",
                "domain": condition,
                "domain_is_proposition": True,
                "body": body,
            }

        def manifest(result: object) -> dict[str, object]:
            return {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": result,
                        "display": "result",
                    }
                ],
            }

        mapped_law = apply("PMF.map", const("law"), const("ranking"))
        conclusion = equality(mapped_law, const("target"))
        condition = apply("ContinuousAt", const("function"), const("point"))
        unconditional_pattern = {
            "id": "mapped_law",
            "relation": "eq",
            "all_features": ["pmf_map"],
            "quantifier_shape": {"forall": 0, "exists": 0},
        }
        unguarded_surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [unconditional_pattern],
        }
        guarded_surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    **unconditional_pattern,
                    "guard_patterns": [
                        {"relation": "any", "all_features": ["continuous"]}
                    ],
                }
            ],
        }

        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(
                unguarded_surface
            ),
            [],
        )
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(guarded_surface),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(implication(condition, conclusion)), unguarded_surface
            )
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(implication(condition, conclusion)), guarded_surface
            ),
            [],
        )
        finite_nonempty_guard = apply("Finset.Nonempty", const("remaining"))
        finite_nonempty_surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    **unconditional_pattern,
                    "guard_patterns": [
                        {"relation": "any", "all_features": ["finite_nonempty"]}
                    ],
                }
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(
                finite_nonempty_surface
            ),
            [],
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(implication(finite_nonempty_guard, conclusion)),
                finite_nonempty_surface,
            ),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(implication(condition, conclusion)), finite_nonempty_surface
            )
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(apply("Or", conclusion, equality(const("left"), const("right")))),
                unguarded_surface,
            )
        )

    def test_schema3_guard_canonical_pin_is_locally_scope_normalized(self) -> None:
        """Guard pins bind exact content without retaining traversal scope labels."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def scoped_bvar(scope: int) -> dict[str, object]:
            return {"tag": "scoped_bvar", "scope": str(scope)}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        def implication(condition: object, body: object) -> dict[str, object]:
            return {
                "tag": "forall",
                "binder_info": "explicit",
                "domain": condition,
                "domain_is_proposition": True,
                "body": body,
            }

        def manifest(result: object) -> dict[str, object]:
            return {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": result,
                        "display": "result",
                    }
                ],
            }

        original_guard = equality(scoped_bvar(4), const("Fixture.bound"))
        alpha_equivalent_guard = equality(scoped_bvar(97), const("Fixture.bound"))
        changed_guard = equality(scoped_bvar(97), const("Fixture.changed_bound"))
        guard_pin = audit_repository.canonical_schema3_expression_sha256(original_guard)
        self.assertEqual(
            guard_pin,
            audit_repository.canonical_schema3_expression_sha256(alpha_equivalent_guard),
        )
        self.assertNotEqual(
            guard_pin,
            audit_repository.canonical_schema3_expression_sha256(changed_guard),
        )

        surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "guarded_result",
                    "relation": "eq",
                    "quantifier_shape": {"forall": 0, "exists": 0},
                    "guard_patterns": [
                        {"relation": "any", "canonical_sha256": guard_pin}
                    ],
                }
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(surface), []
        )
        conclusion = equality(const("Fixture.left"), const("Fixture.right"))
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(implication(alpha_equivalent_guard, conclusion)), surface
            ),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(implication(changed_guard, conclusion)), surface
            )
        )

        result_pin = audit_repository.canonical_schema3_expression_sha256(conclusion)
        result_surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "opaque_result",
                    "relation": "any",
                    "canonical_sha256": result_pin,
                    "quantifier_shape": {"forall": 0, "exists": 0},
                }
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(result_surface),
            [],
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(conclusion), result_surface
            ),
            [],
        )
        changed_conclusion = equality(
            const("Fixture.left"), const("Fixture.changed_right")
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(changed_conclusion), result_surface
            )
        )

        malformed = {
            **surface,
            "required_result_patterns": [
                {
                    **surface["required_result_patterns"][0],
                    "guard_patterns": [
                        {"relation": "any", "canonical_sha256": "A" * 64}
                    ],
                }
            ],
        }
        self.assertTrue(
            audit_evidence_integrity.semantic_surface_validation_errors(malformed)
        )

    def test_schema3_preserves_existential_witness_scope(self) -> None:
        """Coincident de Bruijn indices from separate witnesses cannot be joined."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def bvar(index: int) -> dict[str, object]:
            return {"tag": "bvar", "index": str(index)}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        def less_equal(left: object, right: object) -> dict[str, object]:
            return apply(
                "LE.le", const("Fixture.Type"), const("Fixture.instLE"), left, right
            )

        def conjunction(left: object, right: object) -> dict[str, object]:
            return apply("And", left, right)

        def exists(body: object) -> dict[str, object]:
            domain = const("Fixture.PMF")
            return apply(
                "Exists",
                domain,
                {
                    "tag": "lam",
                    "binder_info": "explicit",
                    "domain": domain,
                    "body": body,
                },
            )

        def manifest(result: object) -> dict[str, object]:
            return {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": result,
                        "display": "result",
                    }
                ],
            }

        raw = apply("MeasureTheory.Measure.map", const("noise"), const("score"))
        bridge = equality(apply("PMF.toMeasure", bvar(0)), raw)
        use_witness = less_equal(bvar(0), const("benchmark"))
        surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "witness_bridge",
                    "relation": "eq",
                    "all_features": ["pmf_to_measure", "measure_map"],
                    "capture": {"feature": "pmf_law", "as": "witness"},
                    "quantifier_shape": {"forall": 0, "exists": 1},
                },
                {
                    "id": "witness_use",
                    "relation": "le",
                    "requires_captures": ["witness"],
                    "operand_patterns": [
                        {"side": "left", "requires_captures": ["witness"]}
                    ],
                    "quantifier_shape": {"forall": 0, "exists": 1},
                },
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(surface), []
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(exists(conjunction(bridge, use_witness))), surface
            ),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(conjunction(exists(bridge), exists(use_witness))), surface
            )
        )

    def test_schema3_rejects_metadata_negation_and_leaf_reuse(self) -> None:
        """Only positive asserted operands and distinct leaves carry evidence."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def application(
            function: object, argument: object, binder_info: str
        ) -> dict[str, object]:
            return {
                "tag": "app",
                "fn": function,
                "arg": argument,
                "arg_binder_info": binder_info,
            }

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Fixture.Type"), left, right)

        def less_equal_with_metadata(left: object, right: object) -> dict[str, object]:
            current: object = const("LE.le")
            for argument, binder_info in (
                (apply("PMF.map", const("law"), const("ranking")), "implicit"),
                (
                    apply(
                        "MeasureTheory.Measure.map", const("noise"), const("score")
                    ),
                    "instImplicit",
                ),
                (left, "explicit"),
                (right, "explicit"),
            ):
                current = application(current, argument, binder_info)
            assert isinstance(current, dict)
            return current

        def manifest(result: object) -> dict[str, object]:
            return {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": result,
                        "display": "result",
                    }
                ],
            }

        metadata_surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "mapped_operands",
                    "relation": "le",
                    "all_features": ["pmf_map", "measure_map"],
                    "quantifier_shape": {"forall": 0, "exists": 0},
                }
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(metadata_surface), []
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(less_equal_with_metadata(const("left"), const("right"))),
                metadata_surface,
            )
        )

        any_continuous_surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "continuous",
                    "relation": "any",
                    "all_features": ["continuous"],
                    "quantifier_shape": {"forall": 0, "exists": 0},
                }
            ],
        }
        continuous = apply("ContinuousAt", const("function"), const("point"))
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(
                any_continuous_surface
            ),
            [],
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(continuous), any_continuous_surface
            ),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(apply("Not", continuous)), any_continuous_surface
            )
        )

        combined = equality(
            apply(
                "MeasureTheory.Measure.map",
                const("noise"),
                apply("PMF.map", const("law"), const("ranking")),
            ),
            const("target"),
        )
        distinct_leaf_surface = {
            "schema": 3,
            "outer_binder_sha256": "0" * 64,
            "required_result_patterns": [
                {
                    "id": "pmf_law",
                    "relation": "eq",
                    "all_features": ["pmf_map"],
                    "quantifier_shape": {"forall": 0, "exists": 0},
                },
                {
                    "id": "raw_law",
                    "relation": "eq",
                    "all_features": ["measure_map"],
                    "quantifier_shape": {"forall": 0, "exists": 0},
                },
            ],
        }
        reuse_opt_in_surface = {
            **distinct_leaf_surface,
            "required_result_patterns": [
                distinct_leaf_surface["required_result_patterns"][0],
                {
                    **distinct_leaf_surface["required_result_patterns"][1],
                    "allow_leaf_reuse": True,
                },
            ],
        }
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(
                distinct_leaf_surface
            ),
            [],
        )
        self.assertEqual(
            audit_evidence_integrity.semantic_surface_validation_errors(
                reuse_opt_in_surface
            ),
            [],
        )
        self.assertTrue(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(combined), distinct_leaf_surface
            )
        )
        self.assertEqual(
            audit_repository.semantic_surface_result_pattern_mismatches(
                manifest(combined), reuse_opt_in_surface
            ),
            [],
        )

    def test_schema3_outer_binder_digest_is_enforced(self) -> None:
        """A matching result cannot conceal a changed theorem interface."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Nat"), left, right)

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture\n"
                "theorem row (n : Nat) : n = n := rfl\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            declaration = audit_repository.LeanDeclaration(
                interface,
                2,
                "theorem",
                "row",
                "theorem row (n : Nat) : n = n := rfl",
            )
            manifest = {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "b/0",
                        "role": "parameter",
                        "binder_info": "explicit",
                        "canonical": const("Nat"),
                        "display": "n : Nat",
                    },
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": equality(const("n"), const("n")),
                        "display": "n = n",
                    },
                ],
            }
            expected_digest = lean_signature_manifest.signature_manifest_outer_binder_digest(
                manifest
            )
            self.assertTrue(expected_digest)
            surface = {
                "schema": 3,
                "outer_binder_sha256": expected_digest,
                "required_result_patterns": [
                    {
                        "id": "reflexive_result",
                        "relation": "eq",
                        "quantifier_shape": {"forall": 0, "exists": 0},
                    }
                ],
            }
            payload = {
                "items": {
                    "source_claim": {
                        "lean_declarations": ["Fixture.row"],
                        "semantic_surface": surface,
                    }
                }
            }
            declarations = {"Fixture.row": [declaration], "row": [declaration]}
            reviewed = {audit_repository.declaration_key(declaration)}

            def findings_for(current_manifest: dict[str, object]) -> list[object]:
                with mock.patch.object(
                    lean_signature_manifest,
                    "run_lean_signature_manifests",
                    return_value={"Fixture.row": current_manifest},
                ):
                    return audit_repository.paper_statement_map_semantic_surface_findings(
                        "Fixture", folder, "formalized", payload, declarations, reviewed
                    )

            self.assertEqual(findings_for(manifest), [])
            changed_manifest = {
                **manifest,
                "atoms": [
                    manifest["atoms"][0],
                    {
                        "ref": "b/1",
                        "role": "parameter",
                        "binder_info": "implicit",
                        "canonical": const("Int"),
                        "display": "{m : Int}",
                    },
                    manifest["atoms"][1],
                ],
            }
            changed_findings = findings_for(changed_manifest)
            self.assertTrue(
                any(
                    "changed outer elaborated binder interface" in finding.message
                    for finding in changed_findings
                ),
                [finding.message for finding in changed_findings],
            )

    def test_schema3_contract_surface_uses_literal_spec_only_after_current_meta_proof(
        self,
    ) -> None:
        """An opaque direct theorem gets Spec-surface credit only through Lean Meta."""

        def const(name: str) -> dict[str, object]:
            return {"tag": "const", "name": name, "levels": []}

        def apply(name: str, *arguments: object) -> dict[str, object]:
            current: dict[str, object] = const(name)
            for argument in arguments:
                current = {"tag": "app", "fn": current, "arg": argument}
            return current

        def equality(left: object, right: object) -> dict[str, object]:
            return apply("Eq", const("Nat"), left, right)

        literal_result = equality(const("zero"), const("zero"))
        spec_manifest = {
            "schema": 2,
            "declaration_kind": "definition",
            "conclusion_mode": "type_and_value",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {
                        "tag": "definition",
                        "type": {"tag": "sort", "level": {"tag": "zero"}},
                        "value": literal_result,
                    },
                    "display": "Prop := 0 = 0",
                }
            ],
        }
        semantic_spec_manifest = (
            audit_repository.semantic_contract_spec_definition_value_manifest(
                spec_manifest
            )
        )
        assert semantic_spec_manifest is not None
        expected_binder_digest = (
            lean_signature_manifest.signature_manifest_outer_binder_digest(
                semantic_spec_manifest
            )
        )
        opaque_evidence_manifest = {
            "schema": 2,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": const("Fixture.opaqueResult"),
                    "display": "opaqueResult",
                }
            ],
        }
        surface = {
            "schema": 3,
            "outer_binder_sha256": expected_binder_digest,
            "required_result_patterns": [
                {
                    "id": "literal_equality",
                    "relation": "eq",
                    "quantifier_shape": {"forall": 0, "exists": 0},
                }
            ],
        }

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture\n"
                "abbrev opaqueResult : Prop := (0 : Nat) = 0\n"
                "abbrev literalSpec : Prop := (0 : Nat) = 0\n"
                "theorem opaqueEvidence : opaqueResult := rfl\n"
                "theorem unrelatedEvidence : opaqueResult := rfl\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            specification = audit_repository.LeanDeclaration(
                interface,
                3,
                "abbrev",
                "literalSpec",
                "abbrev literalSpec : Prop := (0 : Nat) = 0",
            )
            evidence = audit_repository.LeanDeclaration(
                interface,
                4,
                "theorem",
                "opaqueEvidence",
                "theorem opaqueEvidence : opaqueResult := rfl",
            )
            unrelated = audit_repository.LeanDeclaration(
                interface,
                5,
                "theorem",
                "unrelatedEvidence",
                "theorem unrelatedEvidence : opaqueResult := rfl",
            )
            declarations = {
                "Fixture.literalSpec": [specification],
                "literalSpec": [specification],
                "Fixture.opaqueEvidence": [evidence],
                "opaqueEvidence": [evidence],
                "Fixture.unrelatedEvidence": [unrelated],
                "unrelatedEvidence": [unrelated],
            }
            reviewed = {
                audit_repository.declaration_key(specification),
                audit_repository.declaration_key(evidence),
                audit_repository.declaration_key(unrelated),
            }

            def payload(
                contract: dict[str, object] | None,
            ) -> dict[str, object]:
                item: dict[str, object] = {
                    "claim_bearing": True,
                    "lean_declarations": ["Fixture.opaqueEvidence"],
                    "semantic_surface": surface,
                }
                if contract is not None:
                    item["semantic_contract"] = contract
                return {
                    "semantic_contract_schema": 1,
                    "items": {"source_claim": item},
                }

            valid_contract = {
                "spec_declaration": "Fixture.literalSpec",
                "evidence_declaration": "Fixture.opaqueEvidence",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
            exact_route = (
                "Fixture.literalSpec",
                "Fixture.opaqueEvidence",
                "proves",
            )
            transparent = {
                "Fixture.literalSpec": {
                    "passes": True,
                    "failure_tag": "",
                    "failure_declaration": "",
                    "expanded": 1,
                }
            }

            manifest_requests: list[tuple[str, ...]] = []
            current_spec_manifest: dict[str, object] = spec_manifest

            def manifests(names: list[str], **_kwargs: object) -> dict[str, object]:
                manifest_requests.append(tuple(names))
                available = {
                    "Fixture.literalSpec": current_spec_manifest,
                    "Fixture.opaqueEvidence": opaque_evidence_manifest,
                }
                return {
                    name: available[name]
                    for name in names
                    if name in available
                }

            def findings_for(
                current_payload: dict[str, object],
                *,
                meta: dict[tuple[str, str, str], bool],
                transparency: dict[str, dict[str, object]] = transparent,
            ) -> list[audit_repository.Finding]:
                with (
                    mock.patch.object(
                        lean_signature_manifest,
                        "run_lean_semantic_contract_matches",
                        return_value=meta,
                    ),
                    mock.patch.object(
                        lean_signature_manifest,
                        "run_lean_semantic_contract_transparency_checks",
                        return_value=transparency,
                    ),
                    mock.patch.object(
                        lean_signature_manifest,
                        "run_lean_signature_manifests",
                        side_effect=lambda _root, _module, names, **_kwargs: manifests(
                            names
                        ),
                    ),
                ):
                    return audit_repository.paper_statement_map_semantic_surface_findings(
                        "Fixture",
                        folder,
                        "formalized",
                        current_payload,
                        declarations,
                        reviewed,
                    )

            accepted = findings_for(payload(valid_contract), meta={exact_route: True})
            self.assertEqual(accepted, [], [finding.message for finding in accepted])
            self.assertEqual(manifest_requests, [("Fixture.literalSpec",)])

            manifest_requests.clear()
            meta_rejected = findings_for(payload(valid_contract), meta={exact_route: False})
            self.assertTrue(
                any(
                    "no current Lean-Meta exact evidence-to-Spec proof" in finding.message
                    for finding in meta_rejected
                ),
                [finding.message for finding in meta_rejected],
            )
            self.assertTrue(
                any(
                    "does not expose required result pattern" in finding.message
                    for finding in meta_rejected
                ),
                [finding.message for finding in meta_rejected],
            )

            transparency_rejected = findings_for(
                payload(valid_contract), meta={exact_route: True}, transparency={}
            )
            self.assertTrue(
                any(
                    "no current Lean-AST transitive transparency receipt" in finding.message
                    for finding in transparency_rejected
                ),
                [finding.message for finding in transparency_rejected],
            )
            self.assertTrue(
                any(
                    "does not expose required result pattern" in finding.message
                    for finding in transparency_rejected
                ),
                [finding.message for finding in transparency_rejected],
            )

            current_spec_manifest = {
                **spec_manifest,
                "atoms": [
                    {
                        **spec_manifest["atoms"][0],
                        "canonical": {
                            **spec_manifest["atoms"][0]["canonical"],
                            "value": const("Fixture.changedSpecValue"),
                        },
                    }
                ],
            }
            changed_value = findings_for(payload(valid_contract), meta={exact_route: True})
            self.assertTrue(
                any(
                    "does not expose required result pattern" in finding.message
                    for finding in changed_value
                ),
                [finding.message for finding in changed_value],
            )

            current_spec_manifest = {
                **spec_manifest,
                "atoms": [
                    {
                        "ref": "b/0",
                        "role": "parameter",
                        "binder_info": "explicit",
                        "canonical": const("Nat"),
                        "display": "n : Nat",
                    },
                    spec_manifest["atoms"][0],
                ],
            }
            changed_binder = findings_for(payload(valid_contract), meta={exact_route: True})
            self.assertTrue(
                any(
                    "changed outer elaborated binder interface" in finding.message
                    for finding in changed_binder
                ),
                [finding.message for finding in changed_binder],
            )

            current_spec_manifest = spec_manifest
            manifest_requests.clear()
            missing_contract = findings_for(payload(None), meta={})
            self.assertTrue(
                any(
                    "does not expose required result pattern" in finding.message
                    for finding in missing_contract
                ),
                [finding.message for finding in missing_contract],
            )

            wrong_identity_contract = {
                **valid_contract,
                "evidence_declaration": "Fixture.unrelatedEvidence",
            }
            wrong_identity = findings_for(
                payload(wrong_identity_contract), meta={}
            )
            self.assertTrue(
                any(
                    "not the exact explicit direct coverage declaration" in finding.message
                    for finding in wrong_identity
                ),
                [finding.message for finding in wrong_identity],
            )

    def test_semantic_contract_review_membership_uses_declaration_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Example"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text("-- review surface fixture\n", encoding="utf-8")
            audit = folder / "audit"
            audit.mkdir()
            payload = {
                "semantic_contract_schema": 1,
                "items": {
                    "source_claim": {
                        "claim_bearing": True,
                        "semantic_contract": {
                            "spec_declaration": "Second.auditedShape",
                            "evidence_declaration": "Second.renamedEvidence",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    }
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            first_spec = audit_repository.LeanDeclaration(
                folder / "First.lean",
                1,
                "def",
                "auditedShape",
                "def auditedShape : Prop := (0 : Nat) = 0",
            )
            second_spec = audit_repository.LeanDeclaration(
                folder / "Second.lean",
                1,
                "def",
                "auditedShape",
                "def auditedShape : Prop := (0 : Nat) = 0",
            )
            first_evidence = audit_repository.LeanDeclaration(
                folder / "First.lean",
                2,
                "theorem",
                "renamedEvidence",
                "theorem renamedEvidence : auditedShape := by rfl",
            )
            second_evidence = audit_repository.LeanDeclaration(
                folder / "Second.lean",
                2,
                "theorem",
                "renamedEvidence",
                "theorem renamedEvidence : auditedShape := by rfl",
            )
            declarations = {
                "auditedShape": [first_spec, second_spec],
                "First.auditedShape": [first_spec],
                "Second.auditedShape": [second_spec],
                "renamedEvidence": [first_evidence, second_evidence],
                "First.renamedEvidence": [first_evidence],
                "Second.renamedEvidence": [second_evidence],
            }
            status_payload = {
                "review_surface": {
                    "include_names": [
                        "First.auditedShape",
                        "First.renamedEvidence",
                    ],
                    "assumption_names": [],
                }
            }
            with mock.patch.object(
                lean_signature_manifest,
                "run_lean_semantic_contract_matches",
                return_value={
                    (
                        "Second.auditedShape",
                        "Second.renamedEvidence",
                        "proves",
                    ): True
                },
            ), mock.patch.object(
                lean_signature_manifest,
                "run_lean_semantic_contract_transparency_checks",
                return_value={
                    "Second.auditedShape": {
                        "passes": True,
                        "failure_tag": "",
                        "failure_declaration": "",
                        "expanded": 0,
                    }
                },
            ):
                findings = audit_repository.paper_statement_map_semantic_contract_findings(
                    "Example",
                    folder,
                    "formalized",
                    payload,
                    declarations,
                    {"auditedShape", "renamedEvidence"},
                    status_payload,
                )
            self.assertTrue(
                any(
                    "outside the configured review surface" in finding.message
                    for finding in findings
                ),
                [finding.message for finding in findings],
            )

    def test_semantic_contract_resolves_root_namespace_declaration(self) -> None:
        declaration = audit_repository.LeanDeclaration(
            Path("RootSurface.lean"), 1, "def", "rootSpec", ""
        )
        self.assertEqual(
            audit_repository._qualified_contract_declaration_name(
                {"rootSpec": [declaration]}, "rootSpec"
            ),
            "rootSpec",
        )

    def test_quarantined_source_defect_cannot_claim_auxiliary_coverage(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace Example\n"
                "theorem evidence : True := by trivial\n"
                "theorem legacy : True := by trivial\n"
                "end Example\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["evidence"],
                            "assumption_names": [],
                            "auxiliary_names": ["legacy"],
                            "quarantined_auxiliary_names": ["legacy"],
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps({"defects": [{"id": "EXAMPLE-DEFECT-1"}]}),
                encoding="utf-8",
            )
            statement_map = audit / "paper_statement_map.json"

            def findings_for(item: dict[str, object]) -> list[audit_repository.Finding]:
                statement_map.write_text(
                    json.dumps(
                        {
                            "source_coverage_mode": "named_theoretical_statements",
                            "items": {"theorem_1": item},
                        }
                    ),
                    encoding="utf-8",
                )
                with mock.patch.object(
                    audit_repository, "library_lean_declaration_index", return_value={}
                ):
                    return audit_repository.paper_statement_map_declaration_findings(
                        "Example", folder, "formalized"
                    )

            routed_through_legacy = findings_for(
                {
                    "source_kind": "theorem",
                    "source_status": "quarantined_source_defect",
                    "source_defect_ids": ["EXAMPLE-DEFECT-1"],
                    "support_lean_declarations": ["evidence"],
                    "lean_declarations": ["legacy"],
                }
            )
            self.assertTrue(
                any("routes source item(s) through quarantined" in f.message
                    for f in routed_through_legacy)
            )

            support_only_legacy_provenance = findings_for(
                {
                    "source_kind": "theorem",
                    "aliases": ["legacy"],
                    "lean_declarations": ["evidence"],
                    "support_lean_declarations": ["legacy"],
                }
            )
            self.assertFalse(
                any("routes source item(s) through quarantined" in f.message
                    for f in support_only_legacy_provenance),
                [finding.message for finding in support_only_legacy_provenance],
            )

            clean_quarantine = findings_for(
                {
                    "source_kind": "theorem",
                    "source_status": "quarantined_source_defect",
                    "source_defect_ids": ["EXAMPLE-DEFECT-1"],
                    "support_lean_declarations": ["evidence"],
                }
            )
            self.assertEqual(clean_quarantine, [])

            missing_ledger_evidence = findings_for(
                {
                    "source_kind": "theorem",
                    "source_status": "quarantined_source_defect",
                    "source_defect_ids": ["MISSING-DEFECT"],
                    "support_lean_declarations": ["evidence"],
                }
            )
            self.assertTrue(
                any("absent from the source-proof-fidelity ledger" in f.message
                    for f in missing_ledger_evidence)
            )

    def test_tracked_artifact_scan_ignores_deleted_worktree_paths(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            rel = "papers/Example/DependencyDAG.pdf"
            path = root / rel
            path.parent.mkdir(parents=True)
            path.write_bytes(b"%PDF-1.5\n")
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "git_ls_files", return_value=[rel]),
            ):
                present = audit_repository.check_tracked_artifacts(include_active=True)
                self.assertTrue(
                    any("legacy root-level DAG alias" in f.message for f in present)
                )

                path.unlink()
                deleted = audit_repository.check_tracked_artifacts(include_active=True)
                self.assertEqual(deleted, [])


class ReviewSurfaceRouteTests(unittest.TestCase):
    def machine_status_findings_for(
        self,
        paper_entry: dict[str, object],
        *,
        aggregate_entry: dict[str, object] | None = None,
        sidecar_statuses: list[object] | None = None,
        assumption_source: str | None = None,
        source_map: object | None = None,
    ) -> list[audit_repository.Finding]:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper = papers / str(paper_entry["id"])
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "namespace ExamplePaper\n"
                "theorem paper_row : True := by trivial\n"
                "end ExamplePaper\n",
                encoding="utf-8",
            )
            (paper / "AuditInterface.lean").write_text(
                "import ExamplePaper.PaperInterface\n",
                encoding="utf-8",
            )
            if assumption_source is not None:
                (paper / "Assumptions.lean").write_text(
                    assumption_source,
                    encoding="utf-8",
                )
            if source_map is not None:
                audit = paper / "audit"
                audit.mkdir()
                (audit / "paper_statement_map.json").write_text(
                    json.dumps(source_map),
                    encoding="utf-8",
                )
            aggregate = {
                "schema": 1,
                "papers": [aggregate_entry if aggregate_entry is not None else paper_entry],
            }
            (papers / "status.json").write_text(json.dumps(aggregate), encoding="utf-8")
            (paper / "status.json").write_text(json.dumps(paper_entry), encoding="utf-8")

            def collect_sidecar_status(
                _paper_id: str,
                _folder: Path,
                status: object,
                **_kwargs: object,
            ) -> list[audit_repository.Finding]:
                if sidecar_statuses is not None:
                    sidecar_statuses.append(status)
                return []

            patches = (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(audit_repository, "PAPER_STATUS_FILE", papers / "status.json"),
                mock.patch.object(
                    audit_repository,
                    "paper_statement_sidecar_findings",
                    side_effect=collect_sidecar_status,
                ),
                mock.patch.object(audit_repository, "paper_lean_declaration_index", return_value={}),
                mock.patch.object(audit_repository, "current_statement_conditional_boundary_rows", return_value=set()),
                mock.patch.object(audit_repository, "check_source_record_audit", return_value=[]),
                mock.patch.object(audit_repository, "check_proposition_spec_routes", return_value=[]),
            )
            with ExitStack() as stack:
                for patcher in patches:
                    stack.enter_context(patcher)
                return audit_repository.check_machine_paper_status(
                    paper_filter=str(paper_entry["id"])
                )

    def base_machine_status_entry(self) -> dict[str, object]:
        return {
            "id": "ExamplePaper",
            "title": "Example Paper",
            "source_version": "source",
            "build_target": "lake build ExamplePaper",
            "status": "formalized",
            "review_entrypoint": "papers/ExamplePaper/FINAL_VALIDATION_REPORT.md",
            "human_review": {
                "reviewed_rows": 0,
                "total_rows": 1,
                "stale_rows": 0,
                "mismatch_rows": 0,
            },
            "paper_interface": {
                "path": "papers/ExamplePaper/PaperInterface.lean",
                "line_count": 3,
                "declaration_rows": 1,
                "review_rows": 1,
            },
            "review_surface": {
                "source_file": "papers/ExamplePaper/PaperInterface.lean",
                "include_names": ["paper_row"],
                "assumption_names": [],
                "auxiliary_names": [],
            },
        }

    def test_machine_status_rejects_auditinterface_review_source(self) -> None:
        entry = self.base_machine_status_entry()
        entry["review_surface"]["source_file"] = "papers/ExamplePaper/AuditInterface.lean"

        findings = self.machine_status_findings_for(entry)

        self.assertTrue(
            any("review_surface.source_file` must be `PaperInterface.lean" in f.message for f in findings)
        )

    def test_machine_status_rejects_obsolete_audit_surface_path_even_with_paperinterface_source(self) -> None:
        entry = self.base_machine_status_entry()
        entry["paper_interface"]["audit_surface_path"] = "papers/ExamplePaper/AuditInterface.lean"

        findings = self.machine_status_findings_for(entry)

        self.assertTrue(
            any("paper_interface.audit_surface_path` is obsolete" in f.message for f in findings)
        )

    def test_machine_status_rejects_noncanonical_paperinterface_path(self) -> None:
        entry = self.base_machine_status_entry()
        entry["paper_interface"]["path"] = "papers/ExamplePaper/AuditInterface.lean"

        findings = self.machine_status_findings_for(entry)

        self.assertTrue(
            any("paper_interface.path` must point to `papers/ExamplePaper/PaperInterface.lean" in f.message for f in findings)
        )

    def test_machine_status_treats_line_count_as_release_navigation(self) -> None:
        entry = self.base_machine_status_entry()
        entry["paper_interface"]["line_count"] = 999

        findings = self.machine_status_findings_for(entry)
        line_findings = [
            finding
            for finding in findings
            if "display line_count" in finding.message
        ]

        self.assertEqual(len(line_findings), 1)
        self.assertEqual(line_findings[0].severity, "WARN")

    def test_source_claim_human_denominator_uses_configured_claim_slices(self) -> None:
        entry = self.base_machine_status_entry()
        entry["human_review"]["surface"] = "source_claims_v1"
        entry["human_review"]["total_rows"] = 1
        entry["paper_interface"]["review_rows"] = 2
        surface = entry["review_surface"]
        surface["include_names"] = ["paper_row", "support_row"]
        surface["require_v11_raw_source_spec_screening"] = True
        surface["proposition_spec_proofs"] = {
            "paper_row": "paper_row_proof",
            "support_row": "support_row_proof",
        }
        surface["slices"] = [
            {"id": "main", "title": "Main claims", "names": ["paper_row"]}
        ]

        findings = self.machine_status_findings_for(entry)

        self.assertFalse(
            any("human_review.total_rows" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_graph_native_source_condition_denominator_is_not_an_assumption_count(self) -> None:
        entry = self.base_machine_status_entry()
        entry["human_review"]["surface"] = "source_claims_v1"
        entry["human_review"]["total_rows"] = 2
        surface = entry["review_surface"]
        surface["include_names"] = ["paper_row"]
        surface["require_v11_raw_source_spec_screening"] = True
        surface["source_condition_items"] = ["condition"]

        findings = self.machine_status_findings_for(
            entry,
            source_map={
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "semantic_contract": {
                            "spec_declaration": "ExamplePaper.paper_row",
                            "evidence_declaration": "ExamplePaper.paper_row",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    },
                    "condition": {
                        "source_kind": "condition",
                        "inventory_role": "source_semantic_declaration",
                        "lean_declarations": ["ExamplePaper.ModelCondition"],
                    },
                }
            },
        )

        self.assertFalse(
            any("human_review.total_rows" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_paper_filter_uses_local_status_when_generated_aggregate_is_stale(self) -> None:
        local_entry = self.base_machine_status_entry()
        aggregate_entry = json.loads(json.dumps(local_entry))
        aggregate_entry["status"] = "paper draft"
        aggregate_review_surface = aggregate_entry["review_surface"]
        assert isinstance(aggregate_review_surface, dict)
        aggregate_review_surface["source_file"] = (
            "papers/ExamplePaper/AuditInterface.lean"
        )
        sidecar_statuses: list[object] = []

        findings = self.machine_status_findings_for(
            local_entry,
            aggregate_entry=aggregate_entry,
            sidecar_statuses=sidecar_statuses,
        )

        self.assertEqual(sidecar_statuses, ["formalized"])
        self.assertTrue(
            any("aggregate entry is out of sync" in finding.message for finding in findings)
        )
        self.assertFalse(
            any(
                "review_surface.source_file` must be `PaperInterface.lean"
                in finding.message
                for finding in findings
            )
        )

    def test_machine_status_fails_closeout_when_semantic_projection_is_unavailable(self) -> None:
        entry = self.base_machine_status_entry()
        entry["review_surface"]["semantic_model_review"] = {"schema": 2}

        findings = self.machine_status_findings_for(entry)

        self.assertTrue(
            any(
                finding.severity == "ERROR"
                and "cannot safely project normal named-theory hidden-premise auditing"
                in finding.message
                and "Retained the complete PaperInterface audit surface" in finding.message
                for finding in findings
            )
        )

    def test_status_sync_validator_rejects_non_paperinterface_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "ExamplePaper"
            folder.mkdir(parents=True)
            entry = self.base_machine_status_entry()
            entry["paper_interface"]["audit_surface_path"] = "papers/ExamplePaper/AuditInterface.lean"
            entry["review_surface"]["human_source_file"] = "papers/ExamplePaper/AuditInterface.lean"

            with mock.patch.object(sync_paper_status, "ROOT", root):
                errors = sync_paper_status.validate_review_surface_routes([(folder, entry)])

        self.assertTrue(any("audit_surface_path is obsolete" in error for error in errors))
        self.assertTrue(any("review_surface.human_source_file must be" in error for error in errors))

    def test_legacy_postpaperaudit_does_not_force_root_import(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            folder = papers / "ExamplePaper"
            folder.mkdir(parents=True)
            (papers / "ExamplePaper.lean").write_text(
                "import ExamplePaper.PaperInterface\n",
                encoding="utf-8",
            )
            (folder / "PaperInterface.lean").write_text(
                "namespace ExamplePaper\n"
                "abbrev paper_definition : Prop := True\n"
                "theorem paper_row : paper_definition := by trivial\n"
                "end ExamplePaper\n",
                encoding="utf-8",
            )
            (folder / "PostPaperAudit.lean").write_text(
                "import ExamplePaper.PaperInterface\n"
                "/- Legacy implementation-facing proof ledger. See `PaperInterface.lean`. -/\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}),
                encoding="utf-8",
            )

            with (
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = audit_repository.check_post_paper_audit_interfaces(
                    include_active=True
                )

        self.assertFalse(
            any("PostPaperAudit.lean" in f.message and "root should import" in f.message for f in findings)
        )

    def test_zero_row_review_surface_rejects_paper_local_import_shim(self) -> None:
        self.assertTrue(
            audit_repository.zero_row_review_surface_imports_paper_module(
                "ExamplePaper",
                "import ExamplePaper.AuditInterface\n\n/- empty review surface -/\n",
                [],
            )
        )

        self.assertFalse(
            audit_repository.zero_row_review_surface_imports_paper_module(
                "ExamplePaper",
                "/- empty review surface -/\n",
                [],
            )
        )

        self.assertFalse(
            audit_repository.zero_row_review_surface_imports_paper_module(
                "ExamplePaper",
                "import ExamplePaper.AuditInterface\n\ndef paper_row : Prop := True\n",
                ["paper_row"],
            )
        )

    def test_empty_review_surface_allowance_is_draft_only_and_explicit(self) -> None:
        payload: dict[str, object] = {
            "status": "paper draft",
            "human_review": {"total_rows": 0},
            "review_surface": {
                "include_names": [],
                "assumption_names": [],
                "auxiliary_names": [],
            },
        }
        self.assertTrue(audit_repository.status_allows_empty_review_surface(payload))

        payload["status"] = "formalized"
        self.assertFalse(audit_repository.status_allows_empty_review_surface(payload))

        payload["status"] = "paper draft"
        payload["review_surface"] = {
            "include_names": ["paper_row"],
            "assumption_names": [],
            "auxiliary_names": [],
        }
        self.assertFalse(audit_repository.status_allows_empty_review_surface(payload))

        payload["review_surface"] = {
            "include_names": [],
            "assumption_names": [],
            "auxiliary_names": [],
        }
        payload["human_review"] = {"total_rows": 1}
        self.assertFalse(audit_repository.status_allows_empty_review_surface(payload))

    def test_tuple_witness_gate_reads_result_type_not_name(self) -> None:
        interface_text = """theorem theorem3_iidProduct_selected_witness_statement
    (h : True) : True := by
  trivial

def actual_tuple_witness_statement : Nat × Nat := (0, 0)
"""

        flagged = audit_repository.interface_tuple_witness_declarations(interface_text)

        self.assertEqual(flagged, [(5, "actual_tuple_witness_statement")])

    def test_auxiliary_names_must_be_exported_from_paperinterface(self) -> None:
        missing = audit_repository.auxiliary_names_not_exported_from_review_source(
            {"paperFormula", "AuditOnlyHelper"},
            ["reviewed", "paperFormula"],
        )

        self.assertEqual(missing, ["AuditOnlyHelper"])

    def test_machine_status_accepts_exact_configured_assumptions_auxiliary(self) -> None:
        entry = self.base_machine_status_entry()
        entry["review_surface"]["auxiliary_names"] = ["opaque_support_alias"]

        findings = self.machine_status_findings_for(
            entry,
            assumption_source=(
                "namespace ExamplePaper\n"
                "abbrev opaque_support_alias : Prop := True\n"
                "end ExamplePaper\n"
            ),
        )

        self.assertFalse(
            any(
                "opaque_support_alias" in finding.message
                and "auxiliary" in finding.message.lower()
                for finding in findings
            )
        )
        self.assertFalse(
            any("human_review.total_rows" in finding.message for finding in findings)
        )

    def test_machine_status_does_not_infer_assumptions_auxiliary_from_name(self) -> None:
        entry = self.base_machine_status_entry()
        entry["review_surface"]["auxiliary_names"] = ["opaque_support_alias"]

        findings = self.machine_status_findings_for(
            entry,
            assumption_source=(
                "namespace ExamplePaper\n"
                "abbrev assumption_opaque_support_alias : Prop := True\n"
                "end ExamplePaper\n"
            ),
        )

        self.assertTrue(
            any(
                "opaque_support_alias" in finding.message
                and "Assumptions.lean" in finding.message
                for finding in findings
            )
        )

    def test_assumptions_declaration_does_not_satisfy_include_names(self) -> None:
        entry = self.base_machine_status_entry()
        entry["review_surface"]["include_names"] = [
            "paper_row",
            "opaque_support_alias",
        ]
        entry["human_review"]["total_rows"] = 2

        findings = self.machine_status_findings_for(
            entry,
            assumption_source=(
                "namespace ExamplePaper\n"
                "theorem opaque_support_alias : True := by trivial\n"
                "end ExamplePaper\n"
            ),
        )

        self.assertTrue(
            any(
                "status names are not exported by the review surface" in finding.message
                and "opaque_support_alias" in finding.message
                for finding in findings
            )
        )

    def test_reviewed_names_must_be_declared_in_paperinterface(self) -> None:
        declaration_blocks = review_surface_structure.review_declaration_blocks(
            "import ExamplePaper.AuditInterface\n"
            "namespace ExamplePaper\n"
            "export AuditInterface (paper_row)\n"
            "theorem local_row : True := by trivial\n"
            "end ExamplePaper\n"
        )

        missing = audit_repository.reviewed_names_not_declared_in_review_source(
            ["paper_row", "local_row"],
            declaration_blocks,
        )

        self.assertEqual(missing, ["paper_row"])

    def test_multiline_declaration_is_indexed_and_visible(self) -> None:
        interface_text = (
            "namespace ExamplePaper\n"
            "theorem\n"
            "  folded_row : True := by trivial\n"
            "end ExamplePaper\n"
        )

        self.assertEqual(
            review_surface_structure.review_rows_from_interface_text(interface_text),
            [(2, "folded_row")],
        )
        self.assertIn(
            "folded_row",
            review_surface_structure.review_declaration_blocks(interface_text),
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ExamplePaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                interface_text, encoding="utf-8"
            )
            declarations = audit_repository.paper_lean_declaration_index(folder)

        self.assertEqual(
            len(
                audit_repository.resolve_declaration_name(
                    declarations, "ExamplePaper.folded_row"
                )
            ),
            1,
        )
    def test_method_style_declaration_is_indexed_with_its_full_name(self) -> None:
        interface_text = (
            "namespace ExamplePaper\n"
            "namespace PaperInterface\n"
            "structure EndpointVariation where\n"
            "  witness : True\n"
            "theorem EndpointVariation.zero_density_reward_eq : True := by trivial\n"
            "end PaperInterface\n"
            "end ExamplePaper\n"
        )

        self.assertEqual(
            review_surface_structure.review_rows_from_interface_text(interface_text),
            [
                (3, "EndpointVariation"),
                (5, "EndpointVariation.zero_density_reward_eq"),
            ],
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ExamplePaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                interface_text, encoding="utf-8"
            )
            declarations = audit_repository.paper_lean_declaration_index(folder)
            dashboard_rows = review_dashboard.parse_review_source_declarations(
                folder / "PaperInterface.lean"
            )

        self.assertEqual(
            len(
                audit_repository.resolve_declaration_name(
                    declarations,
                    "ExamplePaper.PaperInterface.EndpointVariation.zero_density_reward_eq",
                )
            ),
            1,
        )
        self.assertIn(
            (
                "theorem",
                "EndpointVariation.zero_density_reward_eq",
                "ExamplePaper.PaperInterface.EndpointVariation.zero_density_reward_eq",
                "theorem EndpointVariation.zero_density_reward_eq : True",
                None,
                5,
                folder / "PaperInterface.lean",
            ),
            dashboard_rows,
        )

    def test_hidden_premise_scan_excludes_existential_result_witnesses(self) -> None:
        declaration = (
            "theorem paper_row (h : SourceAssumption) : "
            "∃ (M : SourceModel), Conclusion M := by trivial"
        )

        self.assertEqual(
            audit_repository.hidden_premise_binders(declaration, set()),
            ["h : SourceAssumption"],
        )
        self.assertNotIn(
            "M", audit_repository.declaration_explicit_binder_prefix(declaration)
        )

    def test_individual_direct_source_route_requires_exact_receipt_pins(self) -> None:
        declaration_sha = "a" * 64
        signature_sha = "b" * 64
        item = {
            "source_statement_association": {
                "schema": 2,
                "role": "direct_source_route",
                "association_origin": "explicit_source_map_direct_route",
                "review_scope": "individual_row_only",
                "structural_pairing": "not_applicable_direct_source_route",
                "semantic_association_sha256": "c" * 64,
                "reviewed_declaration_identity": {
                    "qualified_declaration": "ExamplePaper.arbitrary_bundle_name",
                    "declaration_sha256": declaration_sha,
                },
                "reviewed_elaborated_signature_identity": {
                    "qualified_declaration": "ExamplePaper.arbitrary_bundle_name",
                    "elaborated_signature_sha256": signature_sha,
                },
                "source_item_identities": [
                    {
                        "source_key": "theorem_2",
                        "source_kind": "theorem",
                        "source_location": "source.txt:10-20",
                        "source_map_item_sha256": "d" * 64,
                        "source_semantic_sha256": "e" * 64,
                    }
                ],
            }
        }

        self.assertTrue(
            audit_repository.semantic_model_item_has_individual_direct_source_route(
                item,
                qualified_declaration="ExamplePaper.arbitrary_bundle_name",
                declaration_sha256=declaration_sha,
                elaborated_signature_sha256=signature_sha,
            )
        )
        item["source_statement_association"]["source_item_identities"].append(  # type: ignore[index]
            {"source_key": "second"}
        )
        self.assertFalse(
            audit_repository.semantic_model_item_has_individual_direct_source_route(
                item,
                qualified_declaration="ExamplePaper.arbitrary_bundle_name",
                declaration_sha256=declaration_sha,
                elaborated_signature_sha256=signature_sha,
            )
        )


class SemanticCorrectedScopeAuditTests(unittest.TestCase):
    def test_assumption_ledger_uses_configured_declarations_not_name_prefixes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "Assumptions.lean"
            path.write_text(
                "abbrev source_visible_condition : Prop := True\n"
                "abbrev assumption_internal_helper : Prop := True\n",
                encoding="utf-8",
            )

            declarations = review_surface_structure.assumption_declarations_from_text(
                path.read_text(encoding="utf-8"), {"source_visible_condition"}
            )

        self.assertEqual(set(declarations), {"source_visible_condition"})


    def test_current_corrected_model_premise_bridge_is_exact_and_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture\n"
                "structure RootModel (index : Nat) where\n"
                "  nested : NestedModel index\n"
                "structure NestedModel (index : Nat) where\n"
                "  witness : True\n"
                "structure ForeignModel where\n"
                "  witness : True\n"
                "namespace PaperInterface\n"
                "theorem model_row (n : Nat) (arbitrary_name : RootModel n) : True := by trivial\n"
                "theorem selected_nested_row (n : Nat) (unrelated_name : Fixture.NestedModel n) : True := by trivial\n"
                "theorem out_of_mode_row (n : Nat) (out_of_mode_name : RootModel n) : True := by trivial\n"
                "theorem ambiguous_row (n : Nat) (candidate : NestedModel n) : True := by trivial\n"
                "theorem foreign_row (foreign : ForeignModel) : True := by trivial\n"
                "theorem unreviewed_row (n : Nat) (unreviewed : Fixture.NestedModel n) : True := by trivial\n"
                "end PaperInterface\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            (folder / "Other.lean").write_text(
                "namespace Other\n"
                "structure NestedModel (index : Nat) where\n"
                "  witness : True\n"
                "end Other\n",
                encoding="utf-8",
            )
            interface_path = str(interface.resolve())
            source_sha = hashlib.sha256(interface.read_bytes()).hexdigest()
            direct_field = {
                "judgment_key": "Fixture.RootModel.nested",
                "structure": "Fixture.RootModel",
                "path": "Fixture.RootModel -> Fixture.RootModel.nested",
                "nested_structures": ["Fixture.NestedModel"],
            }
            nested_field = {
                "judgment_key": "Fixture.NestedModel.witness",
                "structure": "Fixture.NestedModel",
                "path": (
                    "Fixture.RootModel -> Fixture.RootModel.nested -> "
                    "Fixture.NestedModel.witness"
                ),
                "nested_structures": [],
            }
            raw_audit = {
                "review_interface_source": {
                    "path": interface_path,
                    "sha256": source_sha,
                },
                "source_record_input_fingerprint": {
                    "review_interface_source": {
                        "path": interface_path,
                        "sha256": source_sha,
                    }
                },
                "recursive_field_items": [direct_field, nested_field],
                "configured_review_rows": [
                    {
                        "row": "model_row",
                        "qualified_declaration": "Fixture.PaperInterface.model_row",
                        "source_file": interface_path,
                        "source_sha256": source_sha,
                        "elaborated_signature_sha256": "b" * 64,
                    },
                    {
                        "row": "selected_nested_row",
                        "qualified_declaration": (
                            "Fixture.PaperInterface.selected_nested_row"
                        ),
                        "source_file": interface_path,
                        "source_sha256": source_sha,
                        "elaborated_signature_sha256": "c" * 64,
                    }
                ],
                "out_of_mode_review_surface_rows": [
                    "out_of_mode_row",
                    "ambiguous_row",
                    "foreign_row",
                ],
                "expected_semantic_model_judgment_keys": [
                    "semantic-model::model_row",
                    "semantic-model::selected_nested_row",
                ],
                "semantic_model_items": [
                    {
                        "judgment_key": "semantic-model::model_row",
                        "qualified_declaration": "Fixture.PaperInterface.model_row",
                        "expanded_lean_surface": {
                            "binder_domains": [
                                {
                                    "expanded_type": "Nat",
                                    "alpha_normalized_type": "Nat",
                                },
                                {
                                    "expanded_type": "RootModel n",
                                    "alpha_normalized_type": "RootModel _f0",
                                },
                            ],
                            "record_roots": ["Fixture.RootModel"],
                        },
                        "record_input_bindings": [
                            {
                                "binder_names": ["arbitrary_name"],
                                "record_roots": ["Fixture.RootModel"],
                                "source_type_canonical": "RootModel n",
                                "expanded_type": "RootModel n",
                                "alpha_normalized_type": "RootModel _f0",
                                "fully_qualified_expanded_type_canonical": (
                                    "Fixture.RootModel n"
                                ),
                            }
                        ],
                    },
                    {
                        "judgment_key": "semantic-model::selected_nested_row",
                        "qualified_declaration": (
                            "Fixture.PaperInterface.selected_nested_row"
                        ),
                        "expanded_lean_surface": {
                            "binder_domains": [
                                {
                                    "expanded_type": "Nat",
                                    "alpha_normalized_type": "Nat",
                                },
                                {
                                    "expanded_type": "Fixture.NestedModel n",
                                    "alpha_normalized_type": "Fixture.NestedModel _f0",
                                },
                            ],
                            "record_roots": ["Fixture.NestedModel"],
                        },
                        "record_input_bindings": [
                            {
                                "binder_names": ["unrelated_name"],
                                "record_roots": ["Fixture.NestedModel"],
                                "source_type_canonical": "Fixture.NestedModel n",
                                "expanded_type": "Fixture.NestedModel n",
                                "alpha_normalized_type": "Fixture.NestedModel _f0",
                                "fully_qualified_expanded_type_canonical": (
                                    "Fixture.NestedModel n"
                                ),
                            }
                        ],
                    },
                ],
            }
            (audit / "source_record_audit.json").write_text(
                json.dumps(raw_audit), encoding="utf-8"
            )
            contract = {
                "model_field_mappings": [
                    {"source_record_item_key": "Fixture.RootModel.nested"}
                ],
                "target_result_mappings": [
                    {
                        "target_declaration": "Fixture.PaperInterface.model_row",
                        "source_record_item_key": "semantic-model::model_row",
                    }
                ],
                "assumption_mappings": [],
                "semantic_item_mappings": [
                    {
                        "qualified_declaration": "Fixture.PaperInterface.model_row",
                        "source_record_item_key": "semantic-model::model_row",
                    },
                    {
                        "qualified_declaration": (
                            "Fixture.PaperInterface.selected_nested_row"
                        ),
                        "source_record_item_key": "semantic-model::selected_nested_row",
                    },
                ],
            }
            (audit / "corrected_model_semantic_contract.json").write_text(
                json.dumps(contract), encoding="utf-8"
            )
            payload: dict[str, object] = {
                "formalization_scope": {
                    "model_spec_declaration": "Fixture.RootModel",
                    "target_result_declarations": [
                        "Fixture.PaperInterface.model_row"
                    ],
                    "semantic_contract": {
                        "path": "audit/corrected_model_semantic_contract.json"
                    },
                },
                "review_surface": {
                    "include_names": [
                        "model_row",
                        "selected_nested_row",
                        "out_of_mode_row",
                        "ambiguous_row",
                        "foreign_row",
                    ]
                },
            }
            declaration_index = audit_repository.paper_lean_declaration_index(folder)
            model_row = audit_repository.resolve_declaration_name(
                declaration_index, "Fixture.PaperInterface.model_row"
            )[0]
            selected_nested_row = audit_repository.resolve_declaration_name(
                declaration_index, "Fixture.PaperInterface.selected_nested_row"
            )[0]
            out_of_mode_row = audit_repository.resolve_declaration_name(
                declaration_index, "Fixture.PaperInterface.out_of_mode_row"
            )[0]
            ambiguous_row = audit_repository.resolve_declaration_name(
                declaration_index, "Fixture.PaperInterface.ambiguous_row"
            )[0]
            foreign_row = audit_repository.resolve_declaration_name(
                declaration_index, "Fixture.PaperInterface.foreign_row"
            )[0]
            unreviewed_row = audit_repository.resolve_declaration_name(
                declaration_index, "Fixture.PaperInterface.unreviewed_row"
            )[0]

            complete_transitive_fields = {
                str(direct_field["judgment_key"]): direct_field,
                str(nested_field["judgment_key"]): nested_field,
            }
            with mock.patch.object(
                audit_repository,
                "current_corrected_model_contract_field_items",
                return_value=complete_transitive_fields,
            ):
                bridge = audit_repository.current_corrected_model_premise_bridge(
                    folder, payload
                )

            self.assertIsNotNone(bridge)
            self.assertTrue(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "arbitrary_name : RootModel n",
                    model_row,
                    bridge,
                    declaration_index,
                )
            )
            self.assertTrue(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "anonymous : Fixture.RootModel n",
                    model_row,
                    bridge,
                    declaration_index,
                )
            )
            self.assertTrue(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "unrelated_name : Fixture.NestedModel n",
                    selected_nested_row,
                    bridge,
                    declaration_index,
                )
            )
            self.assertFalse(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "arbitrary_name : RootModel (n + 1)",
                    model_row,
                    bridge,
                    declaration_index,
                )
            )
            self.assertFalse(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "out_of_mode_name : RootModel n",
                    out_of_mode_row,
                    bridge,
                    declaration_index,
                )
            )
            self.assertFalse(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "candidate : NestedModel n",
                    ambiguous_row,
                    bridge,
                    declaration_index,
                )
            )
            self.assertFalse(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "foreign : ForeignModel",
                    foreign_row,
                    bridge,
                    declaration_index,
                )
            )
            self.assertFalse(
                audit_repository.premise_is_current_corrected_model_contract_input(
                    "unreviewed : Fixture.NestedModel",
                    unreviewed_row,
                    bridge,
                    declaration_index,
                )
            )

            with mock.patch.object(
                audit_repository,
                "current_corrected_model_contract_field_items",
                return_value=None,
            ):
                self.assertIsNone(
                    audit_repository.current_corrected_model_premise_bridge(
                        folder, payload
                    )
                )

            with mock.patch.object(
                audit_repository,
                "current_corrected_model_contract_field_items",
                return_value={str(direct_field["judgment_key"]): direct_field},
            ):
                self.assertIsNone(
                    audit_repository.current_corrected_model_premise_bridge(
                        folder, payload
                    )
                )

    def test_current_corrected_scope_replaces_only_legacy_agent_source_audit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            docs = folder / "docs"
            docs.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            (docs / "AGENT_SOURCE_AUDIT.md").write_text(
                "# Historical notice\n", encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## DAG Audit\nDependencyDAG.tex DependencyDAG.pdf\n"
                "## Validation Checks\npython3 scripts/audit_repository.py --paper FixturePaper\n",
                encoding="utf-8",
            )

            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
                mock.patch.object(audit_repository, "paper_local_status", return_value="formalized"),
                mock.patch.object(
                    audit_repository,
                    "current_author_approved_corrected_scope",
                    return_value=True,
                ),
            ):
                current_findings = audit_repository.check_dag_and_validation_report_closeout(
                    include_active=True,
                    paper_filter="FixturePaper",
                )

            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
                mock.patch.object(audit_repository, "paper_local_status", return_value="formalized"),
                mock.patch.object(
                    audit_repository,
                    "current_author_approved_corrected_scope",
                    return_value=False,
                ),
            ):
                legacy_findings = audit_repository.check_dag_and_validation_report_closeout(
                    include_active=True,
                    paper_filter="FixturePaper",
                )

        self.assertFalse(any("AGENT_SOURCE_AUDIT" in item.message for item in current_findings))
        self.assertTrue(any("AGENT_SOURCE_AUDIT" in item.message for item in legacy_findings))


class NamedTheorySemanticSurfaceTests(unittest.TestCase):
    def test_current_v11_uses_exact_paper_status_not_stale_generated_entry(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "namespace Example\n"
                "def spec : Prop := True\n"
                "theorem proof : spec := by trivial\n"
                "end Example\n",
                encoding="utf-8",
            )
            declarations = typed_fixture_declaration_index(
                folder,
                {"Example.spec": "def", "Example.proof": "theorem"},
            )
            exact_status = {
                "status": "formalized",
                "review_surface": {
                    "include_names": ["spec"],
                    "proposition_spec_proofs": {"spec": "proof"},
                    # Historical status vocabulary is not a v11 role map.
                    "source_definition_names": [
                        "AppliedModelingLib.Example.ReusableModel"
                    ],
                    "require_v11_raw_source_spec_screening": True,
                },
            }
            statement_map = {
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "Example.spec",
                            "evidence_declaration": "Example.proof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        }
                    }
                }
            }
            context = mock.Mock()
            context.issued_by_builder = True
            context.selected_v11_closeout = True
            context.current_v11_closeout = True
            context.v11_direct_semantic_review_current = True
            context.evidence_context = object()
            context.paper_declaration_index.return_value = declarations
            context.exact_json_payload.side_effect = lambda path: (
                exact_status if path.name == "status.json" else statement_map
            )

            with mock.patch.object(
                audit_repository,
                "graph_authority_source_spec_correspondence_errors",
                side_effect=AssertionError(
                    "current v11 hidden-premise selection must not fall back to raw graph authority"
                ),
            ):
                surface, error = (
                    audit_repository.current_named_theory_semantic_review_surface(
                        folder,
                        {"status": "formalized"},
                        declarations,
                        run_context=context,
                    )
                )

        self.assertEqual(error, "")
        self.assertIsNotNone(surface)
        assert surface is not None
        self.assertEqual(set(surface.rows), {"Example.spec"})

    def write_receipt_fixture(
        self,
        folder: Path,
        *,
        coverage_mode: str,
        semantic_declarations: list[str],
        scope_targets: list[str] | None = None,
    ) -> tuple[
        dict[str, object],
        dict[str, list[audit_repository.LeanDeclaration]],
        dict[str, audit_repository.LeanDeclaration],
        dict[str, object],
    ]:
        audit = folder / "audit"
        audit.mkdir(parents=True)
        interface = folder / "PaperInterface.lean"
        interface.write_text(
            "namespace Fixture\n"
            "namespace PaperInterface\n"
            "theorem selected_result (h : True) : True := h\n"
            "theorem governing_target (h : True) : True := h\n"
            "theorem supplemental_surface (h : True) : True := h\n"
            "end PaperInterface\n"
            "end Fixture\n",
            encoding="utf-8",
        )
        declaration_blocks = review_surface_structure.review_declaration_blocks(
            interface.read_text(encoding="utf-8")
        )
        declaration_index = audit_repository.paper_lean_declaration_index(folder)
        declarations = {
            qualified: declaration_index[qualified][0]
            for qualified in (
                "Fixture.PaperInterface.selected_result",
                "Fixture.PaperInterface.governing_target",
                "Fixture.PaperInterface.supplemental_surface",
            )
        }
        source_sha = hashlib.sha256(interface.read_bytes()).hexdigest()
        configured_rows: list[dict[str, object]] = []
        semantic_items: list[dict[str, object]] = []
        for qualified in semantic_declarations:
            short_name = qualified.rsplit(".", 1)[-1]
            _line, _kind, declaration_source = declaration_blocks[short_name]
            declaration_sha = hashlib.sha256(
                declaration_source.encode("utf-8")
            ).hexdigest()
            signature_sha = hashlib.sha256(
                (qualified + " signature").encode("utf-8")
            ).hexdigest()
            configured_rows.append(
                {
                    "qualified_declaration": qualified,
                    "source_file": str(interface.resolve()),
                    "source_sha256": source_sha,
                    "elaborated_signature_sha256": signature_sha,
                    "lean_source_declaration": declaration_source,
                }
            )
            semantic_items.append(
                {
                    "judgment_key": "semantic-model::" + qualified,
                    "qualified_declaration": qualified,
                    "reviewed_declaration_identity": {
                        "qualified_declaration": qualified,
                        "declaration_sha256": declaration_sha,
                    },
                    "reviewed_elaborated_signature_identities": [
                        {
                            "qualified_declaration": qualified,
                            "elaborated_signature_sha256": signature_sha,
                        }
                    ],
                }
            )
        receipt: dict[str, object] = {
            "prompt_version": audit_repository.REQUIRED_SOURCE_RECORD_PROMPT_VERSION,
            "source_coverage_mode": coverage_mode,
            "configured_review_rows": configured_rows,
            "expected_semantic_model_judgment_keys": [
                item["judgment_key"] for item in semantic_items
            ],
            "semantic_model_items": semantic_items,
        }
        source_record_integrity.stamp_source_record_audit_receipts(receipt)
        (audit / "source_record_audit.json").write_text(
            json.dumps(receipt), encoding="utf-8"
        )
        status: dict[str, object] = {
            "review_surface": {"semantic_model_review": {"schema": 2}}
        }
        if scope_targets is not None:
            status["formalization_scope"] = {
                "target_result_declarations": scope_targets
            }
        return status, declaration_index, declarations, receipt

    def write_grouped_receipt_fixture(
        self, folder: Path
    ) -> tuple[
        dict[str, object],
        dict[str, list[audit_repository.LeanDeclaration]],
        dict[str, audit_repository.LeanDeclaration],
        dict[str, object],
    ]:
        """Write a direct/transparent-Spec receipt with arbitrary row labels."""

        audit = folder / "audit"
        audit.mkdir(parents=True)
        interface = folder / "PaperInterface.lean"
        direct_short_name = "opaque_alpha_17"
        spec_short_name = "opaque_beta_41"
        interface.write_text(
            "namespace Fixture\n"
            "namespace PaperInterface\n"
            f"theorem {direct_short_name} : True := by trivial\n"
            f"abbrev {spec_short_name} : Prop := True\n"
            "theorem unreviewed_surface (h : True) : True := h\n"
            "end PaperInterface\n"
            "end Fixture\n",
            encoding="utf-8",
        )
        direct = f"Fixture.PaperInterface.{direct_short_name}"
        spec = f"Fixture.PaperInterface.{spec_short_name}"
        unreviewed = "Fixture.PaperInterface.unreviewed_surface"
        declaration_blocks = review_surface_structure.review_declaration_blocks(
            interface.read_text(encoding="utf-8")
        )
        declaration_index = audit_repository.paper_lean_declaration_index(folder)
        declarations = {
            qualified: declaration_index[qualified][0]
            for qualified in (direct, spec, unreviewed)
        }
        direct_source = declaration_blocks[direct_short_name][2]
        spec_source = declaration_blocks[spec_short_name][2]
        direct_declaration_sha = hashlib.sha256(
            direct_source.encode("utf-8")
        ).hexdigest()
        spec_declaration_sha = hashlib.sha256(spec_source.encode("utf-8")).hexdigest()
        direct_signature_sha = hashlib.sha256(
            (direct + " signature").encode("utf-8")
        ).hexdigest()
        spec_signature_sha = hashlib.sha256(
            (spec + " signature").encode("utf-8")
        ).hexdigest()
        source_sha = hashlib.sha256(interface.read_bytes()).hexdigest()
        source_identity = {
            # The storage key is deliberately not part of the route check.
            "source_key": "ordinary_storage_key",
            "source_kind": "definition",
            "source_location": "source.tex:11-15",
            "source_map_item_sha256": hashlib.sha256(b"source item").hexdigest(),
            "source_semantic_sha256": hashlib.sha256(b"source semantics").hexdigest(),
            "semantic_contract": {
                "evidence_declaration": direct,
                "spec_declaration": spec,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        surface = {"binder_domains": [], "alpha_normalized_result": "True"}
        direct_identity = {
            "qualified_declaration": direct,
            "declaration_sha256": direct_declaration_sha,
        }
        spec_identity = {
            "qualified_declaration": spec,
            "declaration_sha256": spec_declaration_sha,
        }
        direct_signature_identity = {
            "qualified_declaration": direct,
            "elaborated_signature_sha256": direct_signature_sha,
        }
        association = {
            "schema": 2,
            "role": "direct_evidence",
            "paired_qualified_declaration": spec,
            "review_scope": "individual_row_only",
            "structural_pairing": "not_asserted_by_source_association",
            "reviewed_declaration_identity": direct_identity,
            "reviewed_elaborated_signature_identity": direct_signature_identity,
            "semantic_association_sha256": hashlib.sha256(
                b"generated direct-spec association"
            ).hexdigest(),
            "source_item_identities": [source_identity],
        }
        semantic_item = {
            # Row labels are intentionally arbitrary and are not route keys.
            "row": "presentation_label_without_semantic_role",
            "judgment_key": "semantic-model::opaque-group",
            "qualified_declaration": direct,
            "lean_source_declaration": direct_source,
            "reviewed_declaration_identity": direct_identity,
            "reviewed_elaborated_signature_identities": [
                direct_signature_identity,
            ],
            "semantic_surface_origin": {
                "kind": "transparent_spec_body",
                "qualified_declaration": spec,
            },
            "semantic_contract_group": {
                "schema": 1,
                "structural_alpha_normalized_equal": True,
                "source_item_identities": [source_identity],
                "member_rows": [
                    {
                        "role": "direct_evidence",
                        "row": "arbitrary_member_label_one",
                        "qualified_declaration": direct,
                        "reviewed_declaration_identity": direct_identity,
                    },
                    {
                        "role": "transparent_spec",
                        "row": "arbitrary_member_label_two",
                        "qualified_declaration": spec,
                        "reviewed_declaration_identity": spec_identity,
                    },
                ],
                "direct_evidence_type": {
                    "qualified_declaration": direct,
                    "structural_alpha_normalized_surface": surface,
                },
                "surface_root": {
                    "kind": "transparent_spec_body",
                    "qualified_declaration": spec,
                    "structural_alpha_normalized_surface": surface,
                },
            },
            "semantic_contract_source_association": association,
        }
        receipt: dict[str, object] = {
            "prompt_version": audit_repository.REQUIRED_SOURCE_RECORD_PROMPT_VERSION,
            "source_coverage_mode": audit_repository.NAMED_THEORETICAL_STATEMENTS,
            "configured_review_rows": [
                {
                    "row": "unrelated_configured_label_a",
                    "qualified_declaration": direct,
                    "source_file": str(interface.resolve()),
                    "source_sha256": source_sha,
                    "elaborated_signature_sha256": direct_signature_sha,
                    "lean_source_declaration": direct_source,
                },
                {
                    "row": "unrelated_configured_label_b",
                    "qualified_declaration": spec,
                    "source_file": str(interface.resolve()),
                    "source_sha256": source_sha,
                    "elaborated_signature_sha256": spec_signature_sha,
                    "lean_source_declaration": spec_source,
                },
            ],
            "expected_semantic_model_judgment_keys": [
                "semantic-model::opaque-group"
            ],
            "semantic_model_items": [semantic_item],
        }
        source_record_integrity.stamp_source_record_audit_receipts(receipt)
        (audit / "source_record_audit.json").write_text(
            json.dumps(receipt), encoding="utf-8"
        )
        status: dict[str, object] = {
            "review_surface": {"semantic_model_review": {"schema": 2}}
        }
        return status, declaration_index, declarations, receipt

    @staticmethod
    def persist_grouped_receipt(folder: Path, receipt: dict[str, object]) -> None:
        source_record_integrity.stamp_source_record_audit_receipts(receipt)
        (folder / "audit" / "source_record_audit.json").write_text(
            json.dumps(receipt), encoding="utf-8"
        )

    def test_normal_named_theory_selects_only_receipt_pinned_rows_and_scope_targets(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            selected = "Fixture.PaperInterface.selected_result"
            target = "Fixture.PaperInterface.governing_target"
            supplemental = "Fixture.PaperInterface.supplemental_surface"
            status, declaration_index, declarations, _receipt = self.write_receipt_fixture(
                folder,
                coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                semantic_declarations=[selected, target],
                scope_targets=[target],
            )

            surface, error = audit_repository.current_named_theory_semantic_review_surface(
                folder, status, declaration_index
            )
            selected_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[selected], surface
                )
            )
            target_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[target], surface
                )
            )
            supplemental_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[supplemental], surface
                )
            )

        self.assertEqual(error, "")
        self.assertIsNotNone(surface)
        assert surface is not None
        self.assertEqual(set(surface.rows), {selected, target})
        self.assertTrue(selected_matches)
        self.assertTrue(target_matches)
        self.assertFalse(supplemental_matches)

    def test_direct_transparent_spec_group_uses_exact_generated_members(self) -> None:
        with self.subTest("accepts group despite arbitrary row and storage labels"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                status, declaration_index, declarations, receipt = (
                    self.write_grouped_receipt_fixture(folder)
                )
                semantic_items = receipt["semantic_model_items"]
                assert isinstance(semantic_items, list)
                assert isinstance(semantic_items[0], dict)
                grouped_item = semantic_items[0]
                group = grouped_item["semantic_contract_group"]
                association = grouped_item["semantic_contract_source_association"]
                assert isinstance(group, dict)
                assert isinstance(association, dict)
                group["member_rows"][0]["row"] = "renamed_presentation_only"
                association["source_item_identities"][0]["source_key"] = (
                    "renamed_storage_key"
                )
                group["source_item_identities"][0]["source_key"] = "renamed_storage_key"
                self.persist_grouped_receipt(folder, receipt)

                surface, error = (
                    audit_repository.current_named_theory_semantic_review_surface(
                        folder, status, declaration_index
                    )
                )
                direct = "Fixture.PaperInterface.opaque_alpha_17"
                spec = "Fixture.PaperInterface.opaque_beta_41"
                direct_matches = (
                    audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                        declarations[direct], surface
                    )
                )
                spec_matches = (
                    audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                        declarations[spec], surface
                    )
                )

            self.assertEqual(error, "")
            self.assertIsNotNone(surface)
            assert surface is not None
            self.assertEqual(set(surface.rows), {direct})
            self.assertTrue(direct_matches)
            self.assertFalse(spec_matches)

        with self.subTest("rejects duplicate direct member"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                status, declaration_index, _declarations, receipt = (
                    self.write_grouped_receipt_fixture(folder)
                )
                semantic_items = receipt["semantic_model_items"]
                assert isinstance(semantic_items, list)
                assert isinstance(semantic_items[0], dict)
                group = semantic_items[0]["semantic_contract_group"]
                assert isinstance(group, dict)
                members = group["member_rows"]
                assert isinstance(members, list)
                members.append(dict(members[0]))
                self.persist_grouped_receipt(folder, receipt)

                surface, error = (
                    audit_repository.current_named_theory_semantic_review_surface(
                        folder, status, declaration_index
                    )
                )

            self.assertIsNone(surface)
            self.assertIn("ambiguous or incomplete exact identity", error)

        with self.subTest("rejects association signature tampering"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                status, declaration_index, _declarations, receipt = (
                    self.write_grouped_receipt_fixture(folder)
                )
                semantic_items = receipt["semantic_model_items"]
                assert isinstance(semantic_items, list)
                assert isinstance(semantic_items[0], dict)
                association = semantic_items[0][
                    "semantic_contract_source_association"
                ]
                assert isinstance(association, dict)
                association["reviewed_elaborated_signature_identity"] = {
                    "qualified_declaration": "Fixture.PaperInterface.opaque_alpha_17",
                    "elaborated_signature_sha256": "0" * 64,
                }
                self.persist_grouped_receipt(folder, receipt)

                surface, error = (
                    audit_repository.current_named_theory_semantic_review_surface(
                        folder, status, declaration_index
                    )
                )

            self.assertIsNone(surface)
            self.assertIn("ambiguous or incomplete exact identity", error)

        with self.subTest("rejects association source-pin tampering"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                status, declaration_index, _declarations, receipt = (
                    self.write_grouped_receipt_fixture(folder)
                )
                semantic_items = receipt["semantic_model_items"]
                assert isinstance(semantic_items, list)
                assert isinstance(semantic_items[0], dict)
                association = semantic_items[0][
                    "semantic_contract_source_association"
                ]
                assert isinstance(association, dict)
                source_pins = association["source_item_identities"]
                assert isinstance(source_pins, list)
                association["source_item_identities"] = [
                    {
                        **source_pins[0],
                        "source_semantic_sha256": "0" * 64,
                    }
                ]
                self.persist_grouped_receipt(folder, receipt)

                surface, error = (
                    audit_repository.current_named_theory_semantic_review_surface(
                        folder, status, declaration_index
                    )
                )

            self.assertIsNone(surface)
            self.assertIn("ambiguous or incomplete exact identity", error)

    def test_external_semantic_support_without_signature_identity_does_not_block_projection(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            selected = "Fixture.PaperInterface.selected_result"
            status, _declaration_index, declarations, receipt = self.write_receipt_fixture(
                folder,
                coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                semantic_declarations=[selected],
            )
            assumptions = folder / "Assumptions.lean"
            assumptions.write_text(
                "namespace Fixture\n"
                "theorem source_condition (h : True) : True := h\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            assumption_blocks = review_surface_structure.review_declaration_blocks(
                assumptions.read_text(encoding="utf-8")
            )
            _line, _kind, assumption_source = assumption_blocks["source_condition"]
            support_qualified = "Fixture.source_condition"
            support_sha = hashlib.sha256(assumptions.read_bytes()).hexdigest()
            support_declaration_sha = hashlib.sha256(
                assumption_source.encode("utf-8")
            ).hexdigest()
            configured_rows = receipt["configured_review_rows"]
            semantic_items = receipt["semantic_model_items"]
            expected_keys = receipt["expected_semantic_model_judgment_keys"]
            assert isinstance(configured_rows, list)
            assert isinstance(semantic_items, list)
            assert isinstance(expected_keys, list)
            configured_rows.append(
                {
                    "qualified_declaration": support_qualified,
                    "source_file": str(assumptions.resolve()),
                    "source_sha256": support_sha,
                    "elaborated_signature_sha256": hashlib.sha256(
                        b"external support signature"
                    ).hexdigest(),
                    "lean_source_declaration": assumption_source,
                }
            )
            support_key = "semantic-model::external-support"
            semantic_items.append(
                {
                    "judgment_key": support_key,
                    "qualified_declaration": support_qualified,
                    "reviewed_declaration_identity": {
                        "qualified_declaration": support_qualified,
                        "declaration_sha256": support_declaration_sha,
                    },
                    # External semantic support is aggregate-audit material;
                    # it intentionally has no PaperInterface signature route.
                }
            )
            expected_keys.append(support_key)
            source_record_integrity.stamp_source_record_audit_receipts(receipt)
            (folder / "audit" / "source_record_audit.json").write_text(
                json.dumps(receipt), encoding="utf-8"
            )
            declaration_index = audit_repository.paper_lean_declaration_index(folder)

            surface, error = audit_repository.current_named_theory_semantic_review_surface(
                folder, status, declaration_index
            )
            selected_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[selected], surface
                )
            )

        self.assertEqual(error, "")
        self.assertIsNotNone(surface)
        assert surface is not None
        self.assertEqual(set(surface.rows), {selected})
        self.assertTrue(selected_matches)

    def test_deep_mode_retains_every_hidden_premise_row(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            selected = "Fixture.PaperInterface.selected_result"
            supplemental = "Fixture.PaperInterface.supplemental_surface"
            status, declaration_index, declarations, _receipt = self.write_receipt_fixture(
                folder,
                coverage_mode=audit_repository.DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
                semantic_declarations=[selected],
            )

            surface, error = audit_repository.current_named_theory_semantic_review_surface(
                folder, status, declaration_index
            )
            selected_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[selected], surface
                )
            )
            supplemental_matches = (
                audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                    declarations[supplemental], surface
                )
            )

        self.assertEqual(error, "")
        self.assertIsNone(surface)
        self.assertTrue(selected_matches)
        self.assertTrue(supplemental_matches)

    def test_stale_or_malformed_receipt_fails_closed_to_full_surface(self) -> None:
        with self.subTest("source bytes changed after receipt"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                selected = "Fixture.PaperInterface.selected_result"
                supplemental = "Fixture.PaperInterface.supplemental_surface"
                status, declaration_index, declarations, _receipt = self.write_receipt_fixture(
                    folder,
                    coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                    semantic_declarations=[selected],
                )
                interface = folder / "PaperInterface.lean"
                interface.write_text(
                    interface.read_text(encoding="utf-8") + "\n-- later edit\n",
                    encoding="utf-8",
                )

                surface, error = audit_repository.current_named_theory_semantic_review_surface(
                    folder, status, declaration_index
                )

                self.assertIsNone(surface)
                self.assertIn("source bytes are stale", error)
                self.assertTrue(
                    audit_repository.declaration_is_on_current_named_theory_semantic_review_surface(
                        declarations[supplemental], surface
                    )
                )

        with self.subTest("raw receipt identity was modified"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                selected = "Fixture.PaperInterface.selected_result"
                status, declaration_index, _declarations, receipt = self.write_receipt_fixture(
                    folder,
                    coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                    semantic_declarations=[selected],
                )
                semantic_items = receipt["semantic_model_items"]
                assert isinstance(semantic_items, list)
                assert isinstance(semantic_items[0], dict)
                semantic_items[0]["reviewed_declaration_identity"] = {
                    "qualified_declaration": "Fixture.PaperInterface.unrelated_result",
                    "declaration_sha256": "0" * 64,
                }
                source_record_integrity.stamp_source_record_audit_receipts(receipt)
                (folder / "audit" / "source_record_audit.json").write_text(
                    json.dumps(receipt), encoding="utf-8"
                )

                surface, error = audit_repository.current_named_theory_semantic_review_surface(
                    folder, status, declaration_index
                )

                self.assertIsNone(surface)
                self.assertIn("ambiguous or incomplete exact identity", error)

        with self.subTest("raw receipt integrity was modified"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                selected = "Fixture.PaperInterface.selected_result"
                status, declaration_index, _declarations, receipt = self.write_receipt_fixture(
                    folder,
                    coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                    semantic_declarations=[selected],
                )
                receipt["source_coverage_mode"] = "tampered_mode"
                (folder / "audit" / "source_record_audit.json").write_text(
                    json.dumps(receipt), encoding="utf-8"
                )

                surface, error = audit_repository.current_named_theory_semantic_review_surface(
                    folder, status, declaration_index
                )

                self.assertIsNone(surface)
                self.assertIn("source-record receipt is not current", error)

        with self.subTest("elaborated signature pin is missing"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                selected = "Fixture.PaperInterface.selected_result"
                status, declaration_index, _declarations, receipt = self.write_receipt_fixture(
                    folder,
                    coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                    semantic_declarations=[selected],
                )
                configured_rows = receipt["configured_review_rows"]
                assert isinstance(configured_rows, list)
                assert isinstance(configured_rows[0], dict)
                configured_rows[0]["elaborated_signature_sha256"] = ""
                source_record_integrity.stamp_source_record_audit_receipts(receipt)
                (folder / "audit" / "source_record_audit.json").write_text(
                    json.dumps(receipt), encoding="utf-8"
                )

                surface, error = audit_repository.current_named_theory_semantic_review_surface(
                    folder, status, declaration_index
                )

                self.assertIsNone(surface)
                self.assertIn("complete FQN/source/signature receipt route", error)

        with self.subTest("semantic signature identity mismatches configured route"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                selected = "Fixture.PaperInterface.selected_result"
                status, declaration_index, _declarations, receipt = self.write_receipt_fixture(
                    folder,
                    coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                    semantic_declarations=[selected],
                )
                semantic_items = receipt["semantic_model_items"]
                assert isinstance(semantic_items, list)
                assert isinstance(semantic_items[0], dict)
                signature_identities = semantic_items[0][
                    "reviewed_elaborated_signature_identities"
                ]
                assert isinstance(signature_identities, list)
                assert isinstance(signature_identities[0], dict)
                signature_identities[0]["elaborated_signature_sha256"] = "a" * 64
                source_record_integrity.stamp_source_record_audit_receipts(receipt)
                (folder / "audit" / "source_record_audit.json").write_text(
                    json.dumps(receipt), encoding="utf-8"
                )

                surface, error = audit_repository.current_named_theory_semantic_review_surface(
                    folder, status, declaration_index
                )

                self.assertIsNone(surface)
                self.assertIn("does not exactly match its configured FQN route", error)

        with self.subTest("governing target cannot be omitted"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                selected = "Fixture.PaperInterface.selected_result"
                target = "Fixture.PaperInterface.governing_target"
                status, declaration_index, _declarations, _receipt = self.write_receipt_fixture(
                    folder,
                    coverage_mode=audit_repository.NAMED_THEORETICAL_STATEMENTS,
                    semantic_declarations=[selected],
                    scope_targets=[target],
                )

                surface, error = audit_repository.current_named_theory_semantic_review_surface(
                    folder, status, declaration_index
                )

                self.assertIsNone(surface)
                self.assertIn("governing formalization-scope target", error)

        with self.subTest("missing receipt"):
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "FixturePaper"
                folder.mkdir()
                interface = folder / "PaperInterface.lean"
                interface.write_text(
                    "namespace Fixture\nnamespace PaperInterface\n"
                    "theorem result : True := by trivial\n"
                    "end PaperInterface\nend Fixture\n",
                    encoding="utf-8",
                )
                declaration_index = audit_repository.paper_lean_declaration_index(folder)
                status = {"review_surface": {"semantic_model_review": {"schema": 2}}}

                surface, error = audit_repository.current_named_theory_semantic_review_surface(
                    folder, status, declaration_index
                )

                self.assertIsNone(surface)
                self.assertIn("no saved source-record receipt", error)


class ReviewDashboardReadOnlyPrecheckTests(unittest.TestCase):
    def review_item(self) -> review_dashboard.ReviewItem:
        return review_dashboard.ReviewItem(
            name="paper_row",
            kind="theorem",
            lean_statement="theorem paper_row : True",
            paper_statement="paper row",
            agent_statement="paper row",
        )

    def source_hashes(self, marker: str = "current") -> dict[str, str]:
        return {
            "review_source_file": "PaperInterface.lean",
            "interface_sha256": marker,
            "report_sha256": "report",
            "tex_sha256": "tex",
            "text_sha256": "text",
            "pdf_sha256": "pdf",
            "paper_statement_map_sha256": "map",
            "review_surface_static_sha256": "surface",
            "review_surface_display_sha256": "display",
            "review_surface_rebind_sha256": "rebind",
            "lean_source_closure_sha256": "lean-closure",
        }

    def test_read_only_row_loading_skips_rendered_statement_images(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            item = self.review_item()
            with (
                mock.patch.object(
                    review_dashboard,
                    "load_interactive_cached_review_rows",
                    return_value=[item],
                ) as load_cache,
                mock.patch.object(
                    review_dashboard,
                    "review_source_file",
                    return_value=folder / "PaperInterface.lean",
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_relative_file",
                    return_value=folder / "missing-report.md",
                ),
                mock.patch.object(
                    review_dashboard,
                    "parse_interface_items",
                    return_value=[item],
                ),
                mock.patch.object(
                    review_dashboard,
                    "attach_rendered_statement_images",
                ) as attach_images,
                mock.patch.object(
                    review_dashboard,
                    "_cache_source_hashes",
                    return_value=self.source_hashes(),
                ),
            ):
                rows = review_dashboard.review_items_for_paper(
                    folder,
                    use_cache=True,
                    render_images=False,
                )

        self.assertEqual(rows, [item])
        load_cache.assert_called_once()
        attach_images.assert_not_called()

    def test_strict_row_loading_uses_one_fresh_batched_extraction(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            item = self.review_item()
            context = {"PaperInterface.lean": {"schema": 1, "import_module": "Example.PaperInterface"}}
            source_hashes = self.source_hashes()
            with (
                mock.patch.object(
                    review_dashboard,
                    "current_review_signature_contexts",
                    side_effect=[context, context],
                ) as current_contexts,
                mock.patch.object(
                    review_dashboard,
                    "load_cached_review_rows",
                    return_value=None,
                ) as load_cache,
                mock.patch.object(
                    review_dashboard,
                    "review_source_file",
                    return_value=folder / "PaperInterface.lean",
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_relative_file",
                    return_value=folder / "missing-report.md",
                ),
                mock.patch.object(
                    review_dashboard,
                    "parse_interface_items",
                    return_value=[item],
                ) as parse_items,
                mock.patch.object(
                    review_dashboard,
                    "write_cached_review_rows",
                ) as write_cache,
                mock.patch.object(
                    review_dashboard,
                    "_cache_source_hashes",
                    return_value=source_hashes,
                ) as cache_hashes,
            ):
                rows = review_dashboard.review_items_for_paper(
                    folder,
                    use_cache=True,
                    render_images=False,
                    require_current_signatures=True,
                )

        self.assertEqual(rows, [item])
        self.assertEqual(current_contexts.call_count, 2)
        self.assertEqual(cache_hashes.call_count, 2)
        load_cache.assert_not_called()
        parse_items.assert_called_once()
        self.assertFalse(parse_items.call_args.kwargs["render_lean_previews"])
        write_cache.assert_called_once_with(
            folder,
            [item],
            signature_contexts=context,
            source_hashes=source_hashes,
        )

    def test_strict_row_loading_refuses_context_drift_during_extraction(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            item = self.review_item()
            before = {
                "PaperInterface.lean": {
                    "schema": 1,
                    "import_module": "Example.PaperInterface",
                    "workspace_fingerprint": "before",
                }
            }
            after = {
                "PaperInterface.lean": {
                    "schema": 1,
                    "import_module": "Example.PaperInterface",
                    "workspace_fingerprint": "after",
                }
            }
            with (
                mock.patch.object(
                    review_dashboard,
                    "current_review_signature_contexts",
                    side_effect=[before, after],
                ),
                mock.patch.object(
                    review_dashboard,
                    "load_cached_review_rows",
                    return_value=None,
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_source_file",
                    return_value=folder / "PaperInterface.lean",
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_relative_file",
                    return_value=folder / "missing-report.md",
                ),
                mock.patch.object(
                    review_dashboard,
                    "parse_interface_items",
                    return_value=[item],
                ),
                mock.patch.object(
                    review_dashboard,
                    "write_cached_review_rows",
                ) as write_cache,
                mock.patch.object(
                    review_dashboard,
                    "_cache_source_hashes",
                    return_value=self.source_hashes(),
                ),
            ):
                with self.assertRaisesRegex(RuntimeError, "context changed"):
                    review_dashboard.review_items_for_paper(
                        folder,
                        use_cache=True,
                        render_images=False,
                        require_current_signatures=True,
                    )

        write_cache.assert_not_called()

    def test_strict_cached_row_loading_refuses_source_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            item = self.review_item()
            context = {
                "PaperInterface.lean": {
                    "schema": 1,
                    "import_module": "Example.PaperInterface",
                }
            }
            with (
                mock.patch.object(
                    review_dashboard,
                    "current_review_signature_contexts",
                    return_value=context,
                ),
                mock.patch.object(
                    review_dashboard,
                    "load_cached_review_rows",
                    return_value=[item],
                ) as load_cache,
                mock.patch.object(
                    review_dashboard,
                    "review_source_file",
                    return_value=folder / "PaperInterface.lean",
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_relative_file",
                    return_value=folder / "missing-report.md",
                ),
                mock.patch.object(
                    review_dashboard,
                    "parse_interface_items",
                    return_value=[item],
                ),
                mock.patch.object(
                    review_dashboard,
                    "_cache_source_hashes",
                    side_effect=[
                        self.source_hashes("before"),
                        self.source_hashes("after"),
                    ],
                ) as cache_hashes,
                mock.patch.object(
                    review_dashboard,
                    "write_cached_review_rows",
                ) as write_cache,
            ):
                with self.assertRaisesRegex(RuntimeError, "sources changed"):
                    review_dashboard.review_items_for_paper(
                        folder,
                        use_cache=True,
                        render_images=False,
                        require_current_signatures=True,
                    )

        self.assertEqual(cache_hashes.call_count, 2)
        load_cache.assert_not_called()
        write_cache.assert_not_called()

    def test_precheck_status_paths_gather_without_rendered_images(self) -> None:
        with (
            mock.patch.object(
                review_dashboard,
                "gather_paper_data",
                return_value=[],
            ) as gather,
            mock.patch.object(
                review_dashboard,
                "merge_hidden_premise_audit_rows",
                return_value=[],
            ),
        ):
            review_dashboard.stale_review_summary("ExamplePaper", None, "main")

        gather.assert_called_once_with(
            "ExamplePaper",
            "main",
            render_images=False,
        )

    def test_assumption_precheck_uses_direct_strict_rows(self) -> None:
        with (
            mock.patch.object(
                review_dashboard,
                "fast_saved_source_record_assumption_precheck",
                return_value=None,
            ),
            mock.patch.object(
                review_dashboard,
                "direct_assumption_audit_rows",
                return_value=[],
            ) as direct_rows,
            mock.patch.object(
                review_dashboard,
                "merge_hidden_premise_audit_rows",
                return_value=[],
            ),
            mock.patch.object(
                review_dashboard,
                "gather_paper_data",
                side_effect=AssertionError(
                    "assumption precheck must not build dashboard data"
                ),
            ),
        ):
            self.assertFalse(
                review_dashboard.print_assumption_audit_status(
                    "ExamplePaper", "main"
                )
            )

        direct_rows.assert_called_once_with("ExamplePaper", "main")

    def test_statement_precheck_does_not_build_dashboard_data(self) -> None:
        with (
            mock.patch.object(
                review_dashboard,
                "direct_statement_audit_rows",
                return_value=[],
            ) as direct_rows,
            mock.patch.object(
                review_dashboard,
                "gather_paper_data",
                side_effect=AssertionError(
                    "statement precheck must not build dashboard data"
                ),
            ),
        ):
            self.assertFalse(
                review_dashboard.print_statement_audit_status(
                    "ExamplePaper", "main"
                )
            )

        direct_rows.assert_called_once_with("ExamplePaper", "main")

    def test_direct_statement_check_uses_shared_library_surface(self) -> None:
        folder = Path("/fixture/papers/ExamplePaper")
        authority = object()
        item = self.review_item()
        library_summary = {"needs_attention": False, "current_matches": 2}
        semantic_surface = review_dashboard._CurrentSemanticReviewSurface(
            human_claims=[],
            library_prerequisites=[],
            library_summary=library_summary,
        )
        statement_summary = {"needs_attention": False, "matches": 1}
        with (
            mock.patch.object(
                review_dashboard,
                "_direct_audit_inputs",
                return_value=iter([(folder, authority, [item], [item])]),
            ),
            mock.patch.object(
                review_dashboard,
                "current_semantic_review_surface",
                return_value=semantic_surface,
            ) as shared_surface,
            mock.patch.object(
                review_dashboard,
                "statement_translation_audit_summary",
                return_value=statement_summary,
            ) as statement_audit,
        ):
            rows = review_dashboard.direct_statement_audit_rows(
                "ExamplePaper", "main"
            )

        self.assertEqual(rows, [{"paper": "ExamplePaper", **statement_summary}])
        shared_surface.assert_called_once_with(
            folder,
            [item],
            [item],
            semantic_reuse_authority=authority,
        )
        statement_audit.assert_called_once_with(
            folder,
            [item],
            library_summary_override=library_summary,
        )

    def test_paper_coverage_precheck_does_not_build_dashboard_data(self) -> None:
        with (
            mock.patch.object(
                review_dashboard,
                "direct_paper_coverage_audit_rows",
                return_value=[],
            ) as direct_rows,
            mock.patch.object(
                review_dashboard,
                "gather_paper_data",
                side_effect=AssertionError(
                    "paper coverage precheck must not build dashboard data"
                ),
            ),
        ):
            self.assertFalse(
                review_dashboard.print_paper_coverage_audit_status(
                    "ExamplePaper", "main"
                )
            )

        direct_rows.assert_called_once_with("ExamplePaper", "main")

    def test_direct_paper_coverage_reuses_current_semantic_authority(self) -> None:
        folder = Path("/fixture/papers/ExamplePaper")
        authority = object()
        item = self.review_item()
        summary = {"needs_attention": False, "direct": 1}
        with (
            mock.patch.object(
                review_dashboard,
                "iter_paper_folders",
                return_value=[folder],
            ),
            mock.patch.object(
                review_dashboard,
                "current_dashboard_semantic_reuse_authority",
                return_value=authority,
            ) as load_authority,
            mock.patch.object(
                review_dashboard,
                "review_items_for_paper",
                return_value=[item],
            ) as review_items,
            mock.patch.object(
                review_dashboard,
                "filter_items_by_slice",
                return_value=[item],
            ) as filter_items,
            mock.patch.object(
                review_dashboard,
                "current_semantic_review_surface",
                return_value=review_dashboard._CurrentSemanticReviewSurface(
                    human_claims=[],
                    library_prerequisites=[],
                    library_summary={"needs_attention": False},
                ),
            ) as semantic_surface,
            mock.patch.object(
                review_dashboard,
                "paper_coverage_audit_summary",
                return_value=summary,
            ) as coverage_summary,
        ):
            rows = review_dashboard.direct_paper_coverage_audit_rows(
                "ExamplePaper", "main"
            )

        self.assertEqual(rows, [{"paper": "ExamplePaper", **summary}])
        load_authority.assert_called_once_with(folder)
        review_items.assert_called_once_with(
            folder,
            use_cache=True,
            render_images=False,
            semantic_reuse_authority=authority,
        )
        filter_items.assert_called_once_with([item], "ExamplePaper", "main")
        semantic_surface.assert_called_once_with(
            folder,
            [item],
            [item],
            semantic_reuse_authority=authority,
        )
        coverage_summary.assert_called_once_with(folder, [item])

    def test_assumption_precheck_uses_fast_saved_receipt_without_dashboard_rows(self) -> None:
        fast_result = {
            "paper": "ExamplePaper",
            "scope": "repository sources/configuration only",
            "needs_attention": False,
            "required_judgment_count": 3,
            "current_judgment_count": 3,
        }
        with (
            mock.patch.object(
                review_dashboard,
                "fast_saved_source_record_assumption_precheck",
                return_value=fast_result,
            ) as fast_precheck,
            mock.patch.object(
                review_dashboard,
                "print_fast_saved_source_record_assumption_precheck",
                return_value=False,
            ) as print_fast,
            mock.patch.object(
                review_dashboard,
                "gather_paper_data",
                side_effect=AssertionError("fast precheck must not build dashboard rows"),
            ),
        ):
            self.assertFalse(review_dashboard.print_assumption_audit_status("ExamplePaper"))

        fast_precheck.assert_called_once_with("ExamplePaper", None)
        print_fast.assert_called_once_with(fast_result)

    def test_hidden_premise_precheck_does_not_run_full_machine_audit(self) -> None:
        with mock.patch.object(
            review_dashboard,
            "conditional_boundary_statement_premises",
            return_value={},
        ), mock.patch(
            "scripts.audit_repository.check_hidden_variable_premises",
            return_value=[],
        ) as hidden_scan, mock.patch(
            "scripts.audit_repository.check_machine_paper_status",
            side_effect=AssertionError("assumption precheck must stay phase-local"),
        ):
            rows = review_dashboard.hidden_premise_repository_audit_rows(
                None
            )

        self.assertEqual(rows, [])
        hidden_scan.assert_called_once_with(include_active=False)

    def test_fast_precheck_marks_unimported_assumption_support_as_inactive(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "ExamplePaper"
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            assumptions = folder / "Assumptions.lean"
            payload = {
                "review_assumption_source": {
                    "path": "papers/ExamplePaper/Assumptions.lean"
                },
                "unconfigured_assumption_support_rows": [
                    "ExamplePaper.legacy_tail_bound"
                ],
            }
            with (
                mock.patch.object(review_dashboard, "ROOT", root),
                mock.patch.object(
                    review_dashboard,
                    "assumption_source_file",
                    return_value=interface,
                ),
            ):
                active, inactive, error = (
                    review_dashboard._fast_source_record_unconfigured_support_scope(
                        folder,
                        payload,
                        {interface},
                    )
                )
                self.assertEqual(active, [])
                self.assertEqual(inactive, ["ExamplePaper.legacy_tail_bound"])
                self.assertEqual(error, "")

                active, inactive, error = (
                    review_dashboard._fast_source_record_unconfigured_support_scope(
                        folder,
                        payload,
                        {interface, assumptions},
                    )
                )
                self.assertEqual(active, ["ExamplePaper.legacy_tail_bound"])
                self.assertEqual(inactive, [])
                self.assertEqual(error, "")

class PaperCloseoutScopingTests(unittest.TestCase):
    def test_paper_closeout_dispatches_without_repository_hygiene(self) -> None:
        expected = [
            audit_repository.Finding(
                "ERROR",
                Path("papers/ExamplePaper/PaperInterface.lean"),
                "selected semantic gate",
            )
        ]
        run_context = mock.Mock()
        evidence_context = mock.Mock()
        evidence_context.source_record_identity_error = ""
        evidence_context.input_snapshots = ()
        evidence_context.watched_input_digest = "fixture-inputs"
        run_context.paper_id = "ExamplePaper"
        run_context.evidence_context = evidence_context
        run_context.selected_v11_closeout = False
        with (
            mock.patch.object(
                audit_repository,
                "check_dag_and_validation_report_closeout",
                return_value=[],
            ),
            mock.patch(
                "scripts.paper_closeout_executor.source_intake_readiness",
                return_value={"ready": True, "errors": []},
            ),
            mock.patch.object(
                audit_repository,
                "build_paper_closeout_evidence_context",
                return_value=evidence_context,
            ),
            mock.patch.object(
                audit_repository.PaperCloseoutRunContext,
                "from_exact_evidence_context",
                return_value=run_context,
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_evidence_context_prebuild_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_fast_route_schema_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "check_machine_paper_status",
                return_value=expected,
            ) as machine_status,
            mock.patch.object(
                audit_repository,
                "paper_closeout_evidence_integrity_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_conclusion_provenance_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "check_paper_root_build_closeout",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "check_generic_source_reference_hygiene",
                side_effect=AssertionError("repository hygiene must not run"),
            ),
            mock.patch.object(
                audit_repository,
                "check_sorries",
                side_effect=AssertionError("global Lean scan must not run"),
            ),
        ):
            findings = audit_repository.run(
                include_active=False,
                strict_style=False,
                paper_filter="ExamplePaper",
                paper_closeout=True,
            )

        self.assertEqual(findings, expected)
        machine_status.assert_called_once_with(
            library_premise_audit=False,
            paper_filter="ExamplePaper",
            paper_closeout=True,
            require_source_bytes=True,
            deep_paper_prose=False,
            prevalidated_strict_v11_occurrence_papers=mock.ANY,
            run_context=mock.ANY,
            phase_timings=mock.ANY,
            phase_progress_callback=mock.ANY,
        )

    def presentation_fixture_findings(
        self, *, deep_paper_prose: bool
    ) -> list[audit_repository.Finding]:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper = papers / "ExamplePaper"
            paper.mkdir(parents=True)
            interface = paper / "PaperInterface.lean"
            interface_text = (
                "namespace ExamplePaper\n"
                "/-- Theorem 1 formula presentation. -/\n"
                "def source_bundle : Prop := True\n"
                "theorem semantic_row (h : SourceCertificate) : True := by trivial\n"
                "end ExamplePaper\n"
            )
            interface.write_text(interface_text, encoding="utf-8")
            status = {
                "id": "ExamplePaper",
                "title": "Example Paper",
                "source_version": "source",
                "build_target": "lake build ExamplePaper.PaperInterface",
                "status": "formalized",
                "review_entrypoint": "papers/ExamplePaper/FINAL_VALIDATION_REPORT.md",
                "human_review": {
                    "reviewed_rows": 2,
                    "total_rows": 2,
                    "stale_rows": 0,
                    "mismatch_rows": 0,
                },
                "paper_interface": {
                    "path": "papers/ExamplePaper/PaperInterface.lean",
                    "line_count": len(interface_text.splitlines()),
                    "declaration_rows": 2,
                    "review_rows": 2,
                    "oversized": False,
                },
                "review_surface": {
                    "source_file": "papers/ExamplePaper/PaperInterface.lean",
                    "include_names": ["source_bundle", "semantic_row"],
                    "assumption_names": [],
                    "auxiliary_names": [],
                },
            }
            (paper / "status.json").write_text(json.dumps(status), encoding="utf-8")

            patches = (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    audit_repository,
                    "PAPER_STATUS_FILE",
                    papers / "missing-aggregate-status.json",
                ),
                mock.patch.object(audit_repository, "paper_dirs", return_value=[paper]),
                mock.patch.object(
                    audit_repository,
                    "paper_statement_sidecar_findings",
                    side_effect=lambda *_args, **_kwargs: [],
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_lean_declaration_index",
                    return_value={},
                ),
                mock.patch.object(
                    audit_repository,
                    "current_statement_conditional_boundary_rows",
                    return_value=set(),
                ),
                mock.patch.object(
                    audit_repository,
                    "current_author_approved_corrected_scope",
                    return_value=False,
                ),
                mock.patch.object(
                    audit_repository,
                    "current_corrected_model_premise_bridge",
                    return_value=None,
                ),
                mock.patch.object(
                    audit_repository,
                    "check_paper_interface_axiom_closure",
                    return_value=[],
                ),
                mock.patch.object(
                    audit_repository,
                    "check_proposition_spec_routes",
                    return_value=[],
                ),
                mock.patch.object(
                    audit_repository,
                    "check_source_proof_fidelity",
                    return_value=[],
                ),
                mock.patch.object(
                    audit_repository,
                    "check_explicit_source_route_semantic_model_evidence",
                    return_value=[],
                ),
                mock.patch.object(
                    audit_repository,
                    "check_source_record_audit",
                    return_value=[],
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_validated_boundary_premises",
                    return_value=set(),
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_complete_model_record_bindings",
                    return_value={},
                ),
                mock.patch.object(
                    audit_repository,
                    "current_named_theory_semantic_review_surface",
                    return_value=(None, ""),
                ),
                mock.patch.object(
                    audit_repository,
                    "load_expanded_review_statements",
                    return_value={},
                ),
            )
            with ExitStack() as stack:
                for patcher in patches:
                    stack.enter_context(patcher)
                return audit_repository.check_machine_paper_status(
                    paper_filter="ExamplePaper",
                    paper_closeout=True,
                    deep_paper_prose=deep_paper_prose,
                )

    def test_paper_closeout_defaults_to_semantic_rows_not_presentation_heuristics(self) -> None:
        default_messages = [
            finding.message
            for finding in self.presentation_fixture_findings(deep_paper_prose=False)
        ]
        deep_messages = [
            finding.message
            for finding in self.presentation_fixture_findings(deep_paper_prose=True)
        ]

        presentation_markers = (
            "broad aggregate name",
            "Source status:",
            "opaque alias/signature",
            "premises not routed through explicit Assumptions.lean",
        )
        self.assertFalse(
            any(marker in message for marker in presentation_markers for message in default_messages),
            default_messages,
        )
        for marker in presentation_markers:
            self.assertTrue(
                any(marker in message for message in deep_messages),
                deep_messages,
            )

    def test_source_status_comment_is_opt_in_for_source_map_bridges(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "PaperInterface.lean").write_text(
                "namespace Example\n"
                "/-- A source-facing bridge without presentation metadata. -/\n"
                "theorem bridge : True := by trivial\n"
                "end Example\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["Example.bridge"],
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_theorem": {
                                "source_kind": "theorem",
                                "title": "Theorem 1. Fixture result",
                                "lean_declarations": ["Example.bridge"],
                                "proof_lean_declarations": ["Example.bridge"],
                                "semantic_bridge_declarations": ["Example.bridge"],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                audit_repository, "library_lean_declaration_index", return_value={}
            ):
                default_findings = audit_repository.paper_statement_map_declaration_findings(
                    "Example", folder, "formalized"
                )
                deep_findings = audit_repository.paper_statement_map_declaration_findings(
                    "Example",
                    folder,
                    "formalized",
                    presentation_hygiene=True,
                )

        self.assertFalse(
            any("lack a `Source status:`" in finding.message for finding in default_findings),
            [finding.message for finding in default_findings],
        )
        self.assertTrue(
            any("lack a `Source status:`" in finding.message for finding in deep_findings),
            [finding.message for finding in deep_findings],
        )

    def test_selected_v11_direct_library_route_needs_no_paper_wrapper(self) -> None:
        """Location-neutral v11 review must not manufacture equivalence aliases."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            folder.mkdir()
            audit = folder / "audit"
            audit.mkdir()
            statement_map = {
                "items": {
                    "source_definition": {
                        "source_kind": "definition",
                        "source_location": "source.txt:1-2",
                        "statement": "Definition 1. The reusable model has carrier Nat.",
                        "lean_declarations": ["AppliedModelingLib.Example.ReusableModel"],
                    }
                }
            }
            status = {
                "status": "formalized",
                "review_surface": {
                    "include_names": [],
                    "assumption_names": [],
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(statement_map), encoding="utf-8"
            )
            (folder / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            declaration = audit_repository.LeanDeclaration(
                path=Path(temp_dir) / "AppliedModelingLib" / "Example.lean",
                line=1,
                kind="def",
                name="ReusableModel",
                source="def ReusableModel : Nat := 0",
                qualified_name="AppliedModelingLib.Example.ReusableModel",
            )
            library_index = {
                "AppliedModelingLib.Example.ReusableModel": [declaration],
                "ReusableModel": [declaration],
            }
            context = mock.Mock()
            context.selected_v11_closeout = True
            context.evidence_context = None
            context.paper_declaration_index.return_value = {}
            context.library_declaration_index.return_value = library_index
            context.exact_json_payload.side_effect = lambda path: (
                statement_map
                if path.name == "paper_statement_map.json"
                else status
                if path.name == "status.json"
                else None
            )

            with mock.patch.object(
                audit_repository,
                "review_declaration_comments",
                side_effect=AssertionError(
                    "selected v11 routes must not parse Lean comments"
                ),
            ):
                current = audit_repository.paper_statement_map_declaration_findings(
                    folder.name,
                    folder,
                    "formalized",
                    run_context=context,
                    skip_semantic_contract_lean=True,
                )
            with mock.patch.object(
                audit_repository,
                "library_lean_declaration_index",
                return_value=library_index,
            ):
                legacy = audit_repository.paper_statement_map_declaration_findings(
                    folder.name,
                    folder,
                    "formalized",
                    skip_semantic_contract_lean=True,
                )

        self.assertFalse(
            any("directly to reusable-library" in finding.message for finding in current),
            [finding.message for finding in current],
        )
        self.assertTrue(
            any("directly to reusable-library" in finding.message for finding in legacy),
            [finding.message for finding in legacy],
        )


if __name__ == "__main__":
    unittest.main()
