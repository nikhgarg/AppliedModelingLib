from __future__ import annotations

import copy
import io
import json
import subprocess
import unittest
from contextlib import ExitStack, redirect_stderr
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import lean_signature_manifest as manifest
from scripts import lean_review_surface as review_surface
from scripts.current_closeout.declarations import declaration_index_from_inventory


ROOT = Path(__file__).resolve().parents[2]


class LeanDeclarationInventoryTests(unittest.TestCase):
    HASH_TOOL_IDENTITY = {
        "schema": "1",
        "command": "sha256sum",
        "resolved_path": "/fixture/sha256sum",
        "executable_sha256": "f" * 64,
        "version_stdout_sha256": "e" * 64,
        "version_banner": "sha256sum fixture",
        "known_vector": "sha256(abc)",
        "known_vector_sha256": (
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        ),
    }

    def test_review_surface_has_one_module_owner(self) -> None:
        self.assertFalse(
            hasattr(manifest, "semantic_review_display_surface_from_inventory")
        )
        self.assertFalse(hasattr(manifest, "LeanSemanticReviewDisplaySurface"))
        self.assertTrue(
            callable(review_surface.semantic_review_display_surface_from_inventory)
        )
        self.assertTrue(callable(review_surface.lean_source_range_text))

    def test_current_graph_uses_module_ownership_not_econcslib_spelling(self) -> None:
        source = (ROOT / "AppliedModelingLib" / "Audit" / "DeclarationGraph.lean").read_text(
            encoding="utf-8"
        )
        self.assertNotIn('startsWith "AppliedModelingLib.', source)
        self.assertNotIn('Name.mkSimple "AppliedModelingLib"', source)

    @staticmethod
    def _semantic_signature(declaration: str) -> dict[str, object]:
        return {
            "declaration": declaration,
            "signature": {
                "schema": "2",
                "declaration_kind": "definition",
                "conclusion_mode": "type_and_value",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": {"tag": "const", "name": "True"},
                        "display": "Prop := True",
                    }
                ],
            },
        }

    def _payload(self) -> dict[str, object]:
        registry = manifest.load_foundation_registry(ROOT)
        return {
            "schema": "4",
            "inventory_modules": [],
            "paper_modules": ["Fixture.ProofInterface"],
            "workspace_modules": ["Fixture.ProofInterface"],
            "module_range_entry_count": 0,
            "generated_constant_count": 0,
            "source_declarations": [],
            "declarations": [],
            "proof_pairs": [
                {
                    "specification": "Fixture.claimSpec",
                    "proof": "Fixture.claim",
                    "matches": True,
                    "proof_is_unsafe": False,
                    "proof_value_has_sorry": False,
                    "proof_axiom_closure_checked": False,
                    "proof_axiom_closure": [],
                }
            ],
            "semantic_contracts": [],
            "semantic_signatures": {"schema": "1", "items": [], "errors": []},
            "semantic_review_claims": {"schema": "1", "items": [], "errors": []},
            "semantic_manifests": {"schema": "1", "items": [], "errors": []},
            "root_semantic_manifests": {
                "schema": "1",
                "items": [],
                "errors": [],
            },
            "semantic_revalidations": {
                "schema": "1",
                "items": [],
                "errors": [],
            },
            "foundation_frontier_preview": {
                "schema": "1",
                "acceptance_credential": False,
                "foundation_policy_id": registry.policy_id,
                "foundation_registry_sha256": registry.sha256,
                "foundation_module_roots": list(registry.module_roots),
                "specifications": [],
                "promoted_expansions": [],
                "summary": {
                    "specification_count": 0,
                    "conventional_foundation_root_count": 0,
                    "promoted_root_count": 0,
                    "promoted_expansion_row_count": 0,
                    "maximum_promoted_depth": 0,
                    "promoted_reuse_count": 0,
                    "domain_root_count": 0,
                    "unregistered_external_root_count": 0,
                },
            },
            "transparent_spec_displays": {"schema": "2", "items": []},
            "paper_prerequisite_displays": {"schema": "2", "items": []},
            "library_prerequisite_displays": {"schema": "3", "items": []},
        }

    def _parse(
        self,
        payload: dict[str, object],
        *,
        semantic_declarations: tuple[str, ...] = (),
        semantic_contracts: tuple[tuple[str, str, str], ...] = (),
        semantic_signatures: tuple[str, ...] = (),
        semantic_review_claims: tuple[str, ...] = (),
        semantic_manifests: tuple[str, ...] = (),
        semantic_revalidations: tuple[str, ...] = (),
        include_semantic_displays: bool = False,
    ) -> dict[str, object] | None:
        return manifest._parse_declaration_inventory_output(
            manifest.DECLARATION_INVENTORY_SENTINEL
            + json.dumps(payload, sort_keys=True, separators=(",", ":")),
            inventory_modules=(),
            paper_modules=("Fixture.ProofInterface",),
            workspace_modules=("Fixture.ProofInterface",),
            specifications=(),
            semantic_declarations=semantic_declarations,
            proof_pairs=(("Fixture.claimSpec", "Fixture.claim"),),
            semantic_contracts=semantic_contracts,
            axiom_roots=(),
            semantic_signature_declarations=semantic_signatures,
            semantic_review_claim_declarations=semantic_review_claims,
            semantic_manifest_declarations=semantic_manifests,
            root_semantic_manifest_declarations=(),
            semantic_revalidation_declarations=semantic_revalidations,
            foundation_registry=manifest.load_foundation_registry(ROOT),
            promoted_foundation_declarations=(),
            include_semantic_displays=include_semantic_displays,
            include_axiom_closure=False,
        )

    def test_lean_source_ranges_slice_unicode_character_columns(self) -> None:
        source = "namespace Fixture\n  def claim : Prop := ⟨True⟩\nend Fixture\n"
        selected = review_surface.lean_source_range_text(
            source.encode("utf-8"),
            {
                "line_start": 2,
                "column_start": 2,
                "line_end": 2,
                "column_end": len("  def claim : Prop := ⟨True⟩"),
            },
        )
        self.assertEqual(selected, "def claim : Prop := ⟨True⟩")

    def test_source_declaration_projection_uses_only_lean_owned_ranges(self) -> None:
        path = Path("/repo/Fixture/PaperInterface.lean")
        source = b"namespace Fixture\ndef claimSpec : Prop := True\nend Fixture\n"
        raw_range = {
            "line_start": 2,
            "column_start": 0,
            "line_end": 2,
            "column_end": len("def claimSpec : Prop := True"),
        }
        payload = {
            "source_declarations": ["Fixture.claimSpec"],
            "declarations": [
                {
                    "declaration": "Fixture.claimSpec",
                    "review_owner_declaration": "Fixture.claimSpec",
                    "generated_from_owner": False,
                    "module": "Fixture.PaperInterface",
                    "source_presented": True,
                    "source_range": raw_range,
                    "declaration_kind": "definition",
                    "is_transparent_definition": True,
                    "type_display": "Prop",
                }
            ],
        }
        records = manifest.lean_inventory_source_declaration_records(
            payload,
            {"Fixture.PaperInterface": (path, source)},
        )
        self.assertEqual(
            records["Fixture.claimSpec"]["source"],
            "def claimSpec : Prop := True",
        )
        malformed = copy.deepcopy(payload)
        malformed["declarations"][0]["source_range"] = None  # type: ignore[index]
        with self.assertRaisesRegex(ValueError, "source range"):
            manifest.lean_inventory_source_declaration_records(
                malformed,
                {"Fixture.PaperInterface": (path, source)},
            )

    def test_configured_support_can_use_lean_owned_unpresented_declaration(self) -> None:
        """A source-condition declaration need not itself be a review row."""

        path = Path("/repo/Fixture/Assumptions.lean")
        source = b"def sourceCondition : Prop := True\n"
        inventory = {
            "declarations": [
                {
                    "declaration": "Fixture.sourceCondition",
                    "module": "Fixture.Assumptions",
                    "declaration_kind": "definition",
                    "paper_owned": False,
                    "source_presented": False,
                    "generated_from_owner": False,
                    "review_owner_declaration": "Fixture.sourceCondition",
                    "source_range": {
                        "line_start": 1,
                        "column_start": 0,
                        "line_end": 1,
                        "column_end": len("def sourceCondition : Prop := True"),
                    },
                }
            ]
        }
        modules = {"Fixture.Assumptions": (path, source)}

        self.assertEqual(declaration_index_from_inventory(inventory, modules), {})
        resolved = declaration_index_from_inventory(
            inventory,
            modules,
            source_presented_only=False,
            paper_owned_only=False,
        )
        self.assertEqual(resolved["Fixture.sourceCondition"][0].path, path)

    def test_explicit_source_projection_does_not_require_module_wide_discovery(
        self,
    ) -> None:
        path = Path("/repo/Fixture/PaperInterface.lean")
        source = b"namespace Fixture\ndef claimSpec : Prop := True\nend Fixture\n"
        payload = {
            "source_declarations": [],
            "declarations": [
                {
                    "declaration": "Fixture.claimSpec",
                    "review_owner_declaration": "Fixture.claimSpec",
                    "generated_from_owner": False,
                    "module": "Fixture.PaperInterface",
                    "source_presented": True,
                    "source_range": {
                        "line_start": 2,
                        "column_start": 0,
                        "line_end": 2,
                        "column_end": len("def claimSpec : Prop := True"),
                    },
                    "declaration_kind": "definition",
                    "is_transparent_definition": True,
                    "type_display": "Prop",
                }
            ],
        }
        records = manifest.lean_inventory_source_declaration_records(
            payload,
            {"Fixture.PaperInterface": (path, source)},
            declaration_names={"Fixture.claimSpec"},
        )
        self.assertEqual(records["Fixture.claimSpec"]["source_sha256"],
                         manifest.hashlib.sha256(b"def claimSpec : Prop := True").hexdigest())

    def test_direct_spec_body_retains_named_prerequisites_as_separate_cards(
        self,
    ) -> None:
        """The renderer never unfolds a helper just to simplify a source row."""

        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        namespace = "AppliedModelingLibAudit.DeclarationGraphFixture"
        primitive = namespace + ".reviewedPrimitive"
        helper = namespace + ".transparentHelper"
        specification = namespace + ".claimSpec"
        graph = manifest.run_lean_paper_semantic_review_graph(
            ROOT,
            module,
            specification_names=(specification,),
            semantic_declaration_names=(primitive,),
            semantic_review_claim_declaration_names=(specification,),
            paper_modules=(module,),
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        self.assertTrue(graph)
        display = graph["specification_targets"][specification]
        self.assertIn(primitive, display["prerequisite_declarations"])
        self.assertIn(helper, display["prerequisite_declarations"])
        self.assertIn(primitive, display["display"])
        self.assertIn(helper, display["display"])
        self.assertEqual(display["expanded_declarations"], (specification,))
        prerequisite = graph["paper_declaration_targets"][primitive]
        self.assertTrue(prerequisite["root_expanded"])
        self.assertIn("ℕ → ℕ", prerequisite["display"])
        self.assertIn("n + 1", prerequisite["display"])
        helper_prerequisite = graph["paper_declaration_targets"][helper]
        self.assertTrue(helper_prerequisite["root_expanded"])
        self.assertIn("n + 1", helper_prerequisite["display"])
        claim = graph["review_claim_surfaces"][specification]
        self.assertRegex(claim["manifest_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(claim["claim_atoms_sha256"], r"^[0-9a-f]{64}$")

    def test_material_private_declaration_is_not_a_review_target(self) -> None:
        """Lean rejects an unstable private address only after role selection."""

        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        hidden = (
            "_private.AppliedModelingLib.Audit.DeclarationGraphFixture.0."
            "AppliedModelingLibAudit.DeclarationGraphFixture.hiddenReviewedPrimitive"
        )
        diagnostics = io.StringIO()
        with redirect_stderr(diagnostics):
            payload = manifest.run_lean_declaration_inventory(
                ROOT,
                module,
                inventory_modules=(),
                paper_modules=(module,),
                semantic_declaration_names=(hidden,),
                include_semantic_displays=True,
                include_axiom_closure=False,
                timeout_seconds=120,
                build_timeout_seconds=120,
            )
        self.assertEqual(payload, {})
        self.assertIn(
            "private or compiler-internal and cannot be a stable review target",
            diagnostics.getvalue(),
        )

    def test_range_less_generated_child_reduces_without_name_ownership(self) -> None:
        """Transparent compiler plumbing reduces; the source inductive appears once."""

        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        namespace = "AppliedModelingLibAudit.DeclarationGraphFixture"
        owner = namespace + ".GeneratedChoice"
        generated = owner + ".ctorIdx"
        generated_instance = namespace + ".instDecidableEqGeneratedChoice"
        hand_written = owner + ".sourcePresentedChild"
        specification = namespace + ".generatedOwnerClaimSpec"
        graph = manifest.run_lean_paper_semantic_review_graph(
            ROOT,
            module,
            specification_names=(specification,),
            semantic_declaration_names=(owner, hand_written),
            semantic_review_claim_declaration_names=(specification,),
            paper_modules=(module,),
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        self.assertTrue(graph)
        target = graph["specification_targets"][specification]
        self.assertIn(owner, target["prerequisite_declarations"])
        self.assertNotIn(generated, target["prerequisite_declarations"])
        self.assertNotIn(generated_instance, target["prerequisite_declarations"])
        self.assertNotIn(generated, graph["paper_declaration_targets"])
        self.assertNotIn(generated_instance, graph["paper_declaration_targets"])
        owner_target = graph["paper_declaration_targets"][owner]
        self.assertFalse(owner_target["root_expanded"])
        self.assertIn(
            "constructor " + owner + ".left:", owner_target["display"]
        )
        self.assertIn(
            "constructor " + owner + ".right:", owner_target["display"]
        )
        self.assertIn(hand_written, graph["paper_declaration_targets"])
        self.assertTrue(
            graph["paper_declaration_targets"][hand_written]["root_expanded"]
        )

    def test_lean_partitions_explicit_semantic_roots_by_module_ownership(
        self,
    ) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        paper_root = "AppliedModelingLibAudit.DeclarationGraphFixture.reviewedPrimitive"
        library_root = "AppliedModelingLib.FairDivision.Bundle"
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(library_root, paper_root),
            semantic_signature_declaration_names=(library_root, paper_root),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(),
            expected_paper_declarations=(paper_root,),
            expected_library_declarations=(library_root,),
        )
        self.assertEqual(set(surface.paper_declarations), {paper_root})
        self.assertEqual(set(surface.library_declarations), {library_root})

    def test_graph_wrapper_keeps_opaque_paper_and_library_roots_without_claim_atoms(
        self,
    ) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        specification = (
            "AppliedModelingLibAudit.DeclarationGraphFixture.libraryPrimitiveClaimSpec"
        )
        paper_root = "AppliedModelingLibAudit.DeclarationGraphFixture.GeneratedChoice"
        library_root = (
            "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.helperCarryingValue"
        )
        graph = manifest.run_lean_paper_semantic_review_graph(
            ROOT,
            module,
            specification_names=(specification,),
            semantic_declaration_names=(paper_root, library_root),
            semantic_review_claim_declaration_names=(),
            paper_modules=(module,),
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        self.assertTrue(graph)
        self.assertIn(paper_root, graph["paper_declaration_targets"])
        self.assertIn(library_root, graph["library_declaration_targets"])
        self.assertEqual(graph["review_claim_surfaces"], {})
        self.assertEqual(graph["review_claim_errors"], {})

    def test_spec_retains_explicit_library_root_without_duplicate_expansion(
        self,
    ) -> None:
        """A routed library meaning has one card and remains named in the Spec."""

        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        specification = (
            "AppliedModelingLibAudit.DeclarationGraphFixture.libraryPrimitiveClaimSpec"
        )
        root = (
            "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.helperCarryingValue"
        )
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            specification_names=(specification,),
            semantic_declaration_names=(root,),
            semantic_signature_declaration_names=(root,),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(specification,),
            expected_paper_declarations=(),
            expected_library_declarations=(
                root,
                "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary."
                "transparentImplementationHelper",
            ),
        )
        spec = surface.specifications[specification]
        self.assertIn(root, spec["display"])
        self.assertEqual(spec["library_declarations"], (root,))
        self.assertNotIn("+ 1", spec["display"])
        self.assertNotIn("+ 1", surface.library_declarations[root]["display"])
        self.assertIn(
            "+ 1",
            surface.library_declarations[
                "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary."
                "transparentImplementationHelper"
            ]["display"],
        )

    def test_library_semantic_frontier_keeps_named_prerequisites_as_cards(
        self,
    ) -> None:
        """A direct body names a reviewed predicate; proof plumbing is omitted."""

        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        namespace = "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary"
        root = namespace + ".proofCarryingValue"
        predicate = namespace + ".MaterialPredicate"
        proved_helper = namespace + ".provedImplementationHelper"
        graph = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(root,),
            semantic_signature_declaration_names=(root,),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            graph,
            expected_specifications=(),
            expected_paper_declarations=(),
            expected_library_declarations=(root, predicate),
        )
        self.assertEqual(set(surface.library_declarations), {root, predicate})
        root_target = surface.library_declarations[root]
        self.assertIn(predicate, root_target["direct_library_declarations"])
        self.assertIn(predicate, root_target["display"])
        self.assertIn(proved_helper, root_target["display"])
        self.assertNotIn("m = m", root_target["display"])
        self.assertIn(
            "n = n", surface.library_declarations[predicate]["display"]
        )
        self.assertEqual(
            root_target["erased_proof_declarations"],
            (proved_helper,),
        )
        self.assertNotIn(proved_helper, surface.library_declarations)

    def test_explicit_library_theorem_remains_a_semantic_review_root(self) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        namespace = "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary"
        theorem = namespace + ".explicitSourceLaw"
        carrier = namespace + ".explicitLawCarryingValue"
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(carrier, theorem),
            semantic_signature_declaration_names=(carrier, theorem),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(),
            expected_paper_declarations=(),
            expected_library_declarations=(
                carrier,
                theorem,
                namespace + ".MaterialPredicate",
            ),
        )
        self.assertIn(theorem, surface.library_declarations)
        self.assertIn(
            theorem,
            surface.library_declarations[carrier]["direct_library_declarations"],
        )
        self.assertNotIn(
            theorem,
            surface.library_declarations[carrier][
                "erased_proof_declarations"
            ],
        )

    def test_library_axiom_remains_visible_as_an_unproved_boundary(self) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        namespace = "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary"
        root = namespace + ".boundaryCarryingValue"
        predicate = namespace + ".MaterialPredicate"
        boundary = namespace + ".unprovedBoundary"
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(root,),
            semantic_signature_declaration_names=(root,),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(),
            expected_paper_declarations=(),
            expected_library_declarations=(boundary, predicate, root),
        )
        self.assertIn(boundary, surface.library_declarations)
        self.assertEqual(
            surface.library_declarations[boundary]["declaration_kind"],
            "non_definition",
        )
        self.assertNotIn(
            boundary,
            surface.library_declarations[root]["erased_proof_declarations"],
        )
        self.assertIn(predicate, surface.library_declarations)
        self.assertIn(predicate, surface.library_declarations[boundary]["display"])
        self.assertIn("n = n", surface.library_declarations[predicate]["display"])

    def test_transparent_library_helper_is_its_own_direct_card(self) -> None:
        """The review surface never unfolds an ordinary helper into its caller."""

        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        namespace = "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary"
        root = namespace + ".helperCarryingValue"
        helper = namespace + ".transparentImplementationHelper"
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(root,),
            semantic_signature_declaration_names=(root,),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(),
            expected_paper_declarations=(),
            expected_library_declarations=(root, helper),
        )
        target = surface.library_declarations[root]
        self.assertIn(helper, surface.library_declarations)
        self.assertIn(helper, target["direct_library_declarations"])
        self.assertIn(helper, target["display"])
        self.assertNotIn("+ 1", target["display"])
        self.assertIn("+ 1", surface.library_declarations[helper]["display"])

    def test_pattern_definition_has_one_direct_source_owner_card(
        self,
    ) -> None:
        """The graph reaches a source owner without exposing a matcher artifact."""

        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        root = (
            "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary."
            "transparentPatternValue"
        )
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(root,),
            semantic_signature_declaration_names=(root,),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(),
            expected_paper_declarations=(),
            expected_library_declarations=(root,),
        )
        self.assertEqual(set(surface.library_declarations), {root})
        display = surface.library_declarations[root]["display"]
        self.assertIn("match a with", display)
        self.assertIn("n + 1", display)
        self.assertNotIn("match_", display)

    def test_explicit_paper_theorem_remains_a_semantic_review_root(self) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        paper_namespace = "AppliedModelingLibAudit.DeclarationGraphFixture"
        library_namespace = "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary"
        theorem = paper_namespace + ".explicitPaperSourceLaw"
        carrier = paper_namespace + ".explicitPaperLawCarryingValue"
        predicate = library_namespace + ".MaterialPredicate"
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(carrier, theorem),
            semantic_signature_declaration_names=(carrier, theorem),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(),
            expected_paper_declarations=(carrier, theorem),
            expected_library_declarations=(predicate,),
        )
        self.assertIn(theorem, surface.paper_declarations)
        self.assertIn(
            theorem,
            surface.paper_declarations[carrier]["direct_paper_declarations"],
        )
        self.assertNotIn(
            theorem,
            surface.paper_declarations[carrier]["erased_proof_declarations"],
        )
        self.assertIn(predicate, surface.library_declarations)
        self.assertIn(predicate, surface.paper_declarations[theorem]["display"])
        self.assertIn("n = n", surface.library_declarations[predicate]["display"])

    def test_unrouted_paper_proof_value_retains_its_proposition_semantics(self) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        paper_namespace = "AppliedModelingLibAudit.DeclarationGraphFixture"
        library_namespace = "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary"
        theorem = paper_namespace + ".explicitPaperSourceLaw"
        carrier = paper_namespace + ".explicitPaperLawCarryingValue"
        predicate = library_namespace + ".MaterialPredicate"
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            semantic_declaration_names=(carrier,),
            semantic_signature_declaration_names=(carrier,),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications=(),
            expected_paper_declarations=(carrier,),
            expected_library_declarations=(predicate,),
        )
        self.assertEqual(
            surface.paper_declarations[carrier]["erased_proof_declarations"],
            (theorem,),
        )
        self.assertIn(predicate, surface.library_declarations)
        self.assertIn(theorem, surface.paper_declarations[carrier]["display"])
        self.assertNotIn("m = m", surface.paper_declarations[carrier]["display"])
        self.assertIn("n = n", surface.library_declarations[predicate]["display"])

    def test_proof_plumbing_suppression_does_not_weaken_axiom_closure(self) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        namespace = "AppliedModelingLibAudit.DeclarationGraphFixture"
        specification = namespace + ".boundaryClosureClaimSpec"
        proof = namespace + ".boundaryClosureClaim"
        boundary = (
            "AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.unprovedBoundary"
        )
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            specification_names=(specification,),
            proof_pairs=((specification, proof),),
            include_semantic_displays=True,
            include_axiom_closure=True,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        pair = payload["proof_pairs"][0]
        self.assertTrue(pair["matches"])
        self.assertTrue(pair["proof_axiom_closure_checked"])
        self.assertIn(boundary, pair["proof_axiom_closure"])

    def test_foundation_frontier_preview_is_lean_owned_and_non_evidentiary(
        self,
    ) -> None:
        module = "AppliedModelingLib.Audit.DeclarationGraphFixture"
        specification = "AppliedModelingLibAudit.DeclarationGraphFixture.claimSpec"
        paper_root = "AppliedModelingLibAudit.DeclarationGraphFixture.reviewedPrimitive"
        payload = manifest.run_lean_declaration_inventory(
            ROOT,
            module,
            inventory_modules=(),
            paper_modules=(module,),
            specification_names=(specification,),
            semantic_declaration_names=(paper_root,),
            promoted_foundation_declaration_names=("Nat",),
            include_semantic_displays=True,
            include_axiom_closure=False,
            timeout_seconds=120,
            build_timeout_seconds=120,
        )

        preview = payload["foundation_frontier_preview"]
        self.assertIs(preview["acceptance_credential"], False)
        self.assertEqual(preview["summary"]["specification_count"], 1)
        self.assertEqual(preview["summary"]["promoted_root_count"], 1)
        self.assertEqual(preview["summary"]["promoted_expansion_row_count"], 1)
        self.assertEqual(
            preview["promoted_expansions"][0]["declaration"], "Nat"
        )
        display = preview["promoted_expansions"][0]["display"]
        self.assertIn("constructor Nat.zero:", display)
        self.assertIn("constructor Nat.succ:", display)
        spec_row = preview["specifications"][0]
        self.assertEqual(spec_row["specification"], specification)
        self.assertEqual(
            [row["declaration"] for row in spec_row["promoted_foundation_occurrences"]],
            ["Nat"],
        )
        self.assertIn(
            paper_root,
            [row["declaration"] for row in spec_row["paper_semantic_roots"]],
        )
        self.assertEqual(spec_row["unregistered_external_occurrences"], [])

    def test_foundation_frontier_preview_transport_fails_closed(self) -> None:
        payload = self._payload()
        preview = payload["foundation_frontier_preview"]
        assert isinstance(preview, dict)
        preview["acceptance_credential"] = True
        self.assertIsNone(self._parse(payload))

    def test_spec_display_cache_is_bound_to_exact_semantic_terminals(self) -> None:
        runtime_key = ("/repo", "Fixture.PaperInterface", ("digest", 1), ("graph", 1))
        modules = ("Fixture.PaperInterface",)
        terminal = "Fixture.SourceModel"
        manifest._DECLARATION_SPEC_DISPLAY_CACHE.clear()
        self.addCleanup(manifest._DECLARATION_SPEC_DISPLAY_CACHE.clear)
        payload = {
            "transparent_spec_displays": {
                "schema": "2",
                "items": [
                    {
                        "specification": "Fixture.claimSpec",
                        "display": "Fixture.SourceModel value",
                    }
                ],
            },
            "paper_prerequisite_displays": {"schema": "2", "items": []},
            "library_prerequisite_displays": {"schema": "3", "items": []},
        }
        manifest._cache_declaration_inventory_displays(
            runtime_key,
            modules,
            payload,
            (terminal,),
        )
        with mock.patch.object(
            manifest,
            "_declaration_inventory_runtime_cache_key",
            return_value=runtime_key,
        ):
            current = manifest._cached_declaration_display_section(
                Path("/repo"),
                "Fixture.PaperInterface",
                ["Fixture.claimSpec"],
                paper_modules=modules,
                paper_declarations=(terminal,),
                kind="spec",
            )
            stale = manifest._cached_declaration_display_section(
                Path("/repo"),
                "Fixture.PaperInterface",
                ["Fixture.claimSpec"],
                paper_modules=modules,
                paper_declarations=(),
                kind="spec",
            )
        self.assertIsNotNone(current)
        self.assertIsNone(stale)

    def test_inventory_nodes_are_exactly_the_lean_discovered_review_closure(
        self,
    ) -> None:
        root = "Fixture.SourceModel"
        dependency = "Fixture.SourcePolicy"

        def node(name: str) -> dict[str, object]:
            return {
                "declaration": name,
                "review_owner_declaration": name,
                "generated_from_owner": False,
                "module": "Fixture.ProofInterface",
                "owner_module": "Fixture.ProofInterface",
                "paper_owned": True,
                "declaration_kind": "definition",
                "is_unsafe": False,
                "is_transparent_definition": True,
                "is_opaque": False,
                "is_axiom": False,
                "value_has_sorry": False,
                "source_presented": True,
                "source_range": {
                    "line_start": 1,
                    "column_start": 0,
                    "line_end": 1,
                    "column_end": 1,
                },
                "owner_source_range": {
                    "line_start": 1,
                    "column_start": 0,
                    "line_end": 1,
                    "column_end": 1,
                },
                "type_display": "Type",
                "direct_dependencies": [],
                "axiom_closure_checked": False,
                "axiom_closure": [],
            }

        payload = self._payload()
        payload["declarations"] = [node(root), node(dependency)]
        payload["paper_prerequisite_displays"] = {
            "schema": "2",
            "items": [
                {
                    "declaration": root,
                    "declaration_kind": "definition",
                    "root_expanded": True,
                    "direct_paper_declarations": [dependency],
                    "direct_library_declarations": [],
                    "erased_proof_declarations": [],
                    "display": "Fixture.SourcePolicy",
                },
                {
                    "declaration": dependency,
                    "declaration_kind": "definition",
                    "root_expanded": True,
                    "direct_paper_declarations": [],
                    "direct_library_declarations": [],
                    "erased_proof_declarations": [],
                    "display": "Nat",
                },
            ],
        }
        payload["semantic_signatures"] = {
            "schema": "1",
            "items": [
                self._semantic_signature(root),
                self._semantic_signature(dependency),
            ],
            "errors": [],
        }
        self.assertIsNotNone(
            self._parse(
                payload,
                semantic_declarations=(root,),
                include_semantic_displays=True,
            )
        )

        missing_semantic_identity = copy.deepcopy(payload)
        missing_semantic_identity["semantic_signatures"]["items"].pop()  # type: ignore[index]
        self.assertIsNone(
            self._parse(
                missing_semantic_identity,
                semantic_declarations=(root,),
                include_semantic_displays=True,
            )
        )

        missing_reached_dependency = copy.deepcopy(payload)
        missing_reached_dependency["declarations"] = [node(root)]
        self.assertIsNone(
            self._parse(
                missing_reached_dependency,
                semantic_declarations=(root,),
                include_semantic_displays=True,
            )
        )

        unrelated_module_helper = copy.deepcopy(payload)
        unrelated_module_helper["declarations"].append(node("Fixture.Unrelated"))
        self.assertIsNone(
            self._parse(
                unrelated_module_helper,
                semantic_declarations=(root,),
                include_semantic_displays=True,
            )
        )

    def test_library_projection_rejects_a_saved_line_hint_without_lean_range(self) -> None:
        payload = {
            "library_prerequisite_displays": {
                "schema": "3",
                "items": [
                    {
                        "declaration": "AppliedModelingLib.Model",
                        "review_owner_declaration": "AppliedModelingLib.Model",
                        "source_module": "AppliedModelingLib.Model",
                        "source_line_start": 999,
                        "source_column_start": 0,
                        "source_line_end": 999,
                        "source_column_end": 1,
                        "declaration_kind": "definition",
                        "root_expanded": True,
                    }
                ],
            }
        }
        with self.assertRaisesRegex(ValueError, "frozen source range"):
            manifest.lean_inventory_library_source_declaration_records(
                payload,
                {
                    "AppliedModelingLib.Model": (
                        Path("/repo/AppliedModelingLib/Model.lean"),
                        b"def Model : Nat := 0\n",
                    )
                },
            )

    def test_review_module_projection_uses_lean_ownership_not_source_ranges(
        self,
    ) -> None:
        payload = {
            "declarations": [
                {
                    "declaration": "Fixture.Input",
                    "review_owner_declaration": "Fixture.Input",
                    "generated_from_owner": False,
                    "module": "Fixture.PaperInterface",
                    "paper_owned": True,
                    "source_presented": True,
                    "source_range": None,
                }
            ],
            "library_prerequisite_displays": {
                "schema": "3",
                "items": [
                    {
                        "declaration": "AppliedModelingLib.Model",
                        "review_owner_declaration": "AppliedModelingLib.Model",
                        "source_module": "AppliedModelingLib.Model",
                    },
                    {
                        "declaration": "AppliedModelingLib.NewerExtra",
                        "review_owner_declaration": "AppliedModelingLib.NewerExtra",
                        "source_module": "AppliedModelingLib.Newer",
                    },
                ],
            },
        }
        self.assertEqual(
            manifest.lean_inventory_review_declaration_modules(
                payload,
                paper_declarations={"Fixture.Input"},
                library_declarations={"AppliedModelingLib.Model"},
            ),
            {
                "Fixture.Input": "Fixture.PaperInterface",
                "AppliedModelingLib.Model": "AppliedModelingLib.Model",
            },
        )

        wrong_owner = copy.deepcopy(payload)
        wrong_owner["declarations"][0]["paper_owned"] = False  # type: ignore[index]
        with self.assertRaisesRegex(ValueError, "unique source module"):
            manifest.lean_inventory_review_declaration_modules(
                wrong_owner,
                paper_declarations={"Fixture.Input"},
                library_declarations={"AppliedModelingLib.Model"},
            )

    def test_typed_proof_response_requires_every_safety_fact(self) -> None:
        payload = self._payload()
        self.assertIsNotNone(self._parse(payload))
        for field in (
            "proof_is_unsafe",
            "proof_value_has_sorry",
            "proof_axiom_closure_checked",
            "proof_axiom_closure",
        ):
            malformed = copy.deepcopy(payload)
            del malformed["proof_pairs"][0][field]  # type: ignore[index]
            self.assertIsNone(self._parse(malformed), field)

    def test_typed_semantic_contract_requires_relation_and_safety_facts(self) -> None:
        payload = self._payload()
        contract = (
            "Fixture.claimSpec",
            "Fixture.claim",
            "definitionally_realizes",
        )
        payload["semantic_contracts"] = [
            {
                "specification": contract[0],
                "evidence": contract[1],
                "mode": contract[2],
                "matches": True,
                "evidence_is_unsafe": False,
                "evidence_value_has_sorry": False,
                "evidence_axiom_closure_checked": False,
                "evidence_axiom_closure": [],
            }
        ]
        payload["declarations"] = [
            {
                "declaration": contract[1],
                "review_owner_declaration": contract[1],
                "generated_from_owner": False,
                "module": "Fixture.ProofInterface",
                "owner_module": "Fixture.ProofInterface",
                "paper_owned": True,
                "declaration_kind": "theorem",
                "is_unsafe": False,
                "is_transparent_definition": False,
                "is_opaque": True,
                "is_axiom": False,
                "value_has_sorry": False,
                "source_presented": True,
                "source_range": {
                    "line_start": 1,
                    "column_start": 0,
                    "line_end": 1,
                    "column_end": 1,
                },
                "owner_source_range": {
                    "line_start": 1,
                    "column_start": 0,
                    "line_end": 1,
                    "column_end": 1,
                },
                "type_display": "Fixture.claimSpec",
                "direct_dependencies": [],
                "axiom_closure_checked": False,
                "axiom_closure": [],
            }
        ]
        self.assertIsNotNone(self._parse(payload, semantic_contracts=(contract,)))
        for field in (
            "mode",
            "evidence_is_unsafe",
            "evidence_value_has_sorry",
            "evidence_axiom_closure_checked",
            "evidence_axiom_closure",
        ):
            malformed = copy.deepcopy(payload)
            del malformed["semantic_contracts"][0][field]  # type: ignore[index]
            self.assertIsNone(
                self._parse(malformed, semantic_contracts=(contract,)), field
            )

    def test_unrequested_or_duplicate_rows_fail_closed(self) -> None:
        payload = self._payload()
        duplicate = copy.deepcopy(payload)
        duplicate["proof_pairs"].append(  # type: ignore[union-attr]
            copy.deepcopy(duplicate["proof_pairs"][0])  # type: ignore[index]
        )
        self.assertIsNone(self._parse(duplicate))
        extra_field = copy.deepcopy(payload)
        extra_field["runtime_path"] = "/tmp/not-semantic-evidence"
        self.assertIsNone(self._parse(extra_field))

    def test_per_root_native_failure_is_typed_without_losing_response(self) -> None:
        payload = self._payload()
        payload["semantic_manifests"] = {
            "schema": "1",
            "items": [],
            "errors": [
                {"declaration": "Fixture.missing", "message": "unknown constant"}
            ],
        }
        self.assertIsNotNone(
            self._parse(payload, semantic_manifests=("Fixture.missing",))
        )
        self.assertIsNone(self._parse(payload, semantic_manifests=()))

    def test_semantic_signature_projection_retains_lean_semantic_identity(self) -> None:
        payload = self._payload()
        signature = {
            "schema": "2",
            "declaration_kind": "definition",
            "conclusion_mode": "type_and_value",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {"tag": "const", "name": "True"},
                    "display": "Prop := True",
                }
            ],
        }
        expected = manifest.signature_manifest_digest(signature)
        self.assertRegex(expected, r"^[0-9a-f]{64}$")
        payload["semantic_signatures"] = {
            "schema": "1",
            "items": [
                {"declaration": "Fixture.claimSpec", "signature": signature}
            ],
            "errors": [],
        }
        parsed = self._parse(
            payload, semantic_signatures=("Fixture.claimSpec",)
        )
        self.assertIsNotNone(parsed)
        assert parsed is not None
        self.assertEqual(
            parsed["semantic_signatures"]["items"][0][
                "elaborated_signature_sha256"
            ],
            expected,
        )
        self.assertEqual(
            manifest.semantic_signature_sha256s_from_inventory(
                parsed,
                expected_declarations={"Fixture.claimSpec"},
            ),
            {"Fixture.claimSpec": expected},
        )
        with self.assertRaisesRegex(
            ValueError,
            "differ from the selected review surface",
        ):
            manifest.semantic_signature_sha256s_from_inventory(
                parsed,
                expected_declarations={"Fixture.otherSpec"},
            )
        malformed = copy.deepcopy(payload)
        malformed["semantic_signatures"]["items"][0]["signature"][
            "untrusted_extra"
        ] = True
        malformed_parsed = self._parse(
            malformed, semantic_signatures=("Fixture.claimSpec",)
        )
        self.assertIsNotNone(malformed_parsed)
        assert malformed_parsed is not None
        self.assertEqual(malformed_parsed["semantic_signatures"]["items"], [])
        with self.assertRaisesRegex(ValueError, "incomplete semantic signatures"):
            manifest.semantic_signature_sha256s_from_inventory(
                malformed_parsed,
                expected_declarations={"Fixture.claimSpec"},
            )


    def test_semantic_signature_projection_bounds_large_root_definition(self) -> None:
        """A huge definition still has a Lean-derived signature identity."""

        payload = self._payload()
        signature = {
            "schema": "2",
            "declaration_kind": "definition",
            "conclusion_mode": "type_and_value",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {
                        "tag": "definition",
                        "body": "x" * (manifest.MAX_COMPACT_CANONICAL_BYTES + 1),
                    },
                    "display": "Prop := True",
                }
            ],
        }
        payload["semantic_signatures"] = {
            "schema": "1",
            "items": [
                {"declaration": "Fixture.claimSpec", "signature": signature}
            ],
            "errors": [],
        }

        parsed = self._parse(
            payload, semantic_signatures=("Fixture.claimSpec",)
        )
        self.assertIsNotNone(parsed)
        self.assertRegex(manifest.signature_manifest_digest(signature), r"^[0-9a-f]{64}$")

    def test_semantic_signature_projection_fails_closed_on_bad_or_extra_rows(self) -> None:
        payload = self._payload()
        payload["semantic_signatures"] = {
            "schema": "1",
            "items": [],
            "errors": [
                {"declaration": "Fixture.claimSpec", "message": "unknown declaration"}
            ],
        }
        self.assertIsNotNone(
            self._parse(payload, semantic_signatures=("Fixture.claimSpec",))
        )
        self.assertIsNone(self._parse(payload, semantic_signatures=()))

    def test_invalid_signature_payload_is_a_per_declaration_error(self) -> None:
        """One invalid auxiliary signature cannot erase a valid sibling row."""

        payload = self._payload()
        valid = {
            "schema": "2",
            "declaration_kind": "definition",
            "conclusion_mode": "type_and_value",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {"tag": "const", "name": "True"},
                    "display": "Prop := True",
                }
            ],
        }
        invalid = copy.deepcopy(valid)
        invalid["conclusion_mode"] = "type_only"
        payload["semantic_signatures"] = {
            "schema": "1",
            "items": [
                {"declaration": "Fixture.claimSpec", "signature": valid},
                {"declaration": "Fixture.helper", "signature": invalid},
            ],
            "errors": [],
        }

        parsed = self._parse(
            payload,
            semantic_signatures=("Fixture.claimSpec", "Fixture.helper"),
        )
        self.assertIsNotNone(parsed)
        assert parsed is not None
        section = parsed["semantic_signatures"]
        self.assertEqual(
            [row["declaration"] for row in section["items"]],
            ["Fixture.claimSpec"],
        )
        self.assertEqual(
            section["errors"],
            [
                {
                    "declaration": "Fixture.helper",
                    "message": "invalid semantic signature payload emitted by Lean",
                }
            ],
        )
        with self.assertRaisesRegex(ValueError, "incomplete semantic signatures"):
            manifest.semantic_signature_sha256s_from_inventory(parsed)

    def test_review_display_surface_projection_is_exact_and_fail_closed(self) -> None:
        payload = self._payload()
        payload["transparent_spec_displays"] = {
            "schema": "2",
            "items": [
                {
                    "specification": "Fixture.claimSpec",
                    "complete": True,
                    "expansion_count": "0",
                    "expanded_declarations": [],
                    "prerequisite_declarations": [],
                    "library_declarations": [],
                    "erased_proof_declarations": [],
                    "blocked_declarations": [],
                    "display": "True",
                }
            ],
        }
        surface = review_surface.semantic_review_display_surface_from_inventory(
            payload,
            expected_specifications={"Fixture.claimSpec"},
            expected_paper_declarations=(),
            expected_library_declarations=(),
        )
        self.assertEqual(set(surface.specifications), {"Fixture.claimSpec"})
        self.assertEqual(surface.specifications["Fixture.claimSpec"]["display"], "True")

        blocked = copy.deepcopy(payload)
        blocked["transparent_spec_displays"]["items"][0][
            "blocked_declarations"
        ] = ["Fixture.hidden"]
        with self.assertRaisesRegex(ValueError, "selected review surface"):
            review_surface.semantic_review_display_surface_from_inventory(
                blocked,
                expected_specifications={"Fixture.claimSpec"},
                expected_paper_declarations=(),
                expected_library_declarations=(),
            )

        malformed_empty = self._payload()
        malformed_empty["paper_prerequisite_displays"]["unexpected"] = True
        with self.assertRaisesRegex(ValueError, "malformed paper_prerequisite"):
            review_surface.semantic_review_display_surface_from_inventory(
                malformed_empty,
                expected_specifications=(),
                expected_paper_declarations=(),
                expected_library_declarations=(),
            )

    def test_claim_and_contract_projections_share_exact_inventory_readers(self) -> None:
        atom = {
            "ref": "result",
            "role": "conclusion",
            "canonical": {"tag": "const", "name": "True"},
            "display": "True",
        }
        claim = {
            "schema": "1",
            "signature": {
                "schema": str(manifest.MANIFEST_SCHEMA),
                "declaration_kind": "definition",
                "conclusion_mode": "type_and_value",
                "atoms": [atom],
            },
            "transparent_value_presentation_telescope": {
                "schema": manifest.TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_SCHEMA,
                "reduction": manifest.TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_REDUCTION,
                "atoms": [atom],
            },
        }
        inventory = {
            "semantic_review_claims": {
                "schema": "1",
                "items": [
                    {"declaration": "Fixture.claimSpec", "claim": claim}
                ],
                "errors": [],
            },
            "semantic_contracts": [
                {
                    "specification": "Fixture.claimSpec",
                    "evidence": "Fixture.claim",
                    "mode": "proves",
                    "matches": True,
                    "evidence_is_unsafe": False,
                    "evidence_value_has_sorry": False,
                    "evidence_axiom_closure_checked": True,
                    "evidence_axiom_closure": [],
                }
            ],
        }
        surfaces = manifest.semantic_review_claim_surfaces_from_inventory(
            inventory,
            expected_declarations={"Fixture.claimSpec"},
        )
        self.assertEqual(set(surfaces), {"Fixture.claimSpec"})
        self.assertEqual(
            [row["role"] for row in surfaces["Fixture.claimSpec"]["claim_atoms"]],
            ["conclusion"],
        )
        contract = ("Fixture.claimSpec", "Fixture.claim", "proves")
        rows = manifest.passing_semantic_contract_rows_from_inventory(
            inventory,
            expected_contracts={contract},
        )
        self.assertEqual(set(rows), {contract})

        failed_claim = copy.deepcopy(inventory)
        failed_claim["semantic_review_claims"]["errors"] = [
            {"declaration": "Fixture.other", "message": "unknown declaration"}
        ]
        with self.assertRaisesRegex(ValueError, "malformed review claims"):
            manifest.semantic_review_claim_surfaces_from_inventory(
                failed_claim,
                expected_declarations={"Fixture.claimSpec"},
            )

        unchecked = copy.deepcopy(inventory)
        unchecked["semantic_contracts"][0][
            "evidence_axiom_closure_checked"
        ] = False
        with self.assertRaisesRegex(ValueError, "selected typed routes"):
            manifest.passing_semantic_contract_rows_from_inventory(
                unchecked,
                expected_contracts={contract},
            )

        padded = copy.deepcopy(inventory)
        padded["semantic_contracts"][0]["evidence"] = " Fixture.claim"
        with self.assertRaisesRegex(ValueError, "selected typed routes"):
            manifest.passing_semantic_contract_rows_from_inventory(
                padded,
                expected_contracts={contract},
            )

    def test_spec_batch_caches_reached_library_rows_for_sibling_consumers(
        self,
    ) -> None:
        runtime_key = ("/repo", "Fixture.PaperInterface", ("digest", 1), ("graph", 1))
        payload = {
            "transparent_spec_displays": {
                "schema": "2",
                "items": [
                    {
                        "specification": "Fixture.claimSpec",
                        "display": "True",
                    }
                ],
            },
            "paper_prerequisite_displays": {"schema": "2", "items": []},
            "library_prerequisite_displays": {
                "schema": "3",
                "items": [
                    {
                        "declaration": "AppliedModelingLib.Shared.Model",
                        "direct_library_declarations": [],
                        "display": "Type",
                    }
                ],
            },
        }
        manifest._cache_declaration_inventory_displays(
            runtime_key, ("Fixture.PaperInterface",), payload
        )
        with mock.patch.object(
            manifest,
            "_declaration_inventory_runtime_cache_key",
            return_value=runtime_key,
        ):
            section = manifest._cached_declaration_display_section(
                Path("/repo"),
                "Fixture.PaperInterface",
                ["AppliedModelingLib.Shared.Model"],
                paper_modules=("Fixture.PaperInterface",),
                kind="library",
            )
        self.assertEqual(
            section,
            {
                "schema": "3",
                "items": [
                    {
                        "declaration": "AppliedModelingLib.Shared.Model",
                        "direct_library_declarations": [],
                        "display": "Type",
                    }
                ],
            },
        )

    def test_cached_paper_display_preserves_lean_discovered_closure(self) -> None:
        runtime_key = ("/repo", "Fixture.PaperInterface", ("digest", 1), ("graph", 1))
        paper_modules = ("Fixture.PaperInterface",)
        root = "Fixture.SourceModel"
        dependency = "Fixture.SourcePolicy"
        payload = {
            "transparent_spec_displays": {"schema": "2", "items": []},
            "paper_prerequisite_displays": {
                "schema": "2",
                "items": [
                    {
                        "declaration": root,
                        "direct_paper_declarations": [dependency],
                        "display": "Fixture.SourcePolicy",
                    },
                    {
                        "declaration": dependency,
                        "direct_paper_declarations": [],
                        "display": "Nat",
                    },
                ],
            },
            "library_prerequisite_displays": {"schema": "3", "items": []},
        }
        manifest._cache_declaration_inventory_displays(
            runtime_key, paper_modules, payload
        )
        self.addCleanup(manifest._DECLARATION_PAPER_DISPLAY_CACHE.clear)
        with mock.patch.object(
            manifest,
            "_declaration_inventory_runtime_cache_key",
            return_value=runtime_key,
        ):
            section = manifest._cached_declaration_display_section(
                Path("/repo"),
                "Fixture.PaperInterface",
                [root],
                paper_modules=paper_modules,
                kind="paper",
            )
        self.assertEqual(
            [row["declaration"] for row in section["items"]],
            [root, dependency],
        )

    def test_proof_pair_batch_is_reused_by_exact_compiled_context(self) -> None:
        runtime_key = (
            "/repo",
            "Fixture.ProofInterface",
            ("digest", 1),
            ("graph", 1),
        )
        pair = ("Fixture.claimSpec", "Fixture.claim")
        manifest._DECLARATION_PROOF_PAIR_CACHE.clear()
        self.addCleanup(manifest._DECLARATION_PROOF_PAIR_CACHE.clear)
        manifest._cache_declaration_inventory_proof_pairs(
            runtime_key,
            {
                "proof_pairs": [
                    {
                        "specification": pair[0],
                        "proof": pair[1],
                        "matches": True,
                    }
                ]
            },
        )
        with (
            mock.patch.object(
                manifest,
                "_declaration_inventory_runtime_cache_key",
                return_value=runtime_key,
            ),
            mock.patch.object(manifest, "run_lean_declaration_inventory") as native,
        ):
            result = manifest.run_lean_proposition_spec_proof_matches(
                Path("/repo"), "Fixture.ProofInterface", [pair]
            )
        self.assertEqual(result, {pair: True})
        native.assert_not_called()

    def test_manifest_api_uses_bounded_native_graph_requests_and_retains_successes(
        self,
    ) -> None:
        names = ["Fixture.first", "Fixture.missing", "Fixture.second"]
        context = {"schema": 3}
        graph_payload = {
            "semantic_manifests": {
                "schema": "1",
                "items": [
                    {"declaration": names[0], "manifest": {"sha256": "first"}},
                    {"declaration": names[2], "manifest": {"sha256": "second"}},
                ],
                "errors": [
                    {"declaration": names[1], "message": "unknown declaration"}
                ],
            }
        }
        checkpoints: list[dict[str, object]] = []
        manifest._CACHE.clear()
        self.addCleanup(manifest._CACHE.clear)
        with (
            mock.patch.object(
                manifest,
                "_signature_manifest_context_cache_coordinates",
                return_value=(
                    ("fixture-context", ()),
                    ("Fixture.PaperInterface",),
                    self.HASH_TOOL_IDENTITY,
                ),
            ),
            mock.patch.object(
                manifest,
                "run_lean_declaration_inventory",
                return_value=graph_payload,
            ) as native_graph,
            mock.patch.object(
                manifest,
                "_with_semantic_dependency_module_identities",
                side_effect=lambda _root, rows, timeout_seconds: rows,
            ),
        ):
            result = manifest.run_lean_signature_manifests(
                Path("/fixture"),
                "Fixture.PaperInterface",
                names,
                current_context=context,
                manifest_checkpoint=lambda _context, rows: checkpoints.append(
                    dict(rows)
                ),
            )

        self.assertEqual(set(result), {names[0], names[2]})
        self.assertEqual(
            set().union(*(set(rows) for rows in checkpoints)),
            {names[0], names[2]},
        )
        self.assertEqual(native_graph.call_count, 2)
        self.assertEqual(
            [
                call.kwargs["semantic_manifest_declaration_names"]
                for call in native_graph.call_args_list
            ],
            [names[:2], names[2:]],
        )
        self.assertTrue(
            all(
                not call.kwargs["require_build"]
                for call in native_graph.call_args_list
            )
        )

    def test_manifest_api_batches_large_surface_and_retains_later_successes(
        self,
    ) -> None:
        names = [f"Fixture.row{index:02d}" for index in range(18)]
        context = {"schema": 3}
        checkpoints: list[dict[str, object]] = []
        progress: list[dict[str, object]] = []

        def native_payload(*_args: object, **kwargs: object) -> dict[str, object]:
            requested = list(kwargs["semantic_manifest_declaration_names"])
            # Model one multi-root capacity failure. It must retry the two
            # valid roots independently instead of dropping their manifests.
            if requested == names[: manifest.SEMANTIC_MANIFEST_CHUNK_SIZE]:
                return {}
            return {
                "semantic_manifests": {
                    "schema": "1",
                    "items": [
                        {"declaration": name, "manifest": {"sha256": name}}
                        for name in requested
                    ],
                    "errors": [],
                }
            }

        manifest._CACHE.clear()
        self.addCleanup(manifest._CACHE.clear)
        with (
            mock.patch.object(
                manifest,
                "_signature_manifest_context_cache_coordinates",
                return_value=(
                    ("fixture-context", ()),
                    ("Fixture.PaperInterface",),
                    self.HASH_TOOL_IDENTITY,
                ),
            ),
            mock.patch.object(
                manifest,
                "run_lean_declaration_inventory",
                side_effect=native_payload,
            ) as native_graph,
            mock.patch.object(
                manifest,
                "_with_semantic_dependency_module_identities",
                side_effect=lambda _root, rows, timeout_seconds: rows,
            ),
        ):
            result = manifest.run_lean_signature_manifests(
                Path("/fixture"),
                "Fixture.PaperInterface",
                names,
                current_context=context,
                manifest_checkpoint=lambda _context, rows: checkpoints.append(
                    dict(rows)
                ),
                progress_callback=lambda event: progress.append(dict(event)),
            )

        self.assertEqual(set(result), set(names))
        self.assertEqual(native_graph.call_count, 11)
        requested_batches = [
            call.kwargs["semantic_manifest_declaration_names"]
            for call in native_graph.call_args_list
        ]
        self.assertEqual(
            [len(batch) for batch in requested_batches],
            [
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                1,
                1,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
                manifest.SEMANTIC_MANIFEST_CHUNK_SIZE,
            ],
        )
        self.assertEqual(len(checkpoints), 9)
        self.assertEqual(
            set().union(*(set(rows) for rows in checkpoints)), set(result)
        )
        self.assertEqual(
            [
                (event["batch_number"], event["status"], event["missing_count"])
                for event in progress
                if event["status"] == "finished"
            ],
            [
                (1, "finished", 0),
                (2, "finished", 0),
                (3, "finished", 0),
                (4, "finished", 0),
                (5, "finished", 0),
                (6, "finished", 0),
                (7, "finished", 0),
                (8, "finished", 0),
                (9, "finished", 0),
            ],
        )

    def test_manifest_api_reuses_current_context_for_narrower_request(self) -> None:
        names = ["Fixture.first", "Fixture.second"]
        context = {"schema": 3}
        graph_payload = {
            "semantic_manifests": {
                "schema": "1",
                "items": [
                    {"declaration": name, "manifest": {"sha256": name}}
                    for name in names
                ],
                "errors": [],
            }
        }
        manifest._CACHE.clear()
        self.addCleanup(manifest._CACHE.clear)
        with (
            mock.patch.object(
                manifest,
                "_signature_manifest_context_cache_coordinates",
                return_value=(
                    ("fixture-context", ()),
                    ("Fixture.PaperInterface",),
                    self.HASH_TOOL_IDENTITY,
                ),
            ),
            mock.patch.object(
                manifest,
                "run_lean_declaration_inventory",
                return_value=graph_payload,
            ) as native_graph,
            mock.patch.object(
                manifest,
                "_with_semantic_dependency_module_identities",
                side_effect=lambda _root, rows, timeout_seconds: rows,
            ),
        ):
            full = manifest.run_lean_signature_manifests(
                Path("/fixture"),
                "Fixture.PaperInterface",
                names,
                current_context=context,
            )
            narrow = manifest.run_lean_signature_manifests(
                Path("/fixture"),
                "Fixture.PaperInterface",
                [names[0]],
                current_context=context,
            )

        self.assertEqual(set(full), set(names))
        self.assertEqual(set(narrow), {names[0]})
        native_graph.assert_called_once()

    def test_revalidation_api_uses_one_native_graph_request(self) -> None:
        names = ["Fixture.first", "Fixture.second"]
        context = {"schema": 3}
        graph_payload = {
            "semantic_revalidations": {
                "schema": "1",
                "items": [
                    {"declaration": name, "receipt": {"schema": 1, "name": name}}
                    for name in names
                ],
                "errors": [],
            }
        }
        manifest._MANIFEST_REVALIDATION_RECEIPT_CACHE.clear()
        self.addCleanup(manifest._MANIFEST_REVALIDATION_RECEIPT_CACHE.clear)
        with (
            mock.patch.object(
                manifest,
                "_signature_manifest_context_cache_coordinates",
                return_value=(
                    ("fixture-revalidation-context", ()),
                    ("Fixture.PaperInterface",),
                    self.HASH_TOOL_IDENTITY,
                ),
            ),
            mock.patch.object(
                manifest,
                "run_lean_declaration_inventory",
                return_value=graph_payload,
            ) as native_graph,
        ):
            result = manifest.run_lean_signature_manifest_revalidations(
                Path("/fixture"),
                "Fixture.PaperInterface",
                names,
                current_context=context,
            )

        self.assertEqual(set(result), set(names))
        native_graph.assert_called_once()
        self.assertEqual(
            native_graph.call_args.kwargs["semantic_revalidation_declaration_names"],
            names,
        )


class LeanDeclarationInventorySubprocessDiagnosticTests(unittest.TestCase):
    """Pure subprocess regressions: no Lean, builds, or temporary file writes."""

    def setUp(self) -> None:
        stack = ExitStack()
        self.addCleanup(stack.close)
        self.process = mock.Mock(returncode=0)
        self.process.communicate.return_value = ("", "")
        registry = SimpleNamespace(module_roots=(), policy_id="fixture", sha256="a" * 64)
        for name, result in (
            ("load_foundation_registry", registry),
            ("_build_import_target", True),
            ("_build_compiled_audit_module", True),
            ("_declaration_inventory_runtime_cache_key", ("diagnostic-fixture",)),
            ("_cache_declaration_inventory_displays", None),
            ("_cache_declaration_inventory_proof_pairs", None),
        ):
            stack.enter_context(mock.patch.object(manifest, name, return_value=result))
        stack.enter_context(mock.patch.object(manifest, "_DECLARATION_INVENTORY_CACHE", {}))
        self.parse = stack.enter_context(mock.patch.object(
            manifest, "_parse_declaration_inventory_output", return_value=None
        ))
        self.terminate = stack.enter_context(mock.patch.object(
            manifest, "_terminate_semantic_contract_closure_process"
        ))
        self.launch = stack.enter_context(mock.patch.object(
            manifest.subprocess, "Popen", return_value=self.process
        ))
        temporary = stack.enter_context(mock.patch.object(manifest.tempfile, "TemporaryDirectory"))
        temporary.return_value.__enter__.return_value = "/tmp/not-created-inventory-fixture"
        stack.enter_context(mock.patch.object(Path, "write_text", return_value=0))

    def run_inventory(self) -> tuple[dict[str, object], str]:
        output = io.StringIO()
        with redirect_stderr(output):
            result = manifest.run_lean_declaration_inventory(
                Path("/fixture"), "Fixture.PaperInterface",
                inventory_modules=(), paper_modules=("Fixture.PaperInterface",),
                include_semantic_displays=False, include_axiom_closure=False,
                timeout_seconds=300,
            )
        self.launch.assert_called_once()
        return result, output.getvalue()

    def failure(self) -> dict[str, object]:
        result, output = self.run_inventory()
        self.assertEqual(result, {})
        prefix = "Lean declaration inventory failed: "
        self.assertTrue(output.startswith(prefix), output)
        diagnostic = json.loads(output[len(prefix):])
        self.assertEqual(diagnostic["timeout_seconds"], 300)
        self.assertRegex(diagnostic["request_sha256"], r"^[0-9a-f]{64}$")
        self.assertLessEqual(len(diagnostic["excerpt"]), 1200)
        return diagnostic

    def test_nonzero_exit_preserves_stdout_error_and_exit_code(self) -> None:
        self.process.returncode = 1
        self.process.communicate.return_value = (
            "Fixture.lean:3:1: error: fixture elaboration failed\n", ""
        )
        diagnostic = self.failure()
        self.assertEqual(diagnostic["reason"], "nonzero_exit")
        self.assertEqual(diagnostic["returncode"], 1)
        self.assertIn("fixture elaboration failed", diagnostic["excerpt"])
        self.process.communicate.assert_called_once_with(timeout=300)
        self.terminate.assert_not_called()

    def test_signal_without_output_is_not_silent(self) -> None:
        self.process.returncode = -9
        diagnostic = self.failure()
        self.assertEqual(diagnostic["returncode"], -9)
        self.assertEqual(diagnostic["stdout_chars"], 0)
        self.assertEqual(diagnostic["stderr_chars"], 0)
        self.assertEqual(diagnostic["excerpt"], "")

    def test_timeout_retains_partial_bytes_and_does_not_retry(self) -> None:
        self.process.communicate.side_effect = subprocess.TimeoutExpired(
            ["lean"], 300, output=b"partial output\xff", stderr=b"error: partial timeout diagnostic"
        )
        diagnostic = self.failure()
        self.assertEqual(diagnostic["reason"], "timeout")
        self.assertGreater(diagnostic["stdout_bytes"], 0)
        self.assertIn("partial timeout diagnostic", diagnostic["excerpt"])
        self.terminate.assert_called_once_with(self.process)
        self.process.communicate.assert_called_once_with(timeout=300)
        self.parse.assert_not_called()

    def test_startup_error_is_actionable_without_retry(self) -> None:
        self.launch.side_effect = FileNotFoundError("fixture executable unavailable")
        diagnostic = self.failure()
        self.assertEqual(diagnostic["reason"], "subprocess_error")
        self.assertIn("fixture executable unavailable", diagnostic["excerpt"])
        self.terminate.assert_not_called()
        self.parse.assert_not_called()

    def test_invalid_inventory_counts_records_without_dumping_payloads(self) -> None:
        self.process.communicate.return_value = (
            manifest.DECLARATION_INVENTORY_SENTINEL
            + '{"source":"PRIVATE_SOURCE_BODY' + "x" * 2_000_000 + '"}\n'
            + 'LEAN_ECONCSLIB_DECLARATION_INVENTORY_DIAGNOSTIC:{"message":"fixture native error"}\n',
            "",
        )
        with mock.patch.object(
            manifest, "bounded_lean_diagnostic_excerpt",
            wraps=manifest.bounded_lean_diagnostic_excerpt,
        ) as excerpt:
            diagnostic = self.failure()
        excerpt.assert_called_once()
        for value in excerpt.call_args.args:
            self.assertLessEqual(len(value), 4096)
            self.assertNotIn(manifest.DECLARATION_INVENTORY_SENTINEL, value)
            self.assertNotIn("PRIVATE_SOURCE_BODY", value)
        self.assertEqual(diagnostic["reason"], "invalid_or_missing_inventory")
        self.assertEqual(diagnostic["returncode"], 0)
        self.assertEqual(diagnostic["inventory_record_count"], 1)
        self.assertGreater(diagnostic["stdout_chars"], 20000)
        self.assertIn("fixture native error", diagnostic["excerpt"])
        self.assertNotIn("PRIVATE_SOURCE_BODY", json.dumps(diagnostic))

    def test_missing_inventory_and_long_output_have_bounded_diagnostics(self) -> None:
        self.process.communicate.return_value = ("error: " + "x" * 20000, "")
        with mock.patch.object(
            manifest, "bounded_lean_diagnostic_excerpt",
            wraps=manifest.bounded_lean_diagnostic_excerpt,
        ) as excerpt:
            diagnostic = self.failure()
        excerpt.assert_called_once()
        for value in excerpt.call_args.args:
            self.assertLessEqual(len(value), 4096)
        self.assertEqual(diagnostic["reason"], "invalid_or_missing_inventory")
        self.assertEqual(diagnostic["inventory_record_count"], 0)
        self.assertEqual(len(diagnostic["excerpt"]), 1200)

    def test_timeout_large_byte_inventory_is_filtered_before_excerpting(self) -> None:
        self.process.communicate.side_effect = subprocess.TimeoutExpired(
            ["lean"], 300,
            output=manifest.DECLARATION_INVENTORY_SENTINEL.encode("utf-8")
            + b'{"source":"PRIVATE_SOURCE_BODY' + b"x" * 2_000_000 + b'"}\n'
            + b"error: partial timeout diagnostic\xff\n",
        )
        with mock.patch.object(
            manifest, "bounded_lean_diagnostic_excerpt",
            wraps=manifest.bounded_lean_diagnostic_excerpt,
        ) as excerpt:
            diagnostic = self.failure()
        excerpt.assert_called_once()
        for value in excerpt.call_args.args:
            self.assertLessEqual(len(value), 4096)
            self.assertNotIn("PRIVATE_SOURCE_BODY", value)
        self.assertEqual(diagnostic["reason"], "timeout")
        self.assertEqual(diagnostic["inventory_record_count"], 1)
        self.assertGreater(diagnostic["stdout_bytes"], 2_000_000)
        self.assertIn("partial timeout diagnostic", diagnostic["excerpt"])
        self.terminate.assert_called_once_with(self.process)

    def test_success_preserves_payload_without_failure_output(self) -> None:
        self.parse.return_value = {"paper_prerequisite_displays": {"items": []}}
        result, output = self.run_inventory()
        self.assertEqual(result, self.parse.return_value)
        self.assertEqual(output, "")
        self.terminate.assert_not_called()


if __name__ == "__main__":
    unittest.main()
