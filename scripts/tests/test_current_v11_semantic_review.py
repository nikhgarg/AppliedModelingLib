from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts.current_closeout import semantic_review
from scripts.current_closeout.evidence_transaction import (
    build_current_v11_evidence_run_context,
)
from scripts.current_closeout.review_surface import V11LeanReviewSurface
from scripts.direct_semantic_review_binding import LEAN_TARGET_PROTOCOL, SOURCE_INPUT_PROTOCOL
from scripts.semantic_prerequisite_projection import (
    LIBRARY_SEMANTIC_REVIEW_SCHEMA,
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_SCHEMA,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
)
from scripts.source_review_input import (
    materialize_approved_review_contexts,
    source_semantic_input_bundle,
    statement_digest,
)
from scripts.v11_screening_contract import V11_SCREENING_PROMPT_VERSION


class CurrentV11SemanticReviewTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "Fixture"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self._write(
            self.paper / "status.json",
            {
                "status": "formalized",
                "review_surface": {
                    "require_source_spec_correspondence": True,
                },
            },
        )
        quote = "The source theorem."
        self._write(
            self.audit / "paper_statement_map.json",
            {
                "semantic_contract_schema": 3,
                "items": {
                    "source_theorem": {
                        "claim_bearing": True,
                        "source_kind": "theorem",
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
                        "semantic_contract": {
                            "spec_declaration": "Fixture.sourceTheoremSpec",
                            "evidence_declaration": "Fixture.sourceTheorem",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    }
                },
            },
        )
        self._write(
            self.audit / "v11_raw_source_spec_screening.json",
            {
                "schema": 3,
                "paper": "Fixture",
                "prompt_version": V11_SCREENING_PROMPT_VERSION,
                "validator": "reviewer",
                "validated_at": "2026-08-30",
                "items": {"Fixture.sourceTheoremSpec": {}},
            },
        )
        self._write(
            self.audit / "paper_semantic_prerequisites.json",
            {"schema": 1, "items": {}},
        )
        self._write(
            self.audit / "library_semantic_review.json",
            {"schema": 1, "items": {}},
        )

    @staticmethod
    def _write(path: Path, payload: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")

    def context(self):
        return build_current_v11_evidence_run_context(
            self.paper,
            repository_root=self.root,
        )

    def accepted_direct_fixture(
        self,
        *,
        direct_row_overrides: dict[str, object] | None = None,
        library_row_overrides: dict[str, object] | None = None,
        prerequisite_targets: dict[str, object] | None = None,
        approved_context: bool = False,
    ):
        """Build one exact transaction and its authenticated-reader projection."""

        source_path = self.paper / "source.txt"
        source_path.write_text("The source theorem.\n", encoding="utf-8")
        source_map = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        source_record = source_map["items"]["source_theorem"]
        if approved_context:
            source_record["accepted_additional_assumptions"] = {
                "approval_reference": "reader-test",
                "approved_at": "2026-09-06",
                "conditions": ["A reviewer-visible source convention."],
            }
            contexts, context_error = materialize_approved_review_contexts(
                source_record,
                source_proof_fidelity=None,
            )
            self.assertFalse(context_error)
            source_record["approved_review_context_schema"] = 1
            source_record["approved_review_contexts"] = contexts
            self._write(self.audit / "paper_statement_map.json", source_map)
        source_text, source_digest, source_error = source_semantic_input_bundle(
            source_record,
            require_context_roles=True,
        )
        self.assertFalse(source_error)
        _source_anchors, source_anchor_digest, anchor_error = (
            source_semantic_input_bundle(
                source_record,
                require_context_roles=True,
                include_approved_contexts=False,
            )
        )
        self.assertFalse(anchor_error)
        target_digest = hashlib.sha256(b"accepted direct target").hexdigest()
        signature_digest = hashlib.sha256(b"accepted signature").hexdigest()
        library_target_digest = hashlib.sha256(
            b"accepted library target"
        ).hexdigest()
        library_signature_digest = hashlib.sha256(
            b"accepted library signature"
        ).hexdigest()
        declaration = "Fixture.sourceTheoremSpec"
        library_declaration = "AppliedModelingLib.Fixture.Model"
        row = {
            "source_item": "source_theorem",
            "semantic_target_declaration": declaration,
            "source_input_protocol": SOURCE_INPUT_PROTOCOL,
            "source_input_bundle_sha256": source_digest,
            "paper_statement_sha256": statement_digest(source_text),
            "lean_target_protocol": LEAN_TARGET_PROTOCOL,
            "lean_expanded_statement_sha256": target_digest,
            "judgment": "matches",
            "reason": "The exact source and accepted Lean target agree.",
        }
        row.update(direct_row_overrides or {})
        direct_ledger = {
            "schema": 3,
            "paper": "Fixture",
            "prompt_version": V11_SCREENING_PROMPT_VERSION,
            "validator": "reader-test",
            "validated_at": "2026-09-06",
            "items": {declaration: row},
        }
        paper_ledger = {
            "schema": PAPER_PREREQUISITE_SCHEMA,
            "paper": "Fixture",
            "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
            "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
            "items": {},
        }
        library_items = {}
        if library_row_overrides is not None:
            library_row = {
                "source_item": "source_theorem",
                "source_input_bundle_sha256": source_digest,
                "source_anchor_bundle_sha256": source_anchor_digest,
                "library_declaration": library_declaration,
                "library_semantic_target_protocol": (
                    LIBRARY_SEMANTIC_TARGET_PROTOCOL
                ),
                "library_semantic_target_sha256": library_target_digest,
                "elaborated_signature_sha256": library_signature_digest,
                "judgment": "matches",
                "reason": "The source and reusable model agree.",
                "validator": "reader-test",
                "validator_type": "llm_as_judge",
                "validated_at": "2026-09-06",
            }
            library_row.update(library_row_overrides)
            library_items[library_declaration] = library_row
        library_ledger = {
            "schema": LIBRARY_SEMANTIC_REVIEW_SCHEMA,
            "paper": "Fixture",
            "prompt_version": (
                REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION
            ),
            "target_protocol": LIBRARY_SEMANTIC_TARGET_PROTOCOL,
            "items": library_items,
        }
        self._write(
            self.audit / "v11_raw_source_spec_screening.json", direct_ledger
        )
        self._write(
            self.audit / "paper_semantic_prerequisites.json", paper_ledger
        )
        self._write(
            self.audit / "library_semantic_review.json", library_ledger
        )
        context = self.context()
        accepted = SimpleNamespace(
            source_map=context.statement_map,
            direct_review_ledger=context.json_payload(
                context.canonical_sidecar_path(
                    "v11_raw_source_spec_screening.json"
                )
            ),
            paper_prerequisite_ledger=context.json_payload(
                context.canonical_sidecar_path(
                    "paper_semantic_prerequisites.json"
                )
            ),
            library_prerequisite_ledger=context.json_payload(
                context.canonical_sidecar_path("library_semantic_review.json")
            ),
            direct_target_identities_by_specification={
                declaration: {
                    "semantic_target_kind": "spec_proposition",
                    "reviewed_semantic_target_sha256": target_digest,
                    "elaborated_signature_sha256": signature_digest,
                }
            },
            prerequisite_target_identities_by_declaration=(
                prerequisite_targets
                if prerequisite_targets is not None
                else {
                    library_declaration: {
                        "semantic_target_kind": "semantic_prerequisite",
                        "reviewed_semantic_target_sha256": (
                            library_target_digest
                        ),
                        "elaborated_signature_sha256": (
                            library_signature_digest
                        ),
                    }
                    for _name in library_items
                }
            ),
        )
        expected = semantic_review.CurrentV11SemanticReviewResult(
            surface=V11LeanReviewSurface(
                semantic_targets={
                    declaration: {
                        "display_sha256": target_digest,
                        "lean_target_protocol": LEAN_TARGET_PROTOCOL,
                    }
                },
                paper_prerequisites=(),
                library_prerequisites=(
                    (
                        {
                            "source_item": "source_theorem",
                            "source_input_bundle_sha256": source_digest,
                            "source_anchor_bundle_sha256": source_anchor_digest,
                            "corrected_target_review_sha256": "",
                            "library_semantic_target_sha256": (
                                library_target_digest
                            ),
                            "elaborated_signature_sha256": (
                                library_signature_digest
                            ),
                            "semantic_judgment": "matches",
                            "semantic_current": True,
                        },
                    )
                    if library_items
                    else ()
                ),
                source_declarations={},
                library_source_declarations={},
                semantic_contracts={},
                declaration_inventory={},
                module_sources={},
                build_input_provider=object(),
            ),
            normalized_direct_items={declaration: row},
        )
        return context, accepted, expected

    @staticmethod
    def surface(*, library_judgment: str = "matches") -> V11LeanReviewSurface:
        return V11LeanReviewSurface(
            semantic_targets={"Fixture.sourceTheoremSpec": {}},
            paper_prerequisites=(
                {
                    "lean_name": "Fixture.Model",
                    "semantic_current": True,
                    "semantic_judgment": "matches",
                },
            ),
            library_prerequisites=(
                {
                    "lean_name": "AppliedModelingLib.Model",
                    "semantic_current": True,
                    "semantic_judgment": library_judgment,
                    "semantic_status": "current",
                },
            ),
            source_declarations={},
            library_source_declarations={},
            semantic_contracts={},
            declaration_inventory={},
            module_sources={},
            build_input_provider=object(),
        )

    def test_one_exact_result_is_cached_and_accepts_all_three_lanes(self) -> None:
        context = self.context()
        builder = mock.Mock(return_value=self.surface())
        binder = mock.Mock(return_value={"items": {}})
        with (
            mock.patch.object(
                semantic_review,
                "build_accepting_v11_review_surface",
                builder,
            ),
            mock.patch.object(
                semantic_review,
                "normalized_direct_screening_ledger",
                binder,
            ),
        ):
            first = semantic_review.current_v11_semantic_review_result(
                self.root,
                self.paper,
                context=context,
            )
            second = semantic_review.current_v11_semantic_review_result(
                self.root,
                self.paper,
                context=context,
            )

        self.assertIs(first, second)
        self.assertTrue(first.semantic_review_current)
        builder.assert_called_once()
        binder.assert_called_once()

    def test_checkpoint_only_verdict_never_uses_accepting_graph_builder(self) -> None:
        context = self.context()
        diagnostic_reader = mock.Mock(return_value=self.surface())
        binder = mock.Mock(return_value={"items": {}})
        with (
            mock.patch.object(
                semantic_review,
                "read_diagnostic_v11_review_surface",
                diagnostic_reader,
            ),
            mock.patch.object(
                semantic_review,
                "build_accepting_v11_review_surface",
                side_effect=AssertionError("accepting graph acquisition attempted"),
            ) as accepting_builder,
            mock.patch.object(
                semantic_review,
                "normalized_direct_screening_ledger",
                binder,
            ),
        ):
            result = semantic_review.current_v11_semantic_review_result(
                self.root,
                self.paper,
                context=context,
                require_graph_checkpoint=True,
            )

        self.assertTrue(result.semantic_review_current)
        diagnostic_reader.assert_called_once()
        accepting_builder.assert_not_called()
        binder.assert_called_once()

    @staticmethod
    def complete_result() -> semantic_review.CurrentV11SemanticReviewResult:
        def digest(label: str) -> str:
            return hashlib.sha256(label.encode()).hexdigest()

        targets = {
            name: {
                "display_sha256": digest(name + " target"),
                "review_claim_manifest_sha256": digest(name + " manifest"),
                "review_claim_atoms_sha256": digest(name + " atoms"),
                "lean_target_protocol": "lean-target-v1",
            }
            for name in ("Fixture.mainSpec", "Fixture.appendixSpec")
        }
        direct_items = {
            name: {
                "source_item": source_item,
                "source_input_protocol": "source-input-v1",
                "source_input_bundle_sha256": digest(source_item + " source"),
                "paper_statement_sha256": digest(source_item + " statement"),
                "lean_target_protocol": target["lean_target_protocol"],
                "lean_expanded_statement_sha256": target["display_sha256"],
                "review_claim_manifest_sha256": target[
                    "review_claim_manifest_sha256"
                ],
                "review_claim_atoms_sha256": target["review_claim_atoms_sha256"],
                "judgment": "matches",
                "corrected_target_review_sha256": "",
                "reason": "reviewer prose is outside document currentness",
                "validated_at": "2026-09-06T00:00:00Z",
            }
            for (name, source_item), target in zip(
                (
                    ("Fixture.mainSpec", "main"),
                    ("Fixture.appendixSpec", "appendix"),
                ),
                targets.values(),
                strict=True,
            )
        }
        surface = V11LeanReviewSurface(
            semantic_targets=targets,
            paper_prerequisites=(
                {
                    "source_item": "model",
                    "source_input_bundle_sha256": digest("model source"),
                    "source_anchor_bundle_sha256": digest("model anchors"),
                    "corrected_target_review_sha256": "",
                    "paper_semantic_target_sha256": digest("model target"),
                    "elaborated_signature_sha256": digest("model signature"),
                    "semantic_judgment": "matches",
                    "semantic_current": True,
                    "semantic_reason": "paper prerequisite prose",
                    "validated_at": "2026-09-06T00:00:00Z",
                },
            ),
            library_prerequisites=(
                {
                    "source_item": "expectation",
                    "source_input_bundle_sha256": digest("expectation source"),
                    "source_anchor_bundle_sha256": digest("expectation anchors"),
                    "corrected_target_review_sha256": digest("expectation correction"),
                    "library_semantic_target_sha256": digest("expectation target"),
                    "elaborated_signature_sha256": digest("expectation signature"),
                    "semantic_judgment": "matches_approved_corrected_target",
                    "semantic_current": True,
                    "semantic_reason": "library prerequisite prose",
                    "validated_at": "2026-09-06T00:00:00Z",
                },
            ),
            source_declarations={},
            library_source_declarations={},
            semantic_contracts={},
            declaration_inventory={},
            module_sources={},
            build_input_provider=object(),
        )
        return semantic_review.CurrentV11SemanticReviewResult(
            surface=surface,
            normalized_direct_items=direct_items,
        )

    def test_all_selected_material_includes_appendix_only_target_drift(self) -> None:
        result = self.complete_result()
        original = semantic_review.all_selected_semantic_review_material_sha256(
            result
        )
        changed_targets = {
            name: dict(target) for name, target in result.surface.semantic_targets.items()
        }
        changed_targets["Fixture.appendixSpec"]["display_sha256"] = "f" * 64
        changed_items = {
            name: dict(row) for name, row in result.normalized_direct_items.items()
        }
        changed_items["Fixture.appendixSpec"][
            "lean_expanded_statement_sha256"
        ] = "f" * 64
        changed = replace(
            result,
            surface=replace(result.surface, semantic_targets=changed_targets),
            normalized_direct_items=changed_items,
        )
        self.assertNotEqual(
            original,
            semantic_review.all_selected_semantic_review_material_sha256(changed),
        )

    def test_accepted_graph_material_matches_checkpoint_projection(self) -> None:
        context, accepted, expected = self.accepted_direct_fixture(
            library_row_overrides={}
        )
        with mock.patch(
            "scripts.obligation_closure_credential."
            "authenticated_current_accepted_graph_semantic_review_inputs",
            return_value=accepted,
        ):
            material = (
                semantic_review.accepted_graph_all_selected_semantic_review_material(
                    self.root,
                    self.paper,
                    context=context,
                )
            )
        self.assertEqual(
            material,
            semantic_review.all_selected_semantic_review_material(expected),
        )

    def test_accepted_graph_material_rejects_changed_correction_identity(self) -> None:
        context, accepted, _expected = self.accepted_direct_fixture(
            direct_row_overrides={"corrected_target_review_sha256": "f" * 64}
        )
        with mock.patch(
            "scripts.obligation_closure_credential."
            "authenticated_current_accepted_graph_semantic_review_inputs",
            return_value=accepted,
        ):
            with self.assertRaisesRegex(ValueError, "direct-review identity is stale"):
                semantic_review.accepted_graph_all_selected_semantic_review_material(
                    self.root,
                    self.paper,
                    context=context,
                )

    def test_accepted_graph_material_rejects_stray_direct_correction_fields(
        self,
    ) -> None:
        context, accepted, _expected = self.accepted_direct_fixture(
            direct_row_overrides={
                "corrected_target_protocol": "bogus-protocol",
                "corrected_target_sha256": "a" * 64,
            }
        )
        with mock.patch(
            "scripts.obligation_closure_credential."
            "authenticated_current_accepted_graph_semantic_review_inputs",
            return_value=accepted,
        ):
            with self.assertRaisesRegex(ValueError, "direct-review identity is stale"):
                semantic_review.accepted_graph_all_selected_semantic_review_material(
                    self.root,
                    self.paper,
                    context=context,
                )

    def test_accepted_graph_material_requires_prerequisite_reviewer_metadata(
        self,
    ) -> None:
        context, accepted, _expected = self.accepted_direct_fixture(
            library_row_overrides={"validator_type": ""}
        )
        with mock.patch(
            "scripts.obligation_closure_credential."
            "authenticated_current_accepted_graph_semantic_review_inputs",
            return_value=accepted,
        ):
            with self.assertRaisesRegex(
                ValueError,
                "accepted library prerequisite identity is stale",
            ):
                semantic_review.accepted_graph_all_selected_semantic_review_material(
                    self.root,
                    self.paper,
                    context=context,
                )

    def test_accepted_graph_material_preserves_approved_context_rebind(self) -> None:
        context, accepted, expected = self.accepted_direct_fixture(
            approved_context=True,
            library_row_overrides={},
        )
        library_declaration = "AppliedModelingLib.Fixture.Model"
        library_row = dict(
            accepted.library_prerequisite_ledger["items"][library_declaration]
        )
        anchor_digest = library_row["source_anchor_bundle_sha256"]
        self.assertNotEqual(
            anchor_digest,
            library_row["source_input_bundle_sha256"],
        )
        library_row["source_input_bundle_sha256"] = anchor_digest
        library_ledger = {
            **dict(accepted.library_prerequisite_ledger),
            "items": {library_declaration: library_row},
        }
        self._write(
            self.audit / "library_semantic_review.json",
            library_ledger,
        )
        context = self.context()
        accepted.library_prerequisite_ledger = context.json_payload(
            context.canonical_sidecar_path("library_semantic_review.json")
        )
        with mock.patch(
            "scripts.obligation_closure_credential."
            "authenticated_current_accepted_graph_semantic_review_inputs",
            return_value=accepted,
        ):
            material = (
                semantic_review.accepted_graph_all_selected_semantic_review_material(
                    self.root,
                    self.paper,
                    context=context,
                )
            )
        self.assertEqual(
            material,
            semantic_review.all_selected_semantic_review_material(expected),
        )

    def test_accepted_graph_material_uses_paper_prerequisite_binder(self) -> None:
        context, accepted, expected = self.accepted_direct_fixture(
            library_row_overrides={}
        )
        declaration = "AppliedModelingLib.Fixture.Model"
        library_row = dict(
            accepted.library_prerequisite_ledger["items"][declaration]
        )
        paper_row = dict(library_row)
        paper_row["paper_declaration"] = paper_row.pop("library_declaration")
        paper_row.pop("library_semantic_target_protocol")
        paper_row["paper_semantic_target_protocol"] = (
            PAPER_PREREQUISITE_TARGET_PROTOCOL
        )
        paper_row["paper_semantic_target_sha256"] = paper_row.pop(
            "library_semantic_target_sha256"
        )
        paper_ledger = {
            **dict(accepted.paper_prerequisite_ledger),
            "items": {declaration: paper_row},
        }
        library_ledger = {
            **dict(accepted.library_prerequisite_ledger),
            "items": {},
        }
        self._write(
            self.audit / "paper_semantic_prerequisites.json",
            paper_ledger,
        )
        self._write(
            self.audit / "library_semantic_review.json",
            library_ledger,
        )
        context = self.context()
        accepted.paper_prerequisite_ledger = context.json_payload(
            context.canonical_sidecar_path("paper_semantic_prerequisites.json")
        )
        accepted.library_prerequisite_ledger = context.json_payload(
            context.canonical_sidecar_path("library_semantic_review.json")
        )
        library_projected = dict(expected.surface.library_prerequisites[0])
        paper_projected = dict(library_projected)
        paper_projected["paper_semantic_target_sha256"] = paper_projected.pop(
            "library_semantic_target_sha256"
        )
        expected = replace(
            expected,
            surface=replace(
                expected.surface,
                paper_prerequisites=(paper_projected,),
                library_prerequisites=(),
            ),
        )
        with mock.patch(
            "scripts.obligation_closure_credential."
            "authenticated_current_accepted_graph_semantic_review_inputs",
            return_value=accepted,
        ):
            material = (
                semantic_review.accepted_graph_all_selected_semantic_review_material(
                    self.root,
                    self.paper,
                    context=context,
                )
            )
        self.assertEqual(
            material,
            semantic_review.all_selected_semantic_review_material(expected),
        )

    def test_accepted_graph_material_rejects_incomplete_prerequisites(self) -> None:
        context, accepted, _expected = self.accepted_direct_fixture(
            prerequisite_targets={
                "Fixture.MissingPrerequisite": {
                    "semantic_target_kind": "semantic_prerequisite",
                    "reviewed_semantic_target_sha256": "a" * 64,
                    "elaborated_signature_sha256": "b" * 64,
                }
            }
        )
        with mock.patch(
            "scripts.obligation_closure_credential."
            "authenticated_current_accepted_graph_semantic_review_inputs",
            return_value=accepted,
        ):
            with self.assertRaisesRegex(ValueError, "prerequisite inventory"):
                semantic_review.accepted_graph_all_selected_semantic_review_material(
                    self.root,
                    self.paper,
                    context=context,
                )

    def test_all_selected_material_excludes_review_prose_and_timestamps(self) -> None:
        result = self.complete_result()
        original = semantic_review.all_selected_semantic_review_material_sha256(
            result
        )
        changed_items = {
            name: {**row, "reason": "edited prose", "validated_at": "later"}
            for name, row in result.normalized_direct_items.items()
        }
        paper_rows = tuple(
            {**row, "semantic_reason": "edited prose", "validated_at": "later"}
            for row in result.surface.paper_prerequisites
        )
        library_rows = tuple(
            {**row, "semantic_reason": "edited prose", "validated_at": "later"}
            for row in result.surface.library_prerequisites
        )
        changed = replace(
            result,
            normalized_direct_items=changed_items,
            surface=replace(
                result.surface,
                paper_prerequisites=paper_rows,
                library_prerequisites=library_rows,
            ),
        )
        self.assertEqual(
            original,
            semantic_review.all_selected_semantic_review_material_sha256(changed),
        )

    def test_all_selected_material_excludes_claim_presentation_digests(self) -> None:
        result = self.complete_result()
        original = semantic_review.all_selected_semantic_review_material_sha256(
            result
        )
        changed_targets = {
            name: dict(target) for name, target in result.surface.semantic_targets.items()
        }
        changed_targets["Fixture.appendixSpec"][
            "review_claim_manifest_sha256"
        ] = "e" * 64
        changed_targets["Fixture.appendixSpec"][
            "review_claim_atoms_sha256"
        ] = "f" * 64
        changed = replace(
            result,
            surface=replace(result.surface, semantic_targets=changed_targets),
        )
        self.assertEqual(
            original,
            semantic_review.all_selected_semantic_review_material_sha256(changed),
        )

    def test_all_selected_material_binds_each_prerequisite_identity(self) -> None:
        cases = (
            ("paper", "source_input_bundle_sha256"),
            ("paper", "source_anchor_bundle_sha256"),
            ("paper", "paper_semantic_target_sha256"),
            ("paper", "elaborated_signature_sha256"),
            ("library", "source_input_bundle_sha256"),
            ("library", "source_anchor_bundle_sha256"),
            ("library", "library_semantic_target_sha256"),
            ("library", "elaborated_signature_sha256"),
            ("library", "corrected_target_review_sha256"),
        )
        for role, field in cases:
            with self.subTest(role=role, field=field):
                result = self.complete_result()
                original = (
                    semantic_review.all_selected_semantic_review_material_sha256(
                        result
                    )
                )
                paper_rows = [dict(row) for row in result.surface.paper_prerequisites]
                library_rows = [
                    dict(row) for row in result.surface.library_prerequisites
                ]
                rows = paper_rows if role == "paper" else library_rows
                rows[0][field] = "f" * 64
                changed = replace(
                    result,
                    surface=replace(
                        result.surface,
                        paper_prerequisites=tuple(paper_rows),
                        library_prerequisites=tuple(library_rows),
                    ),
                )
                self.assertNotEqual(
                    original,
                    semantic_review.all_selected_semantic_review_material_sha256(
                        changed
                    ),
                )

    def test_library_uncertainty_fails_the_complete_semantic_verdict(self) -> None:
        context = self.context()
        with (
            mock.patch.object(
                semantic_review,
                "build_accepting_v11_review_surface",
                return_value=self.surface(library_judgment="uncertain"),
            ),
            mock.patch.object(
                semantic_review,
                "normalized_direct_screening_ledger",
                return_value={"items": {}},
            ),
        ):
            result = semantic_review.current_v11_semantic_review_result(
                self.root,
                self.paper,
                context=context,
            )
            direct_findings = (
                semantic_review.current_v11_raw_source_spec_screening_findings(
                    self.root,
                    self.paper,
                    context=context,
                )
            )
            library_findings = (
                semantic_review.current_v11_material_library_semantic_review_findings(
                    self.root,
                    self.paper,
                    context=context,
                )
            )

        self.assertFalse(result.semantic_review_current)
        self.assertEqual(len(result.library_prerequisite_findings), 1)
        self.assertIn("uncertain", result.library_prerequisite_findings[0].message)
        self.assertEqual(direct_findings, [])
        self.assertEqual(library_findings, list(result.library_prerequisite_findings))

    def test_copied_context_cannot_reuse_the_issued_semantic_capability(self) -> None:
        context = replace(self.context())
        self.assertFalse(context.issued_by_builder)

        result = semantic_review.current_v11_semantic_review_result(
            self.root,
            self.paper,
            context=context,
        )

        self.assertFalse(result.semantic_review_current)
        self.assertIn("exact issued transaction", result.selection_error)
        self.assertTrue(
            semantic_review.current_v11_raw_source_spec_screening_findings(
                self.root,
                self.paper,
                context=context,
            )
        )
        self.assertTrue(
            semantic_review.current_v11_material_library_semantic_review_findings(
                self.root,
                self.paper,
                context=context,
            )
        )

    def test_repository_root_is_part_of_the_exact_runtime_binding(self) -> None:
        context = self.context()

        result = semantic_review.current_v11_semantic_review_result(
            self.root / "different-checkout",
            self.paper,
            context=context,
        )

        self.assertFalse(result.semantic_review_current)
        self.assertIn("canonical repository root", result.selection_error)

    def test_import_does_not_load_legacy_or_monolithic_evidence_modules(self) -> None:
        repository_root = Path(__file__).resolve().parents[2]
        command = """
import sys
from scripts.current_closeout import semantic_review
forbidden = {
    'scripts.audit_evidence_integrity',
    'scripts.legacy_source_record_authorities',
    'scripts.source_spec_protocol',
    'scripts.source_record_integrity',
    'scripts.source_record_semantic_reuse',
    'scripts.theorem_realization_transition',
}
loaded = sorted(forbidden.intersection(sys.modules))
if loaded:
    raise SystemExit('loaded historical modules: ' + ', '.join(loaded))
"""
        result = subprocess.run(
            [sys.executable, "-c", command],
            cwd=repository_root,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
