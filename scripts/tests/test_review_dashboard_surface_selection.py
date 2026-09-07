#!/usr/bin/env python3
"""Focused tests for review-surface-aware Lean elaboration."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import review_dashboard, review_dashboard_html


class ReviewDashboardSurfaceSelectionTests(unittest.TestCase):
    @staticmethod
    def _manifest(name: str) -> dict[str, object]:
        return {"sha256": f"manifest:{name}"}

    def test_statement_digest_candidates_include_exact_source_bytes(self) -> None:
        """A byte-pinned source-assumption receipt remains current verbatim."""

        source = "abbrev sourceCondition : Prop :=\n  True\n"
        candidates = review_dashboard.lean_statement_digest_candidates(source)
        self.assertIn(review_dashboard.statement_digest(source), candidates)
        self.assertIn(
            hashlib.sha256(source.encode("utf-8")).hexdigest(), candidates
        )

    def test_typed_dashboard_projects_prepared_cards_without_legacy_audits(
        self,
    ) -> None:
        """PDF/browser parity must not reconstruct parser-shaped audit rows."""

        source_text = "The source claim."
        lean_text = "def Fixture.claimSpec : Prop := True"
        row = {
            "name": "claimSpec",
            "full_name": "Fixture.claimSpec",
            "kind": "def",
            "verbatim_source_input": source_text,
            "paper_statement": source_text,
            "semantic_expanded_statement": lean_text,
            "lean_statement": lean_text,
            "source_input_bundle_sha256": "a" * 64,
            "semantic_expanded_statement_sha256": "b" * 64,
            "llm_match_lean_statement_sha256": "b" * 64,
            "llm_match_paper_statement_sha256": review_dashboard.statement_digest(
                source_text
            ),
            "llm_match_judgment": "matches",
            "llm_match_current": True,
            "human_claim_source_key": "claim",
            "source_item_key": "claim",
            "is_assumption": False,
            "approved_review_context_presentation": {
                "schema": 1,
                "summaries_by_id": {
                    "FIXTURE-CALENDAR-01": "Reader-facing calendar wording."
                },
                "presentation_sha256": "c" * 64,
            },
        }
        paper_prerequisite = {
            "lean_name": "Fixture.Model",
            "source_item": "model",
            "verbatim_source_input": "The model.",
            "semantic_judgment": "matches",
            "semantic_current": True,
        }
        library_prerequisite = {
            "lean_name": "AppliedModelingLib.Shared.Model",
            "source_item": "model",
            "verbatim_source_input": "The model.",
            "semantic_judgment": "matches",
            "semantic_current": True,
        }
        prepared = SimpleNamespace(
            claim_rows=((row, (), "Fixture.claim"),),
            claim_sections=(
                ("Main text", ((row, (), "Fixture.claim"),)),
            ),
            paper_prerequisites=(paper_prerequisite,),
            library_prerequisites=(library_prerequisite,),
            presentation_authority="accepted_graph",
            recorded_graph_projection=object(),
        )
        typed_map = {"semantic_contract_schema": 1, "items": {}}
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            with (
                mock.patch.object(
                    review_dashboard,
                    "paper_statement_map_payload",
                    return_value=typed_map,
                ),
                mock.patch(
                    "scripts.current_closeout.review_surface.prepared_review_surface",
                    return_value=prepared,
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_items_for_paper",
                    side_effect=AssertionError("typed browser parsed Lean rows"),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_filter_names",
                    side_effect=AssertionError(
                        "typed browser reapplied legacy claim selection"
                    ),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_auxiliary_names",
                    side_effect=AssertionError(
                        "typed browser reapplied legacy auxiliary selection"
                    ),
                ),
                mock.patch.object(
                    review_dashboard,
                    "statement_translation_audit_summary",
                    side_effect=AssertionError("typed browser replayed strict statements"),
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_coverage_audit_summary",
                    side_effect=AssertionError("typed browser replayed strict coverage"),
                ),
                mock.patch.object(
                    review_dashboard,
                    "assumption_provenance_audit_summary",
                    side_effect=AssertionError("typed browser replayed assumptions"),
                ),
            ):
                surface = review_dashboard._typed_prepared_dashboard_surface(
                    folder, None
                )

        self.assertIsNotNone(surface)
        assert surface is not None
        self.assertEqual(len(surface.all_claims), 1)
        self.assertEqual(
            surface.all_claims[0]["verbatim_source_input"], source_text
        )
        self.assertEqual(
            surface.all_claims[0]["semantic_expanded_statement"], lean_text
        )
        self.assertEqual(
            surface.all_claims[0]["approved_review_context_presentation"],
            row["approved_review_context_presentation"],
        )
        self.assertFalse(surface.statement_audit["needs_attention"])
        self.assertFalse(surface.paper_coverage_audit["needs_attention"])
        self.assertEqual(surface.paper_coverage_audit["inventory_count"], 2)

    def test_invalid_typed_surface_never_falls_back_to_legacy_parser(self) -> None:
        """A current-protocol presentation error must remain fail closed."""

        typed_map = {"semantic_contract_schema": 1, "items": {}}
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            with (
                mock.patch.object(
                    review_dashboard,
                    "paper_statement_map_payload",
                    return_value=typed_map,
                ),
                mock.patch(
                    "scripts.current_closeout.review_surface.prepared_review_surface",
                    side_effect=ValueError("invalid typed packet"),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_items_for_paper",
                    side_effect=AssertionError("fell back to legacy parser"),
                ),
            ):
                with self.assertRaisesRegex(ValueError, "invalid typed packet"):
                    review_dashboard._typed_prepared_dashboard_surface(folder, None)

    def test_quarantined_support_is_cached_but_not_a_human_row(self) -> None:
        """Defect evidence gets Lean credit without enlarging the claim surface."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FixturePaper"
            folder.mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["SourceSpec"],
                            "auxiliary_names": ["sourceCounterexample"],
                            "quarantined_auxiliary_names": [
                                "sourceCounterexample"
                            ],
                        }
                    }
                ),
                encoding="utf-8",
            )
            claim = review_dashboard.ReviewItem(
                name="SourceSpec",
                kind="def",
                lean_statement="def SourceSpec : Prop := True",
                paper_statement="source claim",
                agent_statement="source claim",
            )
            support = review_dashboard.ReviewItem(
                name="sourceCounterexample",
                kind="theorem",
                lean_statement="@FixturePaper.sourceCounterexample :\nFalse",
                paper_statement="",
                agent_statement="",
            )
            review_dashboard.QUARANTINED_SUPPORT_REVIEW_ITEM_CACHE[
                str(folder.resolve())
            ] = {support.name: support}

            self.assertEqual(
                review_dashboard.review_quarantined_auxiliary_names(folder),
                {"sourceCounterexample"},
            )
            self.assertEqual(
                [item.name for item in review_dashboard.apply_review_slices(
                    folder, [claim, support]
                )],
                ["SourceSpec"],
            )
            self.assertIs(
                review_dashboard.quarantined_support_review_items(folder)[
                    "sourceCounterexample"
                ],
                support,
            )

    def test_corrected_target_uses_exact_qualified_route_before_short_source_key(self) -> None:
        """A corrected endpoint must not fall back to its archival short-name key."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CorrectedPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace CorrectedPaper\n"
                "theorem corrected_endpoint : True := by trivial\n"
                "end CorrectedPaper\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {"review_surface": {"include_names": ["corrected_endpoint"]}}
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            archival = "The archival statement."
            corrected = "The approved corrected statement."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "corrected_endpoint": {
                                "statement": archival,
                                "coverage_status": "corrected_source_statement",
                                "lean_declarations": [
                                    "CorrectedPaper.corrected_endpoint"
                                ],
                                "corrected_target": {"schema": 1, "statement": corrected},
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )

            def check_rows(
                _paper_folder: Path,
                names: list[str],
                _timeout_seconds: int = review_dashboard.AGENT_PREVIEW_CHECK_TIMEOUT,
                source_file: Path | None = None,
            ) -> dict[str, str]:
                del source_file
                return {name: "True" for name in names}

            def manifest_rows(
                _root: Path,
                _import_module: str,
                names: list[str],
                timeout_seconds: int = 120,
                build_timeout_seconds: int = 600,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
                manifest_checkpoint: object | None = None,
            ) -> dict[str, dict[str, object]]:
                del timeout_seconds, build_timeout_seconds, manifest_checkpoint
                self.assertTrue(semantic_dependency_modules)
                self.assertIsNotNone(build_input_provider)
                return {name: self._manifest(name) for name in names}

            cache_key = str(folder.resolve())
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    side_effect=check_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    side_effect=manifest_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                items = review_dashboard.parse_interface_items(interface, None, folder)

            self.assertEqual(len(items), 1)
            self.assertEqual(items[0].paper_statement, corrected)
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

    def test_v11_screening_binds_only_current_source_and_expanded_spec(self) -> None:
        """The browser must show a v11 verdict only for the exact card inputs."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ScreenedPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text("def endpointSpec : Prop := True\n", encoding="utf-8")
            source_digest = "a" * 64
            source_input = "The exact byte-pinned source statement."
            paper_target_digest = review_dashboard.statement_digest(source_input)
            expanded_digest = "b" * 64
            interface_digest = hashlib.sha256(interface.read_bytes()).hexdigest()
            (audit / "v11_raw_source_spec_screening.json").write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.V11_RAW_SOURCE_SPEC_SCREENING_SCHEMA,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.V11_RAW_SOURCE_SPEC_SCREENING_PROMPT_VERSION,
                        "validator": "independent LLM",
                        "validated_at": "2026-08-18T00:00:00Z",
                        "items": {
                            "ScreenedPaper.endpointSpec": {
                                "judgment": "matches",
                                "reason": "Exact raw source and expanded Spec agree.",
                                "source_input_bundle_sha256": source_digest,
                                "paper_statement_sha256": paper_target_digest,
                                "lean_expanded_statement_sha256": expanded_digest,
                                "review_claim_manifest_sha256": "d" * 64,
                                "review_claim_atoms_sha256": "e" * 64,
                                "source_review_target_sha256": "f" * 64,
                                "paper_interface_sha256": interface_digest,
                                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                                "lean_target_protocol": review_dashboard.V11_RAW_SOURCE_SPEC_LEAN_TARGET_PROTOCOL,
                                "semantic_target_declaration": "ScreenedPaper.endpointSpec",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "endpoint": {
                                "statement": source_input,
                                "source_location": "source.txt:1",
                                "source_kind": "theorem",
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            rows = [
                {
                    "full_name": "ScreenedPaper.endpointSpec",
                    "human_claim_source_key": "endpoint",
                    "source_input_bundle_sha256": source_digest,
                    "verbatim_source_input": source_input,
                    "semantic_expanded_statement_sha256": expanded_digest,
                    "review_claim_manifest_sha256": "d" * 64,
                    "review_claim_atoms_sha256": "e" * 64,
                    "source_review_target_sha256": "f" * 64,
                }
            ]

            # An unrelated declaration changes the whole-file digest but not
            # the reviewed source bundle or the expanded Spec proposition.
            interface.write_text(
                "def endpointSpec : Prop := True\n"
                "theorem unrelatedSupport : True := by trivial\n",
                encoding="utf-8",
            )

            review_dashboard.bind_current_v11_source_spec_screening(folder, rows)

        self.assertEqual(rows[0]["llm_match_judgment"], "matches")
        self.assertFalse(rows[0]["llm_match_stale"])
        self.assertEqual(
            rows[0]["llm_match_source"], "v11_raw_source_spec_screening.json"
        )
        self.assertEqual(
            rows[0]["llm_match_source_routes"],
            [
                {
                    "source_item": "endpoint",
                    "source_statement_sha256": paper_target_digest,
                    "source_location": "source.txt:1",
                    "route_kind": "direct",
                }
            ],
        )

    def test_v11_screening_presentation_trace_is_not_semantic_identity(self) -> None:
        """Pretty-printer drift cannot reopen an unchanged canonical target."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ScreenedPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text("def endpointSpec : Prop := True\n", encoding="utf-8")
            source_input = "The exact byte-pinned source statement."
            source_digest = "a" * 64
            expanded_digest = "b" * 64
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "endpoint": {
                                "statement": source_input,
                                "source_location": "source.txt:1",
                                "source_kind": "theorem",
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            screening = {
                "schema": review_dashboard.V11_RAW_SOURCE_SPEC_SCREENING_SCHEMA,
                "paper": folder.name,
                "prompt_version": review_dashboard.V11_RAW_SOURCE_SPEC_SCREENING_PROMPT_VERSION,
                "validator": "independent LLM",
                "validated_at": "2026-08-18T00:00:00Z",
                "items": {
                    "ScreenedPaper.endpointSpec": {
                        "judgment": "matches",
                        "reason": "Exact raw source and expanded Spec agree.",
                        "source_input_bundle_sha256": source_digest,
                        "paper_statement_sha256": review_dashboard.statement_digest(
                            source_input
                        ),
                        "lean_expanded_statement_sha256": expanded_digest,
                        "review_claim_manifest_sha256": "d" * 64,
                        "review_claim_atoms_sha256": "e" * 64,
                        # Intentionally different from the current row's
                        # pretty-render hash, but still a valid trace.
                        "source_review_target_sha256": "1" * 64,
                        "paper_interface_sha256": hashlib.sha256(
                            interface.read_bytes()
                        ).hexdigest(),
                        "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                        "lean_target_protocol": review_dashboard.V11_RAW_SOURCE_SPEC_LEAN_TARGET_PROTOCOL,
                        "semantic_target_declaration": "ScreenedPaper.endpointSpec",
                    }
                },
            }
            screening_path = audit / "v11_raw_source_spec_screening.json"
            screening_path.write_text(json.dumps(screening), encoding="utf-8")

            def current_row() -> dict[str, object]:
                return {
                    "full_name": "ScreenedPaper.endpointSpec",
                    "human_claim_source_key": "endpoint",
                    "source_input_bundle_sha256": source_digest,
                    "verbatim_source_input": source_input,
                    "semantic_expanded_statement_sha256": expanded_digest,
                    "review_claim_manifest_sha256": "d" * 64,
                    "review_claim_atoms_sha256": "e" * 64,
                    "source_review_target_sha256": "f" * 64,
                }

            row = current_row()
            review_dashboard.bind_current_v11_source_spec_screening(folder, [row])
            self.assertEqual(row["llm_match_judgment"], "matches")
            self.assertFalse(row["llm_match_stale"])

            screening["items"]["ScreenedPaper.endpointSpec"][
                "source_review_target_sha256"
            ] = "not-a-digest"
            screening_path.write_text(json.dumps(screening), encoding="utf-8")
            invalid_row = current_row()
            review_dashboard.bind_current_v11_source_spec_screening(
                folder, [invalid_row]
            )
            self.assertNotIn("llm_match_judgment", invalid_row)

    def test_v11_screening_binds_current_approved_corrected_target(self) -> None:
        """A map-pinned corrected target is a positive, non-literal v11 match."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CorrectedPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text("def endpointSpec : Prop := True\n", encoding="utf-8")
            source_digest = "a" * 64
            expanded_digest = "b" * 64
            corrected_target_digest = "c" * 64
            interface_digest = hashlib.sha256(interface.read_bytes()).hexdigest()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "archival_endpoint": {
                                "coverage_status": "corrected_source_statement",
                                "corrected_target": {
                                    "archival_equivalence_claimed": False,
                                    "corrected_target_sha256": corrected_target_digest,
                                },
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "v11_raw_source_spec_screening.json").write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.V11_RAW_SOURCE_SPEC_SCREENING_SCHEMA,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.V11_RAW_SOURCE_SPEC_SCREENING_PROMPT_VERSION,
                        "validator": "independent LLM",
                        "validated_at": "2026-08-18T00:00:00Z",
                        "items": {
                            "CorrectedPaper.endpointSpec": {
                                "judgment": "matches_approved_corrected_target",
                                "reason": "The Spec matches the approved correction.",
                                "corrected_target_protocol": "approved_corrected_target_v1",
                                "corrected_target_sha256": corrected_target_digest,
                                "source_input_bundle_sha256": source_digest,
                                "paper_statement_sha256": source_digest,
                                "lean_expanded_statement_sha256": expanded_digest,
                                "review_claim_manifest_sha256": "d" * 64,
                                "review_claim_atoms_sha256": "e" * 64,
                                "source_review_target_sha256": "f" * 64,
                                "paper_interface_sha256": interface_digest,
                                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                                "lean_target_protocol": review_dashboard.V11_RAW_SOURCE_SPEC_LEAN_TARGET_PROTOCOL,
                                "semantic_target_declaration": "CorrectedPaper.endpointSpec",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            rows = [
                {
                    "full_name": "CorrectedPaper.endpointSpec",
                    "human_claim_source_key": "archival_endpoint",
                    "source_input_bundle_sha256": source_digest,
                    "semantic_expanded_statement_sha256": expanded_digest,
                    "review_claim_manifest_sha256": "d" * 64,
                    "review_claim_atoms_sha256": "e" * 64,
                    "source_review_target_sha256": "f" * 64,
                }
            ]

            review_dashboard.bind_current_v11_source_spec_screening(folder, rows)

        self.assertEqual(
            rows[0]["llm_match_judgment"],
            "matches_approved_corrected_target",
        )
        self.assertEqual(
            rows[0]["llm_match_resolution"], "approved_corrected_target"
        )
        self.assertFalse(rows[0]["llm_match_stale"])

    def test_review_slice_preserves_configured_proof_endpoint_module(self) -> None:
        """Separated proof endpoints must not silently fall back to PaperInterface."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SeparatedPaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "def claimSpec : Prop := True\n", encoding="utf-8"
            )
            (folder / "ProofInterface.lean").write_text(
                "theorem claim : True := trivial\n", encoding="utf-8"
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["claimSpec"],
                            "source_file": "PaperInterface.lean",
                            "proof_file": "ProofInterface.lean",
                            "proof_module": "SeparatedPaper.ProofInterface",
                        }
                    }
                ),
                encoding="utf-8",
            )

            source = review_dashboard.review_source_file(folder)
            payload = review_dashboard.load_review_slice_payload(folder)
            proof_module = review_dashboard.review_proof_module(folder, source)

        self.assertEqual(payload["proof_file"], "ProofInterface.lean")
        self.assertEqual(payload["proof_module"], "SeparatedPaper.ProofInterface")
        self.assertEqual(
            proof_module,
            "SeparatedPaper.ProofInterface",
        )

    def test_presentation_sections_must_preserve_source_dag_order(self) -> None:
        """Main/appendix headings cannot silently move a dependency card."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SectionedPaper"
            folder.mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "presentation_sections": [
                                {"title": "Main", "names": ["mainSpec"]},
                                {"title": "Appendix", "names": ["appendixSpec"]},
                            ]
                        }
                    }
                ),
                encoding="utf-8",
            )
            rows = [
                {"full_name": "SectionedPaper.mainSpec"},
                {"full_name": "SectionedPaper.appendixSpec"},
            ]
            self.assertEqual(
                review_dashboard.human_review_presentation_sections(folder, rows),
                [
                    {"title": "Main", "names": ["SectionedPaper.mainSpec"]},
                    {"title": "Appendix", "names": ["SectionedPaper.appendixSpec"]},
                ],
            )

    def test_presentation_sections_append_source_model_assumptions(self) -> None:
        """Assumptions use their own visible section, outside the Spec partition."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SectionedPaper"
            folder.mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "assumption_names": ["modelAssumption"],
                            "presentation_sections": [
                                {"title": "Main", "names": ["mainSpec"]},
                                {"title": "Appendix", "names": ["appendixSpec"]},
                            ],
                        }
                    }
                ),
                encoding="utf-8",
            )
            rows = [
                {"full_name": "SectionedPaper.mainSpec"},
                {"full_name": "SectionedPaper.appendixSpec"},
                {
                    "full_name": "SectionedPaper.modelAssumption",
                    "is_assumption": True,
                },
            ]
            self.assertEqual(
                review_dashboard.human_review_presentation_sections(folder, rows),
                [
                    {"title": "Main", "names": ["SectionedPaper.mainSpec"]},
                    {"title": "Appendix", "names": ["SectionedPaper.appendixSpec"]},
                    {
                        "title": "Source-model assumptions",
                        "kind": "source_model_assumptions",
                        "names": ["SectionedPaper.modelAssumption"],
                    },
                ],
            )

    def test_presentation_sections_still_reject_unmapped_nonassumption_card(self) -> None:
        """The automatic assumption section cannot hide an ordinary source card."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SectionedPaper"
            folder.mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "presentation_sections": [
                                {"title": "Main", "names": ["mainSpec"]}
                            ]
                        }
                    }
                ),
                encoding="utf-8",
            )
            rows = [
                {"full_name": "SectionedPaper.mainSpec"},
                {"full_name": "SectionedPaper.unmappedSpec"},
            ]
            with self.assertRaisesRegex(
                ValueError, "presentation sections must cover every source card"
            ):
                review_dashboard.human_review_presentation_sections(folder, rows)

    def test_repeated_corrected_presentation_is_not_readded_to_coverage(self) -> None:
        """A source alias inherits the canonical correction rather than a route."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "AliasPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            canonical = {
                "source_kind": "lemma",
                "source_location": "source.txt:1",
                "statement": "Corrected claim.",
                "coverage_status": "corrected_source_statement",
                "corrected_target": {"schema": 1, "statement": "Corrected claim."},
            }
            alias = {
                "source_kind": "lemma",
                "source_location": "source.txt:4",
                "statement": "Corrected claim.",
                "coverage_status": "corrected_source_statement",
                "corrected_target": {"schema": 1, "statement": "Corrected claim."},
                "source_presentation_alias": {
                    "schema": 1,
                    "canonical_source_item": "canonical",
                    "relation": "repeated_source_presentation",
                    "semantic_basis": "The later presentation repeats the same lemma.",
                    "validator": "independent source presentation review",
                    "validated_at": "2026-08-19T00:00:00Z",
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {"canonical": canonical, "alias": alias}}),
                encoding="utf-8",
            )

            _full, selected, _mode, error = review_dashboard.paper_coverage_inventory(
                folder
            )

        self.assertEqual(error, "")
        self.assertIn("canonical", selected)
        self.assertNotIn("alias", selected)

    def test_dashboard_labels_source_model_assumptions_separately(self) -> None:
        """The browser must not fold assumption cards into the source-claim count."""

        page = review_dashboard_html.HTML_PAGE
        self.assertIn("function reviewSurfaceCounts(paper)", page)
        self.assertIn(
            'presentationSectionKind(section) === "source_model_assumptions"',
            page,
        )
        self.assertIn("reviewCards: sourceClaims + sourceModelAssumptions", page)
        self.assertIn("source-model assumption", page)
        self.assertIn("presentationSectionItemNoun(section)", page)
        self.assertNotIn(
            "`0/${visibleItems.length} reviewed; ${visibleItems.length} source claims`",
            page,
        )

    def test_v11_include_order_is_the_explicit_claim_reading_order_without_intake(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OrderedPaper"
            folder.mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["definitionSpec", "theoremSpec"]
                        }
                    }
                ),
                encoding="utf-8",
            )
            self.assertEqual(
                review_dashboard._human_review_intake_order(folder),
                {"definitionSpec": 1, "theoremSpec": 2},
            )

    def test_dashboard_keeps_verbatim_source_out_of_mathjax(self) -> None:
        """Raw TeX environments are source evidence, not MathJax input."""

        self.assertIn("function renderVerbatimSourceInput", review_dashboard_html.HTML_PAGE)
        self.assertIn('ignoreHtmlClass: "verbatim-source-input"', review_dashboard_html.HTML_PAGE)
        self.assertIn('class="verbatim-source-input"', review_dashboard_html.HTML_PAGE)
        self.assertIn(
            "const paperHtml = renderVerbatimSourceInput(item.paper_statement);",
            review_dashboard_html.HTML_PAGE,
        )
        self.assertNotIn("statement-preview", review_dashboard_html.HTML_PAGE)
        self.assertNotIn("compactPreview", review_dashboard_html.HTML_PAGE)
        self.assertNotIn("function renderPaperStatement", review_dashboard_html.HTML_PAGE)

    def test_dashboard_contents_are_linked_without_misleading_nested_numbers(self) -> None:
        """The on-page outline uses linked bullets for prerequisite and claim cards."""

        self.assertIn("function makeReviewContents", review_dashboard_html.HTML_PAGE)
        self.assertIn('const list = document.createElement("ul");', review_dashboard_html.HTML_PAGE)
        self.assertIn("link.dataset.reviewAnchor = id;", review_dashboard_html.HTML_PAGE)

    def test_library_prerequisite_review_uses_a_separate_explicit_scope(self) -> None:
        """Prerequisite annotations stay distinct from paper-claim review rows."""

        with tempfile.TemporaryDirectory() as temp_dir:
            log = Path(temp_dir) / "library_prerequisite_validations.jsonl"
            entry = review_dashboard.append_review(
                log,
                {
                    "paper": "FixturePaper",
                    "theorem": "AppliedModelingLib.Fixture.Model",
                    "prerequisite_key": "FixturePaper::library_prerequisite::AppliedModelingLib.Fixture.Model",
                    "review_scope": "library_prerequisite",
                    "user": "reviewer",
                    "judgment": "matches",
                    "notes": "The source model connection is correct.",
                    "lean_statement": "def Model := True",
                    "paper_statement": "The model is true.",
                    "agent_statement": "",
                    "source_status": "byte-pinned prerequisite source connection",
                    "source_note": "source/main.tex:1",
                },
                "default",
            )

        self.assertEqual(entry["review_scope"], "library_prerequisite")
        self.assertEqual(
            entry["prerequisite_key"],
            "FixturePaper::library_prerequisite::AppliedModelingLib.Fixture.Model",
        )

    def test_browser_card_omits_recursive_lean_manifest(self) -> None:
        """The live dashboard must not ship server-side audit graphs to a browser."""

        projected = review_dashboard.browser_review_item(
            {
                "name": "claimSpec",
                "paper_statement": "A source claim.",
                "lean_signature_manifest": {"recursive_graph": ["large"]},
            }
        )

        self.assertEqual(projected["name"], "claimSpec")
        self.assertNotIn("lean_signature_manifest", projected)

    def test_parser_keeps_the_full_theorem_type_after_an_inner_let_assignment(self) -> None:
        """An inner `let :=` must not truncate the declaration reuse binding."""

        with tempfile.TemporaryDirectory() as temp_dir:
            interface = Path(temp_dir) / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture\n"
                "theorem endpoint (x : Nat) :\n"
                "    (let rho : Nat := x; rho = x) ∧ True := by\n"
                "  simp\n"
                "theorem unparenthesized :\n"
                "    let rho : Nat := 0; rho = 0 ∧ True := by\n"
                "  simp\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            parsed = review_dashboard.parse_review_source_declarations(interface)

        endpoint = next(row for row in parsed if row[1] == "endpoint")
        self.assertIn("let rho : Nat := x; rho = x", endpoint[3])
        self.assertIn("∧ True", endpoint[3])
        self.assertNotIn(":= by", endpoint[3])
        unparenthesized = next(row for row in parsed if row[1] == "unparenthesized")
        self.assertIn("let rho : Nat := 0; rho = 0 ∧ True", unparenthesized[3])
        self.assertNotIn(":= by", unparenthesized[3])

    def test_parser_recognizes_outer_assignment_after_multiline_layout_let(self) -> None:
        """A layout `let` in a theorem type must not consume later declarations."""

        with tempfile.TemporaryDirectory() as temp_dir:
            interface = Path(temp_dir) / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture\n"
                "theorem layout_let :\n"
                "    let rho : Nat := 0\n"
                "    rho = 0 ∧ True := by\n"
                "  simp\n"
                "abbrev followingSpec : Prop := True\n"
                "theorem following : followingSpec := by trivial\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            parsed = review_dashboard.parse_review_source_declarations(interface)

        layout_let = next(row for row in parsed if row[1] == "layout_let")
        self.assertIn("let rho : Nat := 0", layout_let[3])
        self.assertIn("rho = 0 ∧ True", layout_let[3])
        self.assertNotIn(":= by", layout_let[3])
        self.assertEqual(
            [row[1] for row in parsed],
            ["layout_let", "followingSpec", "following"],
        )

    def test_parser_keeps_exact_instance_definition_source(self) -> None:
        """Instances receive the same exact source treatment as definitions."""

        with tempfile.TemporaryDirectory() as temp_dir:
            interface = Path(temp_dir) / "Model.lean"
            interface.write_text(
                "namespace Fixture\n"
                "noncomputable instance observedDecidableEq (α : Type) "
                "[DecidableEq α] : DecidableEq α := by\n"
                "  exact inferInstance\n"
                "def following : Nat := 1\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            parsed = review_dashboard.parse_review_source_declarations(interface)

        instance = next(row for row in parsed if row[1] == "observedDecidableEq")
        self.assertEqual(instance[0], "instance")
        self.assertIn("exact inferInstance", instance[3])
        self.assertEqual([row[1] for row in parsed], ["observedDecidableEq", "following"])

    def test_direct_map_route_rebinds_stale_cache_statement_without_lean_work(self) -> None:
        """A current explicit route repairs an old comment-backed cache row."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CacheInvariantPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace CacheInvariantPaper\n"
                "/-- Obsolete dashboard comment. -/\n"
                "theorem endpoint : True := by trivial\n"
                "end CacheInvariantPaper\n",
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            source_statement = "The source's displayed endpoint has the exact stated form."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_formula": {
                                "statement": source_statement,
                                "source_kind": "formula",
                                "claim_bearing": False,
                                "lean_declarations": [
                                    "CacheInvariantPaper.endpoint"
                                ],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            parsed = review_dashboard.parse_review_source_declarations(interface)
            kind, name, full_name, raw_signature, *_rest = next(
                row for row in parsed if row[1] == "endpoint"
            )
            stale = review_dashboard.ReviewItem(
                name=name,
                kind=kind,
                lean_statement=raw_signature,
                paper_statement="Obsolete dashboard comment.",
                agent_statement="An old draft.",
                full_name=full_name,
                interface_source=raw_signature,
            )
            hashes = {
                "review_source_file": "PaperInterface.lean",
                "interface_sha256": "unchanged-interface",
                "lean_source_closure_sha256": "unchanged-lean-closure",
                "report_sha256": "",
                "tex_sha256": "",
                "text_sha256": "",
                "pdf_sha256": "",
                "paper_statement_map_sha256": "unchanged-map",
                "review_surface_static_sha256": "",
                "review_surface_display_sha256": "",
                "review_surface_rebind_sha256": "",
            }
            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache_path.parent.mkdir()
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": hashes,
                        "rows": [stale.__dict__],
                    }
                ),
                encoding="utf-8",
            )

            with mock.patch.object(
                review_dashboard,
                "run_lean_signature_manifests",
            ) as manifests:
                rows = review_dashboard.load_cached_review_rows(
                    folder,
                    source_hashes=hashes,
                )

            manifests.assert_not_called()
            self.assertIsNotNone(rows)
            assert rows is not None
            self.assertEqual(rows[0].paper_statement, source_statement)
            persisted = json.loads(cache_path.read_text(encoding="utf-8"))
            self.assertEqual(persisted["rows"][0]["paper_statement"], source_statement)

    def test_include_surface_limits_lean_batches_by_full_declaration_name(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FilteredPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                """
namespace First
theorem duplicate : True := by trivial
end First

theorem kept : True := by trivial
theorem auxiliary : True := by trivial
theorem omitted : True := by trivial

namespace Second
theorem duplicate : True := by trivial
end Second
""",
                encoding="utf-8",
            )
            (folder / "Assumptions.lean").write_text(
                "axiom sourcePremise : Prop\n", encoding="utf-8"
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": [
                                "duplicate",
                                "kept",
                                "auxiliary",
                            ],
                            "assumption_names": ["sourcePremise"],
                            "auxiliary_names": ["auxiliary"],
                        }
                    }
                ),
                encoding="utf-8",
            )

            check_batches: dict[str, list[str]] = {}
            manifest_batches: dict[str, list[str]] = {}

            def check_rows(
                _paper_folder: Path,
                names: list[str],
                _timeout_seconds: int = review_dashboard.AGENT_PREVIEW_CHECK_TIMEOUT,
                source_file: Path | None = None,
            ) -> dict[str, str]:
                self.assertIsNotNone(source_file)
                check_batches[(source_file or Path()).name] = list(names)
                return {name: "True" for name in names}

            def manifest_rows(
                _root: Path,
                import_module: str,
                names: list[str],
                timeout_seconds: int = 120,
                build_timeout_seconds: int = 600,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
                manifest_checkpoint: object | None = None,
            ) -> dict[str, dict[str, object]]:
                del timeout_seconds, build_timeout_seconds, manifest_checkpoint
                self.assertIn(import_module, semantic_dependency_modules or ())
                self.assertIsNotNone(build_input_provider)
                manifest_batches[import_module.rsplit(".", 1)[-1] + ".lean"] = list(
                    names
                )
                return {name: self._manifest(name) for name in names}

            cache_key = str(folder.resolve())
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)
            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    side_effect=check_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    side_effect=manifest_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                items = review_dashboard.parse_interface_items(
                    interface, None, folder
                )

            expected_interface = {
                "First.duplicate",
                "Second.duplicate",
                "kept",
            }
            self.assertEqual(
                set(check_batches["PaperInterface.lean"]), expected_interface
            )
            self.assertEqual(
                set(manifest_batches["PaperInterface.lean"]), expected_interface
            )
            self.assertEqual(
                check_batches["Assumptions.lean"], ["sourcePremise"]
            )
            self.assertEqual(
                manifest_batches["Assumptions.lean"], ["sourcePremise"]
            )
            self.assertEqual(
                Counter(item.name for item in items),
                Counter({"duplicate": 2, "kept": 1, "sourcePremise": 1}),
            )
            source_premise = next(
                item for item in items if item.name == "sourcePremise"
            )
            self.assertTrue(source_premise.is_assumption)

            manifests = review_dashboard.SIGNATURE_MANIFEST_CACHE[cache_key]
            self.assertIn("First.duplicate", manifests)
            self.assertIn("Second.duplicate", manifests)
            self.assertNotIn("duplicate", manifests)
            self.assertEqual(manifests["kept"]["sha256"], "manifest:kept")
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

    def test_missing_include_names_keeps_all_declarations_in_lean_batch(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "UnfilteredPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                """
theorem kept : True := by trivial
theorem auxiliary : True := by trivial
theorem omitted : True := by trivial
""",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "assumption_names": [],
                            "auxiliary_names": ["auxiliary"],
                        }
                    }
                ),
                encoding="utf-8",
            )

            check_batches: list[list[str]] = []
            manifest_batches: list[list[str]] = []

            def check_rows(
                _paper_folder: Path,
                names: list[str],
                _timeout_seconds: int = review_dashboard.AGENT_PREVIEW_CHECK_TIMEOUT,
                source_file: Path | None = None,
            ) -> dict[str, str]:
                del source_file
                check_batches.append(list(names))
                return {name: "True" for name in names}

            def manifest_rows(
                _root: Path,
                _import_module: str,
                names: list[str],
                timeout_seconds: int = 120,
                build_timeout_seconds: int = 600,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
                manifest_checkpoint: object | None = None,
            ) -> dict[str, dict[str, object]]:
                del timeout_seconds, build_timeout_seconds, manifest_checkpoint
                self.assertTrue(semantic_dependency_modules)
                self.assertIsNotNone(build_input_provider)
                manifest_batches.append(list(names))
                return {name: self._manifest(name) for name in names}

            cache_key = str(folder.resolve())
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)
            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    side_effect=check_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    side_effect=manifest_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                items = review_dashboard.parse_interface_items(
                    interface, None, folder
                )

            expected_batch = ["kept", "auxiliary", "omitted"]
            self.assertEqual(check_batches, [expected_batch])
            self.assertEqual(manifest_batches, [expected_batch])
            self.assertEqual([item.name for item in items], ["kept", "omitted"])
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

    def test_manifest_only_extraction_skips_separate_check_preview_process(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ManifestOnlyPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            source = "theorem reviewed : True := by trivial\n"
            interface.write_text(source, encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {"review_surface": {"include_names": ["reviewed"]}}
                ),
                encoding="utf-8",
            )

            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                ) as previews,
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    return_value={"reviewed": self._manifest("reviewed")},
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                rows = review_dashboard.parse_interface_items(
                    interface,
                    None,
                    folder,
                    render_lean_previews=False,
                )

            previews.assert_not_called()
            self.assertEqual(len(rows), 1)
            expected_statement = source.split(":=", 1)[0].strip()
            self.assertEqual(rows[0].interface_source, expected_statement)
            self.assertEqual(rows[0].lean_statement, expected_statement)
            self.assertEqual(rows[0].lean_signature_sha256, "manifest:reviewed")

    def test_external_support_only_definition_does_not_require_redundant_review_row(self) -> None:
        item = {
            "source_kind": "definition",
            "source_status": "support_only",
            "support_lean_declarations": ["Example.Model.isOptimal"],
            "lean_declarations": [],
            "source_note": "Direct source definition retained as support, not a theorem conclusion.",
        }

        self.assertFalse(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_definition", item
            )
        )

        item["source_status"] = ""
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_definition", item
            )
        )

    def test_owned_build_input_transaction_rejects_mutation_before_rows_escape(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "MutationPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "theorem reviewed : True := by trivial\n",
                encoding="utf-8",
            )
            provider = mock.Mock()
            provider.finalize_unchanged.return_value = False
            with (
                mock.patch.object(
                    review_dashboard,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    return_value=("MutationPaper.PaperInterface",),
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    return_value={"reviewed": self._manifest("reviewed")},
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    return_value={"reviewed": "True"},
                ),
            ):
                with self.assertRaisesRegex(
                    RuntimeError,
                    "repository build inputs changed",
                ):
                    review_dashboard.parse_interface_items(
                        interface,
                        None,
                        folder,
                    )

            provider.finalize_unchanged.assert_called_once_with()

    def test_explanatory_support_only_remark_needs_explicit_non_target_reason(self) -> None:
        item = {
            "source_kind": "remark",
            "source_status": "support_only",
            "support_lean_declarations": ["Example.counterexample"],
            "lean_declarations": [],
            "source_note": (
                "This post-theorem explanatory prose is not a standalone formal "
                "claim, named result, or theorem premise."
            ),
        }
        self.assertFalse(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_explanatory_remark", item
            )
        )

        item["source_note"] = "Post-theorem prose retained for context."
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_explanatory_remark", item
            )
        )

    def test_formula_status_prose_cannot_create_a_model_route(self) -> None:
        """Only a source model/assumption presentation may use a model route."""

        statement = "The likelihood has the displayed domain."
        source_item = {
            "source_kind": "formula",
            "statement": statement,
            "source_location": "source.tex:10-12",
            "source_status": (
                "global-max scope is conditional on an explicit domain convention"
            ),
        }
        row = review_dashboard.ReviewItem(
            name="formula_row",
            kind="theorem",
            lean_statement="True",
            paper_statement=statement,
            agent_statement=statement,
            llm_match_source_routes=[
                {
                    "source_item": "source_formula",
                    "source_statement_sha256": review_dashboard.statement_digest(
                        statement
                    ),
                    "source_location": "source.tex:10-12",
                    "route_kind": "direct",
                }
            ],
        )

        self.assertFalse(
            review_dashboard.source_item_effective_route_policy(source_item)[
                "is_model_convention"
            ]
        )
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
            "",
        )

        source_item["model_convention_ids"] = ["FIXTURE-MODEL-CONVENTION-1"]
        row.llm_match_source_routes[0]["route_kind"] = "source_model_convention"  # type: ignore[index]
        self.assertFalse(
            review_dashboard.source_item_effective_route_policy(source_item)[
                "is_model_convention"
            ]
        )
        self.assertIn(
            "not one of `direct`, `source_component`",
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
        )
        row.llm_match_source_routes[0]["route_kind"] = "direct"  # type: ignore[index]
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
            "",
        )

        source_item["source_kind"] = "model"
        row.llm_match_source_routes[0]["route_kind"] = "source_model_convention"  # type: ignore[index]
        self.assertTrue(
            review_dashboard.source_item_effective_route_policy(source_item)[
                "is_model_convention"
            ]
        )
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
            "",
        )

    def test_signature_contexts_accept_mixed_relative_and_absolute_source_paths(self) -> None:
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp_dir:
            absolute_folder = Path(temp_dir) / "MixedPathsPaper"
            absolute_folder.mkdir()
            folder = absolute_folder.relative_to(Path.cwd())
            (absolute_folder / "PaperInterface.lean").write_text(
                "theorem reviewed : True := by trivial\n", encoding="utf-8"
            )
            (absolute_folder / "Assumptions.lean").write_text(
                "axiom sourcePremise : Prop\n", encoding="utf-8"
            )
            (absolute_folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "source_file": (
                                f"{folder.as_posix()}/PaperInterface.lean"
                            ),
                            "assumption_source_file": (
                                f"{folder.as_posix()}/Assumptions.lean"
                            ),
                            "assumption_names": ["sourcePremise"],
                        }
                    }
                ),
                encoding="utf-8",
            )

            modules: list[str] = []

            def signature_context(
                _root: Path,
                module: str,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
            ) -> dict[str, object]:
                self.assertEqual(semantic_dependency_modules, (module,))
                self.assertIsNotNone(build_input_provider)
                modules.append(module)
                return {"import_module": module}

            with (
                mock.patch.object(
                    review_dashboard,
                    "signature_manifest_cache_context",
                    side_effect=signature_context,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                contexts = review_dashboard.current_review_signature_contexts(folder)

            self.assertEqual(
                contexts,
                {
                    "Assumptions.lean": {
                        "import_module": "MixedPathsPaper.Assumptions"
                    },
                    "PaperInterface.lean": {
                        "import_module": "MixedPathsPaper.PaperInterface"
                    },
                },
            )
            self.assertEqual(
                modules,
                ["MixedPathsPaper.Assumptions", "MixedPathsPaper.PaperInterface"],
            )

    def test_signature_context_skips_unselected_existing_assumption_module(self) -> None:
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp_dir:
            absolute_folder = Path(temp_dir) / "NoAssumptionRowsPaper"
            absolute_folder.mkdir()
            folder = absolute_folder.relative_to(Path.cwd())
            (absolute_folder / "PaperInterface.lean").write_text(
                "theorem reviewed : True := by trivial\n", encoding="utf-8"
            )
            (absolute_folder / "Assumptions.lean").write_text(
                "axiom sourcePremise : Prop\n", encoding="utf-8"
            )
            (absolute_folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "source_file": (
                                f"{folder.as_posix()}/PaperInterface.lean"
                            ),
                            "assumption_source_file": (
                                f"{folder.as_posix()}/Assumptions.lean"
                            ),
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )

            with (
                mock.patch.object(
                    review_dashboard,
                    "signature_manifest_cache_context",
                    side_effect=lambda _root, module, **_kwargs: {
                        "import_module": module
                    },
                ) as signature_context,
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                contexts = review_dashboard.current_review_signature_contexts(folder)

            self.assertEqual(
                contexts,
                {
                    "PaperInterface.lean": {
                        "import_module": "NoAssumptionRowsPaper.PaperInterface"
                    }
                },
            )
            signature_context.assert_called_once()

    def test_only_lean_extraction_fields_invalidate_static_status_digest(self) -> None:
        base_surface = {
            "source_file": "papers/Example/PaperInterface.lean",
            "include_names": ["paperTheorem"],
            "assumption_names": [],
            "auxiliary_names": [],
            "slices": [{"id": "main", "names": ["paperTheorem"]}],
            "source_definition_names": ["sourceCondition"],
            "llm_statement_review": {"path": "audit/statement_match_llm.json"},
        }
        base = json.dumps({"review_surface": base_surface})
        display_edit = json.dumps(
            {
                "review_surface": {
                    **base_surface,
                    "slices": [{"id": "theory", "names": ["paperTheorem"]}],
                    "future_report_metadata": {"schema": 1},
                }
            }
        )
        extraction_edit = json.dumps(
            {
                "review_surface": {
                    **base_surface,
                    "include_names": ["paperTheorem", "paperLemma"],
                }
            }
        )

        self.assertEqual(
            review_dashboard._review_surface_static_status_digest(base),
            review_dashboard._review_surface_static_status_digest(display_edit),
        )
        self.assertNotEqual(
            review_dashboard._review_surface_rebind_status_digest(base),
            review_dashboard._review_surface_rebind_status_digest(display_edit),
        )
        self.assertNotEqual(
            review_dashboard._review_surface_static_status_digest(base),
            review_dashboard._review_surface_static_status_digest(extraction_edit),
        )

    def test_status_rebind_preserves_full_name_proposition_route(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "QualifiedRoutePaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "namespace Qualified\n"
                "theorem row : True := by trivial\n"
                "end Qualified\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["row"],
                            "proposition_spec_proofs": {
                                "Qualified.row": "Qualified.rowProof"
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            item = review_dashboard.ReviewItem(
                name="row",
                kind="theorem",
                lean_statement="theorem row : True",
                paper_statement="True.",
                agent_statement="True.",
                interface_source="theorem row : True",
                is_proposition_spec=True,
                line_number=2,
            )

            rebound = review_dashboard.rebind_cached_review_status(folder, [item])

            self.assertIsNotNone(rebound)
            assert rebound is not None
            self.assertEqual(rebound[0].full_name, "Qualified.row")
            self.assertEqual(
                rebound[0].proposition_spec_proof, "Qualified.rowProof"
            )
            self.assertEqual(rebound[0].proposition_spec_role, "proof_routed")

    def test_coverage_inventory_uses_current_anchor_not_map_summary_or_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "AnchorSelectedPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source_text = (
                "Theorem 1. Every admissible input has a witness.\n"
                "\n"
                "The displayed conclusion is part of the theorem.\n"
                "Proof.\n"
            )
            source.write_text(source_text, encoding="utf-8")
            quote = "\n".join(source_text.splitlines()[:3])
            anchor = {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 3,
                "quoted_text": quote,
                "quoted_text_sha256": hashlib.sha256(
                    quote.encode("utf-8")
                ).hexdigest(),
            }
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source.read_bytes()
                ).hexdigest(),
                "source_coverage_mode": "named_theoretical_statements",
                "items": {
                    # None of these navigation/classification fields can decide
                    # membership. The prose intentionally omits "Theorem 1".
                    "figure_caption_navigation_key": {
                        "source_kind": "remark",
                        "claim_bearing": True,
                        "statement": "Every admissible input has a witness.",
                        "lean_declarations": ["Fixture.figureCaptionHelper"],
                        "source_anchor_evidence": [anchor],
                    }
                },
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")

            full, selected, mode, error = review_dashboard.paper_coverage_inventory(
                folder
            )

            self.assertEqual(mode, "named_theoretical_statements")
            self.assertEqual(error, "")
            self.assertEqual(set(full), {"figure_caption_navigation_key"})
            self.assertEqual(set(selected), {"figure_caption_navigation_key"})

            # A broad source_location cannot stand in for the verified anchor.
            payload["items"]["figure_caption_navigation_key"].pop(
                "source_anchor_evidence"
            )
            payload["items"]["figure_caption_navigation_key"][
                "source_location"
            ] = "source.txt:1-3"
            map_path.write_text(json.dumps(payload), encoding="utf-8")
            _full, location_only, _mode, _error = (
                review_dashboard.paper_coverage_inventory(folder)
            )
            self.assertEqual(location_only, {})

    def test_coverage_inventory_rejects_anchor_spanning_multiple_presentations(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "AmbiguousAnchorPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source_text = (
                "Theorem 1. The first result holds.\n"
                "Lemma 2. The second result holds.\n"
            )
            source.write_text(source_text, encoding="utf-8")
            quote = source_text.rstrip("\n")
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source.read_bytes()
                ).hexdigest(),
                "source_coverage_mode": "named_theoretical_statements",
                "items": {
                    "misleading_single_row": {
                        "source_kind": "remark",
                        "claim_bearing": True,
                        "statement": "The source has a result.",
                        "proof_lean_declarations": ["Fixture.unrelated"],
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
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )

            _full, selected, _mode, _error = review_dashboard.paper_coverage_inventory(
                folder
            )

            self.assertEqual(selected, {})

    def test_source_anchor_gate_projects_normal_scope_before_validation(self) -> None:
        """Normal scope validates named theory, not every retained deep row."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ScopedAnchorPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source_text = (
                "Theorem 1. The named conclusion holds.\n"
                "Formula 2. A standalone display identity.\n"
                "Equation 3. A standalone equality.\n"
                "Algorithm 4. A standalone procedure.\n"
                "Figure 5. A numerical illustration.\n"
                "Remark 6. A corrected source-visible claim.\n"
            )
            source.write_text(source_text, encoding="utf-8")
            theorem_quote = source_text.splitlines()[0]
            theorem_anchor = {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": theorem_quote,
                "quoted_text_sha256": hashlib.sha256(
                    theorem_quote.encode("utf-8")
                ).hexdigest(),
            }
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source.read_bytes()
                ).hexdigest(),
                "source_anchor_evidence_required": True,
                "source_coverage_mode": "named_theoretical_statements",
                "items": {
                    "opaque_named_route": {
                        "source_kind": "theorem",
                        "claim_bearing": True,
                        "statement": "Theorem 1. The named conclusion holds.",
                        "source_location": "source.txt:1",
                        "source_anchor_evidence": [theorem_anchor],
                    },
                    # These retained rows intentionally have a source locator
                    # but no quote. They are normal-mode deep material even
                    # though their map keys and textual labels look operative.
                    "formula_navigation": {
                        "source_kind": "formula",
                        "claim_bearing": True,
                        "statement": "A standalone display identity.",
                        "source_location": "source.txt:2",
                    },
                    "equation_navigation": {
                        "source_kind": "equation",
                        "claim_bearing": True,
                        "statement": "A standalone equality.",
                        "source_location": "source.txt:3",
                    },
                    "algorithm_navigation": {
                        "source_kind": "algorithm",
                        "claim_bearing": True,
                        "statement": "A standalone procedure.",
                        "source_location": "source.txt:4",
                    },
                    "caption_navigation": {
                        "source_kind": "figure_caption",
                        "claim_bearing": True,
                        "statement": "A numerical illustration.",
                        "source_location": "source.txt:5",
                    },
                    # Explicit corrected targets remain source obligations in
                    # normal mode even when their presentation is a remark.
                    "explicit_correction": {
                        "source_kind": "remark",
                        "claim_bearing": True,
                        "coverage_status": "corrected_source_statement",
                        "statement": "A corrected source-visible claim.",
                        "source_location": "source.txt:6",
                    },
                },
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")

            normal_errors = review_dashboard._scoped_source_anchor_evidence_errors(
                folder
            )
            self.assertTrue(
                any("items.explicit_correction." in error for error in normal_errors),
                normal_errors,
            )
            normal_precheck = review_dashboard.source_inventory_precheck_summary(
                folder
            )
            self.assertEqual(
                normal_precheck["source_anchor_evidence_errors"], normal_errors
            )
            for deep_item in (
                "formula_navigation",
                "equation_navigation",
                "algorithm_navigation",
                "caption_navigation",
            ):
                self.assertFalse(
                    any(f"items.{deep_item}." in error for error in normal_errors),
                    normal_errors,
                )

            payload["source_coverage_mode"] = "deep_paper_with_all_prose_claims"
            map_path.write_text(json.dumps(payload), encoding="utf-8")
            deep_errors = review_dashboard._scoped_source_anchor_evidence_errors(folder)
            for deep_item in (
                "formula_navigation",
                "equation_navigation",
                "algorithm_navigation",
                "caption_navigation",
            ):
                self.assertTrue(
                    any(f"items.{deep_item}." in error for error in deep_errors),
                    deep_errors,
                )


if __name__ == "__main__":
    unittest.main()
