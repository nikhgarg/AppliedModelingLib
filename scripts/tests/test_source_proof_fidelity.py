#!/usr/bin/env python3
"""Regression tests for semantic source-proof fidelity ledgers."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
GATE_PATH = ROOT / "scripts" / "audit_evidence_integrity.py"
REPOSITORY_PATH = ROOT / "scripts" / "audit_repository.py"
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)
from source_coverage_scope import (  # noqa: E402
    DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
    KNOWN_SOURCE_PRESENTATION_KINDS,
    NAMED_THEORETICAL_STATEMENTS,
    filter_source_map_items_for_coverage,
)
SPEC = importlib.util.spec_from_file_location("audit_evidence_integrity", GATE_PATH)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)
from scripts import source_manifest_validation as source_validation
REPOSITORY_SPEC = importlib.util.spec_from_file_location(
    "audit_repository", REPOSITORY_PATH
)
assert REPOSITORY_SPEC is not None and REPOSITORY_SPEC.loader is not None
REPOSITORY = importlib.util.module_from_spec(REPOSITORY_SPEC)
sys.modules[REPOSITORY_SPEC.name] = REPOSITORY
REPOSITORY_SPEC.loader.exec_module(REPOSITORY)


class SourceProofFidelityTests(unittest.TestCase):
    def test_public_complete_selection_uses_explicit_repository_visibility(self) -> None:
        papers = self.root / "papers"
        (papers / "catalog.json").write_text(
            json.dumps(
                {
                    "publication_overrides": {
                        "Formalized": {},
                        "Caveated": {},
                        "Partial": {},
                        "AcademicallyPublishedButPrivate": {},
                    }
                }
            ),
            encoding="utf-8",
        )
        for paper, (status, visibility) in {
            "Formalized": ("formalized", "public"),
            "Caveated": ("formalized with caveat", "public"),
            "Partial": ("partially formalized", "public"),
            "AcademicallyPublishedButPrivate": ("formalized", "private_only"),
            "PrivateOnly": ("formalized", "private_only"),
        }.items():
            folder = papers / paper
            folder.mkdir(exist_ok=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": status,
                        "repository_visibility": visibility,
                    }
                ),
                encoding="utf-8",
            )
        previous_papers = GATE.PAPERS
        GATE.PAPERS = papers
        self.addCleanup(setattr, GATE, "PAPERS", previous_papers)

        selected = GATE.paper_dirs(public_complete=True)

        self.assertEqual(
            [folder.name for folder in selected], ["Caveated", "Formalized"]
        )

    def test_public_complete_selection_fails_closed_on_missing_visibility(self) -> None:
        papers = self.root / "papers"
        folder = papers / "MissingVisibility"
        folder.mkdir(exist_ok=True)
        (folder / "status.json").write_text(
            json.dumps({"status": "formalized"}), encoding="utf-8"
        )
        previous_papers = GATE.PAPERS
        GATE.PAPERS = papers
        self.addCleanup(setattr, GATE, "PAPERS", previous_papers)

        with self.assertRaisesRegex(ValueError, "explicit repository_visibility"):
            GATE.paper_dirs(public_complete=True)

    def test_paper_filter_cannot_bypass_public_complete_selection(self) -> None:
        papers = self.root / "papers"
        private = papers / "PrivateOnly"
        private.mkdir(exist_ok=True)
        (private / "status.json").write_text(
            json.dumps(
                {
                    "status": "formalized",
                    "repository_visibility": "private_only",
                }
            ),
            encoding="utf-8",
        )
        previous_papers = GATE.PAPERS
        GATE.PAPERS = papers
        self.addCleanup(setattr, GATE, "PAPERS", previous_papers)

        self.assertEqual(
            GATE.paper_dirs("PrivateOnly", public_complete=True),
            [],
        )
        missing = papers / "UnselectedMissingVisibility"
        missing.mkdir()
        (missing / "status.json").write_text(
            json.dumps({"status": "formalized"}), encoding="utf-8"
        )
        with self.assertRaisesRegex(ValueError, "explicit repository_visibility"):
            GATE.paper_dirs("PrivateOnly", public_complete=True)

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        source_root_patch = mock.patch.object(source_validation, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        previous_repository_root = REPOSITORY.ROOT
        REPOSITORY.ROOT = self.root
        self.addCleanup(setattr, REPOSITORY, "ROOT", previous_repository_root)
        self.paper = self.root / "papers" / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        self.artifact = self.paper / "source.tex"
        self.artifact.write_text(
            "\n".join(f"source line {index}" for index in range(1, 31)) + "\n",
            encoding="utf-8",
        )
        self.digest = hashlib.sha256(self.artifact.read_bytes()).hexdigest()

    def status(self) -> dict[str, object]:
        return {
            "review_surface": {
                "source_proof_fidelity_review": {
                    # A paper-relative path exercises the shared validator
                    # without coupling this fixture to a module-global root.
                    "ledger_file": "audit/source_proof_fidelity.json"
                }
            }
        }

    def write_source_first_inventory(self, *, source_defect_ids: list[str] | None = None) -> None:
        """Write a deliberately name-free source-first inventory fixture."""

        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "source_curated": True,
                    "source_inventory_kind": "atomic_source_inventory",
                    "source_artifact_path": "source.tex",
                    "source_artifact_sha256": self.digest,
                    "items": {
                        "opaque_inventory_atom_7": {
                            "statement": "The pinned source assertion is compared through its source artifact.",
                            "source_location": "source.tex:1-4",
                            "source_defect_ids": source_defect_ids or [],
                        }
                    },
                }
            ),
            encoding="utf-8",
        )

    def current_v10_status(self) -> dict[str, object]:
        """Return a fully wired current semantic/source review configuration."""

        return {
            "review_surface": {
                "source_proof_fidelity_review": {
                    "ledger_file": "papers/FixturePaper/audit/source_proof_fidelity.json"
                },
                "llm_statement_review": {
                    "lean_to_tex_file": "papers/FixturePaper/audit/lean_to_tex_llm.json",
                    "match_judgment_file": "papers/FixturePaper/audit/statement_match_llm.json",
                    "review_surface_audit_file": "papers/FixturePaper/audit/review_surface_llm.json",
                    "require_explicit_source_routes": True,
                },
                "llm_paper_coverage_review": {
                    "paper_coverage_audit_file": "papers/FixturePaper/audit/paper_coverage_llm.json",
                    "defect_support_judgment_file": "papers/FixturePaper/audit/defect_support_match_llm.json",
                },
                "llm_source_record_review": {
                    "source_record_audit_file": "papers/FixturePaper/audit/source_record_audit.json",
                    "source_record_judgment_file": "papers/FixturePaper/audit/source_record_match_llm.json",
                },
                "semantic_model_review": {
                    "schema": 2,
                    "required_dimensions": sorted(
                        GATE.SEMANTIC_MODEL_REVIEW_DIMENSIONS
                    ),
                },
            }
        }

    def zero_defect_ledger(self) -> dict[str, object]:
        ledger = self.valid_ledger()
        ledger["review_status"] = "reviewed_no_defects"
        ledger["defects"] = []
        scopes = ledger["reviewed_proof_scopes"]
        assert isinstance(scopes, list)
        scopes[0]["outcome"] = "no_defect"  # type: ignore[index]
        return ledger

    def valid_defect(self) -> dict[str, object]:
        return {
            "id": "D01",
            "source_locator": "source.tex:18-25, proof of Theorem 2",
            "source_claim": "The proof reverses the strict tail inequality while bounding the same event.",
            "defect_kind": "inequality_direction",
            "affected_source_locators": ["Theorem 2, p. 4", "source.tex:18-25"],
            "statement_impact": "proof_only",
            "status_impact": "formalized_note",
            "status_impact_rationale": "The repaired proof establishes the same substantive advertised theorem from the source hypotheses.",
            "repair_obligation": "Derive the needed tail comparison from monotonicity with the inequality in the source-theorem direction.",
            "acceptance_condition": "Lean proves the repaired comparison from the stated distribution hypotheses without a new paper assumption.",
            "resolution": "repaired_in_lean",
            "resolution_evidence": "The replacement argument uses monotonicity of the tail event and the theorem's existing hypotheses.",
        }

    def valid_ledger(self) -> dict[str, object]:
        return {
            "schema": 2,
            "paper": "FixturePaper",
            "source_artifact_path": "source.tex",
            "source_artifact_sha256": self.digest,
            "review_status": "defects_recorded",
            "reviewed_proof_scopes": [
                {
                    "source_locator": "Appendix A, proof of Theorem 2; source.tex:1-25",
                    "semantic_scope": "Tail-event comparison and its use in the main probability bound.",
                    "outcome": "defect_recorded",
                }
            ],
            "defects": [self.valid_defect()],
        }

    def write_ledger(self, payload: dict[str, object]) -> None:
        (self.paper / "audit" / "source_proof_fidelity.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def source_anchor(self, line_start: int, line_end: int | None = None) -> dict[str, object]:
        line_end = line_start if line_end is None else line_end
        source_lines = self.artifact.read_text(encoding="utf-8").splitlines()
        quote = "\n".join(source_lines[line_start - 1 : line_end])
        return {
            "path": self.artifact.name,
            "line_start": line_start,
            "line_end": line_end,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
        }

    def valid_deep_observation(self) -> dict[str, object]:
        return {
            "id": "DEEP-PROSE-01",
            "source_locator": "source.tex:8-12, unnumbered prose discussion",
            "affected_source_locators": ["source.tex:8-12", "source.tex:13-15"],
            "source_claim": "The unnumbered discussion asserts that the same comparison holds for every sample realization.",
            "finding": "The displayed source proof does not establish the asserted all-realizations endpoint from the stated assumptions.",
            "repair_handoff": "Prove a uniform comparison over the stated sample space or revise the prose claim in a separately reviewed source correction.",
            "normal_scope_disposition": "unnumbered_prose_outside_named_theory",
        }

    def write_deep_observation_map(
        self,
        *,
        item: dict[str, object] | None = None,
        mode: str = "named_theoretical_statements",
    ) -> None:
        deep_item = item or {
            "source_kind": "prose_assertion",
            "statement": "An unnumbered discussion makes a sample-level comparison.",
            "source_location": "source.tex:8-12",
            "source_anchor_evidence": [self.source_anchor(8, 12)],
            "deep_audit_observation_ids": ["DEEP-PROSE-01"],
        }
        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "source_artifact_path": self.artifact.name,
                    "source_artifact_sha256": self.digest,
                    "source_coverage_mode": mode,
                    "items": {"source_prose_row": deep_item},
                }
            ),
            encoding="utf-8",
        )

    def findings(
        self, payload: dict[str, object], status: str = "formalized"
    ) -> list[object]:
        self.write_ledger(payload)
        return GATE.source_proof_fidelity_findings(self.paper, status, self.status())

    def test_source_located_proof_only_repair_passes_without_lean_name_link(self) -> None:
        self.assertEqual(self.findings(self.valid_ledger()), [])

    def test_model_semantics_defect_kind_is_accepted(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0]["defect_kind"] = "model_semantics"

        self.assertEqual(self.findings(ledger), [])

    def test_full_closeout_requires_config_when_semantic_surface_exposes_proof_debt(self) -> None:
        unconfigured = {"review_surface": {}}

        explicit_route_findings = GATE.source_proof_fidelity_findings(
            self.paper,
            "formalized",
            {
                "review_surface": {
                    "llm_statement_review": {
                        "require_explicit_source_routes": True
                    }
                }
            },
        )
        self.assertTrue(
            any("requires explicit source routes" in finding.message for finding in explicit_route_findings)
        )

        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "items": {
                        "source_result": {"source_defect_ids": ["D01"]}
                    }
                }
            ),
            encoding="utf-8",
        )
        source_map_findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", unconfigured
        )
        self.assertTrue(
            any("canonical source map links" in finding.message for finding in source_map_findings)
        )

        (self.paper / "audit" / "paper_statement_map.json").unlink()
        self.write_ledger(self.valid_ledger())
        ledger_findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", unconfigured
        )
        self.assertTrue(
            any("canonical source-proof ledger records" in finding.message for finding in ledger_findings)
        )

    def test_zero_defect_archival_ledger_does_not_require_new_configuration(self) -> None:
        self.write_ledger(self.zero_defect_ledger())

        findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", {"review_surface": {}}
        )

        self.assertEqual(findings, [])

    def test_source_first_inventory_and_canonical_ledger_require_v10_migration(self) -> None:
        """The trigger uses artifact schema, not a theorem/declaration spelling."""

        self.write_source_first_inventory()
        self.write_ledger(self.zero_defect_ledger())

        findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", {"review_surface": {}}
        )

        self.assertTrue(
            any(
                finding.severity == "ERROR"
                and "v10-migration-pending" in finding.message
                and "llm_statement_review" in finding.message
                and "llm_source_record_review" in finding.message
                for finding in findings
            )
        )

    def test_current_v10_configuration_clears_migration_marker_without_name_routes(self) -> None:
        self.write_source_first_inventory()
        self.write_ledger(self.zero_defect_ledger())

        findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", self.current_v10_status()
        )

        self.assertFalse(
            any("v10-migration-pending" in finding.message for finding in findings)
        )
        self.assertEqual(findings, [])

    def test_v10_migration_requires_paths_to_stay_inside_paper(self) -> None:
        self.write_source_first_inventory()
        self.write_ledger(self.zero_defect_ledger())
        status = self.current_v10_status()
        review_surface = status["review_surface"]
        assert isinstance(review_surface, dict)
        statement_review = review_surface["llm_statement_review"]
        assert isinstance(statement_review, dict)
        statement_review["match_judgment_file"] = "../other-paper.json"

        findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "v10-migration-pending" in finding.message
                and "match_judgment_file escapes the paper folder" in finding.message
                for finding in findings
            )
        )

    def test_v10_migration_requires_defect_support_lane_for_source_defects(self) -> None:
        self.write_source_first_inventory(source_defect_ids=["D01"])
        self.write_ledger(self.valid_ledger())
        status = self.current_v10_status()
        review_surface = status["review_surface"]
        assert isinstance(review_surface, dict)
        coverage_review = review_surface["llm_paper_coverage_review"]
        assert isinstance(coverage_review, dict)
        del coverage_review["defect_support_judgment_file"]

        findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "v10-migration-pending" in finding.message
                and "defect_support_judgment_file" in finding.message
                for finding in findings
            )
        )

    def test_optional_model_conventions_and_checked_steps_are_structured(self) -> None:
        ledger = self.valid_ledger()
        ledger["model_conventions"] = [
            {
                "id": "MODEL-EVENT-01",
                "source_locator": "source.tex:3-10",
                "classification": "explicit_formalization_convention",
                "formal_meaning": "Calibration is compared through measurable joint events rather than an unspecified point-fiber conditional value.",
                "why_needed": "Null prediction fibers need a total semantic convention before the calibration formula has a fixed meaning.",
                "checked_scope": "The event identity is checked for the raw probability law used by the reviewed theorem.",
            }
        ]
        ledger["checked_proof_steps"] = [
            {
                "id": "STEP-MIXTURE-01",
                "source_locator": "source.tex:11-17",
                "source_step": "Form the finite mixture used in the source proof.",
                "checked_conclusion": "The Lean construction preserves the stated joint-event probabilities under the component weights.",
                "scope": "Finite measurable mixture only; it is not an arbitrary conditional-distribution theorem.",
            }
        ]

        self.assertEqual(self.findings(ledger), [])

        conventions = ledger["model_conventions"]
        assert isinstance(conventions, list)
        conventions[0].pop("checked_scope")  # type: ignore[index]
        findings = self.findings(ledger)
        self.assertTrue(
            any("model_conventions[0].checked_scope" in finding.message for finding in findings)
        )

    def test_deep_prose_observation_is_byte_pinned_and_neutral_to_normal_closeout(self) -> None:
        ledger = self.valid_ledger()
        ledger["deep_audit_observations"] = [self.valid_deep_observation()]
        self.write_deep_observation_map()

        self.assertEqual(self.findings(ledger), [])

    def test_deep_prose_observation_does_not_require_a_normal_scope_defect(self) -> None:
        ledger = self.zero_defect_ledger()
        ledger["review_status"] = "defects_recorded"
        scopes = ledger["reviewed_proof_scopes"]
        assert isinstance(scopes, list)
        scopes[0]["outcome"] = "defect_recorded"  # type: ignore[index]
        ledger["deep_audit_observations"] = [self.valid_deep_observation()]
        self.write_deep_observation_map()

        self.assertEqual(self.findings(ledger), [])

    def test_deep_prose_observation_requires_configured_ledger_at_closeout(self) -> None:
        ledger = self.zero_defect_ledger()
        ledger["review_status"] = "defects_recorded"
        scopes = ledger["reviewed_proof_scopes"]
        assert isinstance(scopes, list)
        scopes[0]["outcome"] = "defect_recorded"  # type: ignore[index]
        ledger["deep_audit_observations"] = [self.valid_deep_observation()]
        self.write_deep_observation_map()
        self.write_ledger(ledger)

        findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", {"review_surface": {}}
        )

        self.assertTrue(
            any("deep audit observations" in finding.message for finding in findings),
            findings,
        )

    def test_deep_prose_observation_requires_handoff_and_concrete_affected_anchors(self) -> None:
        ledger = self.valid_ledger()
        observation = self.valid_deep_observation()
        observation.pop("repair_handoff")
        observation["affected_source_locators"] = ["unanchored discussion"]
        ledger["deep_audit_observations"] = [observation]
        self.write_deep_observation_map()

        findings = self.findings(ledger)

        self.assertTrue(
            any("repair_handoff" in finding.message for finding in findings), findings
        )
        self.assertTrue(
            any("affected_source_locators" in finding.message for finding in findings),
            findings,
        )

    def test_deep_prose_observation_spans_must_use_the_pinned_ledger_artifact(self) -> None:
        other_source = self.paper / "other.tex"
        other_source.write_text("other source line\n", encoding="utf-8")
        ledger = self.valid_ledger()
        observation = self.valid_deep_observation()
        observation["source_locator"] = "other.tex:1, unnumbered prose discussion"
        observation["affected_source_locators"] = ["other.tex:1"]
        ledger["deep_audit_observations"] = [observation]
        self.write_deep_observation_map()

        findings = self.findings(ledger)

        self.assertTrue(
            any(
                "does not identify the ledger's canonical source artifact"
                in finding.message
                for finding in findings
            ),
            findings,
        )

    def test_deep_observation_cannot_hide_named_source_presentation(self) -> None:
        ledger = self.valid_ledger()
        ledger["deep_audit_observations"] = [self.valid_deep_observation()]
        self.write_deep_observation_map(
            item={
                "source_kind": "prose_assertion",
                "statement": "Theorem 3. The named source result remains mandatory.",
                "source_location": "source.tex:8-12",
                "source_anchor_evidence": [self.source_anchor(8, 12)],
                "deep_audit_observation_ids": ["DEEP-PROSE-01"],
            }
        )

        findings = self.findings(ledger)

        self.assertTrue(
            any(
                "selected by the normal named-theory scope" in finding.message
                for finding in findings
            ),
            findings,
        )

    def test_prose_assertion_is_known_but_deep_only(self) -> None:
        item = {
            "source_kind": "prose_assertion",
            "statement": "An unnumbered source passage asserts an endpoint.",
        }

        self.assertIn("prose_assertion", KNOWN_SOURCE_PRESENTATION_KINDS)
        self.assertNotIn(
            "prose_assertion", REPOSITORY.THEOREM_LIKE_SOURCE_INVENTORY_KINDS
        )
        self.assertEqual(
            filter_source_map_items_for_coverage(
                {"unnumbered": item}, NAMED_THEORETICAL_STATEMENTS
            ),
            {},
        )
        self.assertEqual(
            filter_source_map_items_for_coverage(
                {"unnumbered": item}, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
            ),
            {"unnumbered": item},
        )

    def test_model_context_is_known_but_not_an_ordinary_named_claim(self) -> None:
        item = {
            "source_kind": "model_context",
            "statement": "An unnumbered source-model explanation.",
        }

        self.assertIn("model_context", KNOWN_SOURCE_PRESENTATION_KINDS)
        self.assertNotIn(
            "model_context", REPOSITORY.THEOREM_LIKE_SOURCE_INVENTORY_KINDS
        )
        self.assertEqual(
            filter_source_map_items_for_coverage(
                {"context": item}, NAMED_THEORETICAL_STATEMENTS
            ),
            {},
        )

    def test_deep_observation_cannot_bypass_deep_all_prose_review(self) -> None:
        ledger = self.valid_ledger()
        ledger["deep_audit_observations"] = [self.valid_deep_observation()]
        self.write_deep_observation_map(mode="deep_paper_with_all_prose_claims")

        findings = self.findings(ledger)

        self.assertTrue(
            any("permitted only when source_coverage_mode" in finding.message for finding in findings),
            findings,
        )

    def test_closed_status_requires_a_completed_semantic_proof_review(self) -> None:
        ledger = self.valid_ledger()
        ledger["review_status"] = "not_started"
        ledger["reviewed_proof_scopes"] = []
        ledger["defects"] = []

        findings = self.findings(ledger)

        self.assertTrue(
            any("requires a completed source-proof fidelity review" in finding.message for finding in findings)
        )

    def test_source_assumption_is_not_a_permitted_proof_defect_resolution(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0]["resolution"] = "validated_source_assumption"  # type: ignore[index]

        findings = self.findings(ledger)

        self.assertTrue(
            any("source assumptions are not a permitted" in finding.message for finding in findings)
        )

    def test_file_line_anchor_must_resolve_inside_the_local_source_cache(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0]["source_locator"] = "source.tex:31-32"  # type: ignore[index]

        findings = self.findings(ledger)

        self.assertTrue(
            any("outside its 30-line source" in finding.message for finding in findings)
        )

    def test_open_obligation_blocks_closed_status_but_can_be_recorded_for_partial_work(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0]["resolution"] = "open_proof_obligation"  # type: ignore[index]
        defects[0]["status_impact"] = "partially_formalized"  # type: ignore[index]
        defects[0]["status_impact_rationale"] = (  # type: ignore[index]
            "The replacement derivation remains open, so the intended source endpoint is not fully formalized."
        )

        closed = self.findings(ledger, "formalized")
        self.assertTrue(any("open_proof_obligation" in finding.message for finding in closed))

        partial = self.findings(ledger, "partially formalized")
        self.assertFalse(any(finding.severity == "ERROR" for finding in partial))

    def test_unrelated_open_obligation_is_not_laundered_into_a_corrected_scope(self) -> None:
        """A narrow approved correction cannot force unrelated debt to look approved."""

        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defect = defects[0]
        assert isinstance(defect, dict)
        defect["resolution"] = "open_proof_obligation"
        defect["status_impact"] = "partially_formalized"
        defect["status_impact_rationale"] = (
            "The source endpoint still needs a derivation and cannot receive "
            "credit from an unrelated approved correction."
        )

        status = self.status()
        status["formalization_scope"] = {
            "kind": GATE.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
            "correction_ids": ["APPROVED-TARGET-01"],
        }
        status["governing_corrections"] = [{"id": "APPROVED-TARGET-01"}]
        self.write_ledger(ledger)

        # This unit test exercises only the ledger-scope boundary; the full
        # corrected-model contract has its own dedicated validation tests.
        with patch.object(
            GATE, "corrected_model_scope_contract_findings", return_value=[]
        ):
            findings = GATE.source_proof_fidelity_findings(
                self.paper, "partially formalized", status
            )

        self.assertFalse(any(finding.severity == "ERROR" for finding in findings), findings)

    def test_declared_governing_metadata_stays_strict(self) -> None:
        """Once a row claims a governing correction, all metadata must validate."""

        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defect = defects[0]
        assert isinstance(defect, dict)
        defect["correction_id"] = "UNKNOWN-CORRECTION"

        status = self.status()
        status["formalization_scope"] = {
            "kind": GATE.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
            "correction_ids": ["APPROVED-TARGET-01"],
        }
        status["governing_corrections"] = [{"id": "APPROVED-TARGET-01"}]
        self.write_ledger(ledger)

        with patch.object(
            GATE, "corrected_model_scope_contract_findings", return_value=[]
        ):
            findings = GATE.source_proof_fidelity_findings(
                self.paper, "partially formalized", status
            )

        messages = [finding.message for finding in findings]
        self.assertTrue(
            any("governing_disposition" in message for message in messages),
            messages,
        )
        self.assertTrue(
            any("declared governing correction" in message for message in messages),
            messages,
        )

    def test_component_scope_allows_a_separate_declared_local_repair(self) -> None:
        """Component evidence cannot erase a separately documented local repair."""

        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defect = defects[0]
        assert isinstance(defect, dict)
        defect.update(
            {
                "governing_disposition": "repaired_in_governing_proof",
                "correction_id": "LOCAL-REPAIR-01",
                "corrected_clause_anchor": "source.tex:18-25",
                "conclusion_relation": "same",
                "does_not_claim_archive_derivation": True,
            }
        )

        status = self.status()
        status["formalization_scope"] = {
            "kind": GATE.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
            "scope_role": GATE.COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE,
            "whole_paper_closeout_claimed": False,
            "correction_ids": ["APPROVED-COMPONENT-01"],
        }
        status["governing_corrections"] = [
            {"id": "APPROVED-COMPONENT-01"},
            {"id": "LOCAL-REPAIR-01"},
        ]
        self.write_ledger(ledger)

        with patch.object(
            GATE, "corrected_model_scope_contract_findings", return_value=[]
        ):
            findings = GATE.source_proof_fidelity_findings(
                self.paper, "partially formalized", status
            )

        self.assertFalse(any(finding.severity == "ERROR" for finding in findings), findings)

    def test_minor_statement_repair_can_be_a_formalized_note(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0]["statement_impact"] = "source_statement"  # type: ignore[index]
        defects[0]["resolution"] = "corrected_source_statement"  # type: ignore[index]
        defects[0]["status_impact"] = "formalized_note"  # type: ignore[index]
        defects[0]["status_impact_rationale"] = (  # type: ignore[index]
            "The finite printed correction leaves the substantive advertised endpoint unchanged and fully proved."
        )

        findings = self.findings(ledger, "formalized")

        self.assertEqual(findings, [])

    def test_user_approved_scope_exclusion_is_visible_and_byte_pinned(self) -> None:
        """An explicit user scope decision is not an unresolved proof defect."""

        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defect = defects[0]
        assert isinstance(defect, dict)
        defect["statement_impact"] = "source_statement"
        defect["status_impact"] = "formalized_note"
        defect["status_impact_rationale"] = (
            "The source-visible assertion is retained in the audit record, but the user "
            "expressly excluded this separate claim from the formalization campaign."
        )
        defect["resolution"] = "user_approved_scope_exclusion"
        locator = str(defect["source_locator"])
        quote = "\n".join(f"source line {index}" for index in range(18, 26))
        defect["user_approved_scope_exclusion"] = {
            "schema": 1,
            "approval_kind": "explicit_user_instruction",
            "approval_reference": "User instruction recorded for the active remediation pass.",
            "approved_at": "2026-07-25",
            "reason": "The user explicitly excluded this source-visible assertion from required formalization scope.",
            "source_locator": locator,
            "source_evidence": "The exact cited source span is retained and byte-pinned below.",
            "source_anchor_quote_sha256": hashlib.sha256(
                quote.encode("utf-8")
            ).hexdigest(),
        }

        self.assertEqual(self.findings(ledger, "formalized"), [])

        del defect["user_approved_scope_exclusion"]["approval_reference"]
        malformed = self.findings(ledger, "formalized")
        self.assertTrue(
            any("approval_reference" in finding.message for finding in malformed)
        )

    def test_structural_scope_exclusion_omits_only_missing_source_quote_check(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defect = defects[0]
        assert isinstance(defect, dict)
        defect["statement_impact"] = "source_statement"
        defect["status_impact"] = "formalized_note"
        defect["status_impact_rationale"] = (
            "The source-visible assertion remains recorded under the user's explicit scope decision."
        )
        defect["resolution"] = "user_approved_scope_exclusion"
        locator = str(defect["source_locator"])
        quote = "\n".join(f"source line {index}" for index in range(18, 26))
        defect["user_approved_scope_exclusion"] = {
            "schema": 1,
            "approval_kind": "explicit_user_instruction",
            "approval_reference": "User instruction recorded for the active remediation pass.",
            "approved_at": "2026-07-25",
            "reason": "The user explicitly excluded this source-visible assertion from required formalization scope.",
            "source_locator": locator,
            "source_evidence": "The exact cited source span is retained and byte-pinned below.",
            "source_anchor_quote_sha256": hashlib.sha256(
                quote.encode("utf-8")
            ).hexdigest(),
        }
        self.write_ledger(ledger)
        self.artifact.unlink()

        structural = GATE.source_proof_fidelity_findings(
            self.paper,
            "formalized",
            self.status(),
            require_source_bytes=False,
        )
        self.assertFalse(
            any(finding.severity == "ERROR" for finding in structural), structural
        )
        self.assertTrue(
            any("not release certification" in finding.message for finding in structural),
            structural,
        )

        strict = GATE.source_proof_fidelity_findings(
            self.paper,
            "formalized",
            self.status(),
            require_source_bytes=True,
        )
        self.assertTrue(
            any("source text cannot be read" in finding.message for finding in strict),
            strict,
        )

        approval = defect["user_approved_scope_exclusion"]
        assert isinstance(approval, dict)
        approval["source_locator"] = "source.tex:17-25"
        approval["source_anchor_quote_sha256"] = "not-a-digest"
        self.write_ledger(ledger)
        malformed = GATE.source_proof_fidelity_findings(
            self.paper,
            "formalized",
            self.status(),
            require_source_bytes=False,
        )
        messages = [finding.message for finding in malformed]
        self.assertTrue(any("must exactly match" in message for message in messages), messages)
        self.assertTrue(any("must be a SHA-256 digest" in message for message in messages), messages)

    def test_substantial_source_error_requires_caveat_status_and_closed_correction(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0]["statement_impact"] = "source_statement"  # type: ignore[index]
        defects[0]["status_impact"] = "formalized_with_caveat"  # type: ignore[index]
        defects[0]["status_impact_rationale"] = (  # type: ignore[index]
            "The central source theorem is false and the corrected theorem materially changes its economic interpretation."
        )
        defects[0]["resolution"] = "corrected_source_statement"  # type: ignore[index]

        plain = self.findings(ledger, "formalized")
        self.assertTrue(any("conflicts with paper status" in finding.message for finding in plain))

        caveated = self.findings(ledger, "formalized with caveat")
        self.assertEqual(caveated, [])

        defects[0]["resolution"] = "repaired_in_lean"  # type: ignore[index]
        unresolved = self.findings(ledger, "formalized with caveat")
        self.assertTrue(
            any("requires a fully checked corrected_source_statement" in finding.message for finding in unresolved)
        )

    def test_caveat_status_requires_a_substantial_source_error_entry(self) -> None:
        findings = self.findings(self.valid_ledger(), "formalized with caveat")
        self.assertTrue(
            any("requires at least one schema-2 defect" in finding.message for finding in findings)
        )

    def test_schema_one_is_not_enough_for_full_closeout(self) -> None:
        ledger = self.valid_ledger()
        ledger["schema"] = 1
        findings = self.findings(ledger, "formalized")
        self.assertTrue(
            any("requires source-proof fidelity schema 2" in finding.message for finding in findings)
        )

    def test_defect_ids_are_required_and_unique(self) -> None:
        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0].pop("id")  # type: ignore[union-attr]
        missing = self.findings(ledger)
        self.assertTrue(any(".id must be a stable" in finding.message for finding in missing))

        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects.append(self.valid_defect())
        duplicate = self.findings(ledger)
        self.assertTrue(any("duplicates source-proof defect" in finding.message for finding in duplicate))

    def test_folder_relative_custom_ledger_path_is_honored(self) -> None:
        custom = self.paper / "proof-ledger.json"
        custom.write_text(json.dumps(self.valid_ledger()), encoding="utf-8")
        status = {
            "review_surface": {
                "source_proof_fidelity_review": {"ledger_file": "proof-ledger.json"}
            }
        }
        self.assertEqual(
            GATE.source_proof_fidelity_findings(self.paper, "formalized", status), []
        )

    def test_full_closeout_cannot_select_clean_alternate_over_canonical_debt(self) -> None:
        self.write_ledger(self.valid_ledger())
        alternate = self.paper / "proof-ledger.json"
        clean = self.valid_ledger()
        clean["review_status"] = "reviewed_no_defects"
        clean["defects"] = []
        scopes = clean["reviewed_proof_scopes"]
        assert isinstance(scopes, list)
        scopes[0]["outcome"] = "no_defect"  # type: ignore[index]
        alternate.write_text(json.dumps(clean), encoding="utf-8")
        alternate_status = {
            "review_surface": {
                "source_proof_fidelity_review": {
                    "ledger_file": "proof-ledger.json"
                }
            }
        }

        findings = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", alternate_status
        )

        self.assertTrue(
            any("must resolve to the canonical" in finding.message for finding in findings)
        )
        self.assertEqual(
            GATE.source_proof_fidelity_findings(
                self.paper, "partially formalized", alternate_status
            ),
            [],
        )

        relative_canonical_status = {
            "review_surface": {
                "source_proof_fidelity_review": {
                    "ledger_file": "audit/source_proof_fidelity.json"
                }
            }
        }
        self.assertEqual(
            GATE.source_proof_fidelity_findings(
                self.paper, "formalized", relative_canonical_status
            ),
            [],
        )

    def test_full_closeout_source_map_defect_ids_must_resolve_in_ledger(self) -> None:
        self.write_ledger(self.valid_ledger())
        source_map = self.paper / "audit" / "paper_statement_map.json"
        source_map.write_text(
            json.dumps(
                {
                    "items": {
                        "source_result": {"source_defect_ids": ["UNRECORDED"]}
                    }
                }
            ),
            encoding="utf-8",
        )

        missing = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", self.status()
        )
        self.assertTrue(
            any(
                "source_defect_ids absent from the configured" in finding.message
                for finding in missing
            )
        )

        source_map.write_text(
            json.dumps(
                {"items": {"source_result": {"source_defect_ids": ["D01"]}}}
            ),
            encoding="utf-8",
        )
        self.assertEqual(
            GATE.source_proof_fidelity_findings(
                self.paper, "formalized", self.status()
            ),
            [],
        )

        source_map.write_text(
            json.dumps(
                {"items": {"source_result": {"source_defect_ids": [17]}}}
            ),
            encoding="utf-8",
        )
        malformed = GATE.source_proof_fidelity_findings(
            self.paper, "formalized", self.status()
        )
        self.assertTrue(
            any(
                "<malformed-source-defect-id:int>" in finding.message
                for finding in malformed
            )
        )

    def test_repository_closeout_reuses_the_same_source_proof_gate(self) -> None:
        self.write_ledger(self.valid_ledger())
        self.assertEqual(
            REPOSITORY.check_source_proof_fidelity(
                self.paper, "formalized", self.status()
            ),
            [],
        )

        ledger = self.valid_ledger()
        defects = ledger["defects"]
        assert isinstance(defects, list)
        defects[0]["resolution"] = "open_proof_obligation"  # type: ignore[index]
        self.write_ledger(ledger)
        findings = REPOSITORY.check_source_proof_fidelity(
            self.paper, "formalized", self.status()
        )
        self.assertTrue(any("open_proof_obligation" in finding.message for finding in findings))

    def test_repository_closeout_reuses_required_config_and_semantic_model_gates(self) -> None:
        self.write_ledger(self.valid_ledger())

        fidelity_findings = REPOSITORY.check_source_proof_fidelity(
            self.paper, "formalized", {"review_surface": {}}
        )
        self.assertTrue(
            any("canonical source-proof ledger records" in finding.message for finding in fidelity_findings)
        )

        self.write_source_first_inventory()
        self.write_ledger(self.zero_defect_ledger())
        migration_findings = REPOSITORY.check_source_proof_fidelity(
            self.paper, "formalized", {"review_surface": {}}
        )
        self.assertTrue(
            any("v10-migration-pending" in finding.message for finding in migration_findings)
        )

        semantic_findings = REPOSITORY.check_explicit_source_route_semantic_model_evidence(
            self.paper,
            "formalized",
            {
                "review_surface": {
                    "llm_statement_review": {
                        "require_explicit_source_routes": True
                    }
                }
            },
        )
        self.assertTrue(
            any("semantic_model_review schema 2" in finding.message for finding in semantic_findings)
        )

    def test_selected_v11_fidelity_gate_never_demands_v10_migration_bundle(
        self,
    ) -> None:
        context = mock.Mock(spec=GATE.V11EvidenceRunContext)
        with (
            mock.patch.object(
                GATE,
                "v10_migration_pending_findings",
                side_effect=AssertionError(
                    "selected v11 fidelity audit entered the v10 migration gate"
                ),
            ),
            mock.patch.object(
                source_validation, "source_proof_fidelity_config", return_value=None
            ),
            mock.patch.object(
                source_validation,
                "source_proof_fidelity_requirement_reasons",
                return_value=(),
            ),
        ):
            findings = GATE.source_proof_fidelity_findings(
                self.paper,
                "formalized",
                {},
                context=context,
            )

        self.assertEqual(findings, [])

    def test_repository_structural_mode_does_not_certify_missing_source_bytes(self) -> None:
        self.write_ledger(self.valid_ledger())
        self.artifact.unlink()
        findings = REPOSITORY.check_source_proof_fidelity(
            self.paper,
            "formalized",
            self.status(),
            require_source_bytes=False,
        )
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "WARN")
        self.assertIn("not release certification", findings[0].message)


if __name__ == "__main__":
    unittest.main()
