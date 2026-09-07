"""Regression checks for content-addressed source-record cache controls."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from scripts import audit_evidence_integrity as EVIDENCE


ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SPEC = importlib.util.spec_from_file_location(
    "source_record_fingerprint_projection_audit", HELPER
)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


class SourceRecordFingerprintProjectionTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.paper_dir = self.root / "papers" / "Fixture"
        self.audit_dir = self.paper_dir / "audit"
        self.audit_dir.mkdir(parents=True)
        (self.paper_dir / "PaperInterface.lean").write_text(
            "namespace Fixture\nend Fixture\n", encoding="utf-8"
        )
        (self.audit_dir / "paper_statement_map.json").write_text(
            "{}\n", encoding="utf-8"
        )
        self.status = {
            "status": "formalized",
            "review_surface": {
                "source_file": "papers/Fixture/PaperInterface.lean",
                "include_names": ["endpoint"],
                "assumption_names": [],
                "auxiliary_names": [],
                "quarantined_auxiliary_names": [],
                "semantic_model_review": {
                    "schema": AUDIT.SEMANTIC_MODEL_REVIEW_SCHEMA,
                    "required_dimensions": list(
                        AUDIT.SEMANTIC_MODEL_DIMENSION_ORDER
                    ),
                },
            },
        }
        self.fidelity = {
            "schema": 2,
            "paper": "Fixture",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": "a" * 64,
            "review_status": "reviewed_no_defects",
            "reviewed_proof_scopes": [],
            "model_conventions": [],
            "checked_proof_steps": [],
            "defects": [],
            # These are deliberately outside source_proof_fidelity_context.
            "policy": ["editing this must not rerun a raw source-record scan"],
            "deep_audit_observations": ["display-only audit note"],
        }
        self._write_inputs()
        self.args = SimpleNamespace(
            paper="Fixture",
            max_depth=4,
            no_lean=False,
            force=False,
            refresh_judgment_summary=False,
            ignore_current_judgments=False,
        )

    def _write_inputs(self) -> None:
        (self.paper_dir / "status.json").write_text(
            json.dumps(self.status, sort_keys=True), encoding="utf-8"
        )
        (self.audit_dir / "source_proof_fidelity.json").write_text(
            json.dumps(self.fidelity, sort_keys=True), encoding="utf-8"
        )

    def _fingerprint(self) -> dict[str, object]:
        full, semantic = AUDIT.paper_statement_map_cache_receipts(self.paper_dir)
        fingerprint = AUDIT.source_record_input_fingerprint(
            self.args,
            self.root,
            self.paper_dir,
            paper_statement_map_sha256=full,
            paper_statement_map_semantic_sha256=semantic,
        )
        self.assertIsInstance(fingerprint, dict)
        assert isinstance(fingerprint, dict)
        return fingerprint

    def _cache_patches(self):
        return (
            patch.object(
                AUDIT,
                "configured_review_reference_static_error",
                return_value="",
            ),
            patch.object(AUDIT, "source_record_audit_receipt_error", return_value=""),
            patch.object(
                AUDIT, "source_record_raw_reusable_item_metadata_error", return_value=""
            ),
            patch.object(
                AUDIT, "source_record_raw_scan_completeness_error", return_value=""
            ),
            patch.object(
                AUDIT,
                "source_record_saved_statement_ledger_coverages",
                return_value=(set(), set()),
            ),
            patch.object(
                AUDIT,
                "refresh_existing_judgment_summary",
                return_value={"reused": True},
            ),
        )

    def _write_reusable_raw(self, fingerprint: dict[str, object]) -> tuple[str, str]:
        full, semantic = AUDIT.paper_statement_map_cache_receipts(self.paper_dir)
        payload = {
            "paper": "Fixture",
            "prompt_version": AUDIT.SOURCE_RECORD_PROMPT_VERSION,
            "source_record_audit_sha256": "b" * 64,
            "paper_statement_map_sha256": full,
            "source_record_input_fingerprint": fingerprint,
            "lean_check": {"returncode": 0},
        }
        (self.audit_dir / "source_record_audit.json").write_text(
            json.dumps(payload, sort_keys=True), encoding="utf-8"
        )
        return full, semantic

    def test_policy_and_sidecar_only_changes_reuse_but_consumed_input_rejects_rebind(
        self,
    ) -> None:
        baseline = self._fingerprint()
        self.assertEqual(baseline["schema"], 10)
        full, semantic = self._write_reusable_raw(baseline)

        # These fields can affect dashboard/LLM presentation, but any saved
        # direct-ledger suppression is independently revalidated before reuse.
        # They must not force the expensive raw scan by themselves.
        surface = self.status["review_surface"]
        assert isinstance(surface, dict)
        surface["llm_source_record_review"] = {
            "policy": "source-record-sidecar-v-next",
            "sidecar": "audit/source_record_match_llm.json",
        }
        surface["llm_paper_coverage_review"] = {"policy": "coverage-v-next"}
        surface["llm_assumption_review"] = {"policy": "assumptions-v-next"}
        self.fidelity["policy"] = ["updated editing guidance"]
        self.fidelity["deep_audit_observations"] = ["updated non-generator note"]
        self._write_inputs()
        self.assertEqual(self._fingerprint(), baseline)

        with ExitStack() as stack:
            for item in self._cache_patches():
                stack.enter_context(item)
            self.assertEqual(
                AUDIT.reusable_source_record_audit(
                    self.args,
                    self.root,
                    self.paper_dir,
                    paper_statement_map_sha256=full,
                    paper_statement_map_semantic_sha256=semantic,
                ),
                {"reused": True},
            )

        # Changing an effective source-record row selector is a raw-generator
        # input. It must not match the narrow fingerprint and therefore
        # requires a fresh raw receipt.
        surface["include_names"] = ["endpoint", "new_endpoint"]
        self._write_inputs()
        self.assertNotEqual(self._fingerprint(), baseline)
        with ExitStack() as stack:
            for item in self._cache_patches():
                stack.enter_context(item)
            self.assertIsNone(
                AUDIT.reusable_source_record_audit(
                    self.args,
                    self.root,
                    self.paper_dir,
                    paper_statement_map_sha256=full,
                    paper_statement_map_semantic_sha256=semantic,
                )
            )

    def test_semantic_model_and_fidelity_context_changes_remain_pinned(self) -> None:
        baseline = self._fingerprint()
        surface = self.status["review_surface"]
        assert isinstance(surface, dict)
        semantic_review = surface["semantic_model_review"]
        assert isinstance(semantic_review, dict)
        semantic_review["required_dimensions"] = [
            AUDIT.SEMANTIC_MODEL_DIMENSION_ORDER[0]
        ]
        self._write_inputs()
        self.assertNotEqual(self._fingerprint(), baseline)

        semantic_review["required_dimensions"] = list(
            AUDIT.SEMANTIC_MODEL_DIMENSION_ORDER
        )
        self.fidelity["defects"] = [
            {
                "id": "FIXTURE-DEFECT",
                "source_locator": "source.txt:1",
                "source_claim": "The source endpoint has a defect.",
            }
        ]
        self._write_inputs()
        self.assertNotEqual(self._fingerprint(), baseline)

    def test_explicit_source_target_selection_is_a_raw_fingerprint_control(self) -> None:
        baseline = self._fingerprint()
        surface = self.status["review_surface"]
        assert isinstance(surface, dict)
        semantic_review = surface["semantic_model_review"]
        assert isinstance(semantic_review, dict)
        semantic_review["explicit_source_target_declarations"] = [
            "Fixture.PaperInterface.endpoint"
        ]
        self._write_inputs()
        self.assertNotEqual(self._fingerprint(), baseline)

    def test_coverage_protocol_change_invalidates_source_record_input(self) -> None:
        with patch.object(
            AUDIT,
            "formalization_coverage_protocol_digest",
            return_value="a" * 64,
        ):
            original = self._fingerprint()
        with patch.object(
            AUDIT,
            "formalization_coverage_protocol_digest",
            return_value="b" * 64,
        ):
            changed = self._fingerprint()

        self.assertEqual(
            original["formalization_coverage_protocol_sha256"], "a" * 64
        )
        self.assertEqual(
            changed["formalization_coverage_protocol_sha256"], "b" * 64
        )
        self.assertNotEqual(original, changed)

    def test_review_protocol_and_prompt_changes_do_not_invalidate_extraction(
        self,
    ) -> None:
        baseline = self._fingerprint()
        with (
            patch.object(
                AUDIT,
                "formalization_protocol_digest",
                return_value="f" * 64,
            ),
            patch.object(
                AUDIT,
                "SOURCE_RECORD_PROMPT_VERSION",
                "source-record-review-only-v-next",
            ),
        ):
            changed = self._fingerprint()

        self.assertEqual(changed, baseline)
        self.assertNotIn("source_record_policy_version", baseline)

    def test_legacy_v9_protocol_projection_is_exact_current_only(self) -> None:
        current = self._fingerprint()
        with (
            patch.object(
                AUDIT,
                "legacy_source_map_cache_semantic_sha256",
                return_value="d" * 64,
            ),
            patch.object(
                AUDIT,
                "formalization_protocol_digest",
                return_value="e" * 64,
            ),
        ):
            legacy = AUDIT.source_record_legacy_v9_protocol_fingerprint(
                current, self.paper_dir
            )

        self.assertIsInstance(legacy, dict)
        assert isinstance(legacy, dict)
        self.assertEqual(legacy["schema"], 9)
        self.assertNotIn("formalization_coverage_protocol_sha256", legacy)
        self.assertEqual(legacy["formalization_protocol_sha256"], "e" * 64)
        self.assertEqual(
            legacy["paper_statement_map_semantic_sha256"], "d" * 64
        )
        self.assertEqual(
            legacy["source_record_policy_version"],
            AUDIT.SOURCE_RECORD_PROMPT_VERSION,
        )

    def test_assumption_role_change_is_pinned_when_row_is_already_included(self) -> None:
        """The assumption role changes semantic selection beyond merged row routing."""

        baseline = self._fingerprint()
        full, semantic = self._write_reusable_raw(baseline)
        before_projection = AUDIT.source_record_status_control_projection(
            self.paper_dir, self.paper_dir / "status.json", self.status
        )
        surface = self.status["review_surface"]
        assert isinstance(surface, dict)
        # ``endpoint`` is already in include_names, so the merged configured
        # row list is unchanged.  The generator nevertheless selects it as an
        # assumption semantic-model row after this role change.
        surface["assumption_names"] = ["endpoint"]
        self._write_inputs()
        after_projection = AUDIT.source_record_status_control_projection(
            self.paper_dir, self.paper_dir / "status.json", self.status
        )
        self.assertEqual(
            before_projection["configured_rows"], after_projection["configured_rows"]
        )
        self.assertNotEqual(
            before_projection["assumption_rows"], after_projection["assumption_rows"]
        )
        self.assertNotEqual(self._fingerprint(), baseline)

        with ExitStack() as stack:
            for item in self._cache_patches():
                stack.enter_context(item)
            self.assertIsNone(
                AUDIT.reusable_source_record_audit(
                    self.args,
                    self.root,
                    self.paper_dir,
                    paper_statement_map_sha256=full,
                    paper_statement_map_semantic_sha256=semantic,
                )
            )

    def test_legacy_v7_receipt_reissues_without_producer_code_identity(self) -> None:
        full, semantic = AUDIT.paper_statement_map_cache_receipts(self.paper_dir)
        legacy = AUDIT.source_record_legacy_v7_input_fingerprint(
            self.args,
            self.root,
            self.paper_dir,
            paper_statement_map_sha256=full,
            paper_statement_map_semantic_sha256=semantic,
        )
        self.assertIsInstance(legacy, dict)
        assert isinstance(legacy, dict)
        self.assertEqual(legacy["schema"], 7)
        self.assertNotEqual(self._fingerprint(), legacy)
        self._write_reusable_raw(legacy)

        with ExitStack() as stack:
            for item in self._cache_patches():
                stack.enter_context(item)
            self.assertIsNone(
                AUDIT.reusable_source_record_audit(
                    self.args,
                    self.root,
                    self.paper_dir,
                    paper_statement_map_sha256=full,
                    paper_statement_map_semantic_sha256=semantic,
                )
            )

    def test_evidence_gate_rejects_legacy_v7_without_producer_code_identity(self) -> None:
        """A v7 receipt cannot bypass the automatic raw-producer binding."""

        full, semantic = AUDIT.paper_statement_map_cache_receipts(self.paper_dir)
        legacy = AUDIT.source_record_legacy_v7_input_fingerprint(
            self.args,
            self.root,
            self.paper_dir,
            paper_statement_map_sha256=full,
            paper_statement_map_semantic_sha256=semantic,
        )
        current = self._fingerprint()
        assert isinstance(legacy, dict)
        self.assertFalse(
            EVIDENCE.source_record_legacy_v7_fingerprint_is_current(
                legacy, current
            )
        )
        missing_projection = dict(legacy)
        missing_projection.pop("toolchain_identities")
        self.assertFalse(
            EVIDENCE.source_record_legacy_v7_fingerprint_is_current(
                missing_projection, current
            )
        )
        helper = (
            self.root
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py"
        )
        helper.parent.mkdir(parents=True)
        helper.write_text("# identity helper fixture\n", encoding="utf-8")
        audit_payload = {
            "paper": "Fixture",
            "source_record_audit_sha256": "c" * 64,
            "paper_statement_map_sha256": full,
            "source_record_input_fingerprint": legacy,
        }
        identity_payload = {
            "schema": 1,
            "paper": "Fixture",
            "paper_statement_map_sha256": full,
            "paper_statement_map_semantic_sha256": semantic,
            "source_record_input_fingerprint": current,
            "legacy_v7_source_record_input_fingerprint": legacy,
        }
        previous_root = EVIDENCE.ROOT
        EVIDENCE.ROOT = self.root
        self.addCleanup(setattr, EVIDENCE, "ROOT", previous_root)
        with patch.object(
            EVIDENCE.subprocess,
            "run",
            return_value=SimpleNamespace(
                returncode=0, stdout=json.dumps(identity_payload), stderr=""
            ),
        ):
            self.assertIn(
                "source_record_input_fingerprint is stale",
                EVIDENCE.source_record_current_input_fingerprint_error(
                    self.paper_dir, audit_payload
                ),
            )


if __name__ == "__main__":
    unittest.main()
