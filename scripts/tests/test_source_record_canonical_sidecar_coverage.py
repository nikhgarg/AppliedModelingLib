#!/usr/bin/env python3
"""Focused tests for canonical source-record sidecar coverage discipline."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
from scripts import audit_repository as REPOSITORY  # noqa: E402
from scripts import source_record_authenticated_overlay_union as UNION  # noqa: E402
from scripts import source_record_current_revalidation as CURRENT  # noqa: E402
from scripts import source_record_differential_revalidation as DIFFERENTIAL  # noqa: E402
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


PAPER = "FixturePaper"
PROMPT = "source-record-v10-semantic-conclusion-boundary-contract"
SOURCE_RECORD_AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)
SOURCE_RECORD_AUDIT_SPEC = importlib.util.spec_from_file_location(
    "canonical_sidecar_coverage_source_record_audit", SOURCE_RECORD_AUDIT_HELPER
)
assert SOURCE_RECORD_AUDIT_SPEC is not None and SOURCE_RECORD_AUDIT_SPEC.loader is not None
SOURCE_RECORD_AUDIT = importlib.util.module_from_spec(SOURCE_RECORD_AUDIT_SPEC)
sys.modules[SOURCE_RECORD_AUDIT_SPEC.name] = SOURCE_RECORD_AUDIT
SOURCE_RECORD_AUDIT_SPEC.loader.exec_module(SOURCE_RECORD_AUDIT)


def raw_item(key: str, input_type: str, result_type: str) -> dict[str, object]:
    """Minimal generated raw item sufficient for the structural group ledger."""

    return {
        "judgment_key": key,
        "kind": "boundary_input",
        "expanded_input_type": input_type,
        "expanded_lean_surface": {
            "input_type": input_type,
            "result_type": result_type,
        },
        "semantic_obligation_tag": result_type,
    }


def raw_audit() -> dict[str, object]:
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "boundary_input_items": [
            raw_item("first current group", "P", "Q"),
            raw_item("second current group", "R", "S"),
        ],
        "lean_check": {"returncode": 0},
    }
    stamp_source_record_audit_receipts(payload)
    return payload


class CanonicalSourceRecordSidecarCoverageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.paper_dir = Path(self.temporary.name) / "papers" / PAPER
        (self.paper_dir / "audit").mkdir(parents=True)
        self.sidecar_path = self.paper_dir / "audit" / "source_record_match_llm.json"
        self.raw = raw_audit()
        self.expected = {"first current group", "second current group"}

    def coverage_error(
        self,
        sidecar: dict[str, object],
        effective_keys: set[str],
        *,
        effective_items: dict[str, object] | None = None,
        primary_closeout_source_record_receipt: bool = False,
    ) -> str:
        return EVIDENCE.canonical_source_record_sidecar_effective_coverage_error(
            self.raw,
            sidecar,
            effective_items=(
                effective_items
                if effective_items is not None
                else {key: {} for key in effective_keys}
            ),
            paper_dir=self.paper_dir,
            sidecar_path=self.sidecar_path,
            primary_closeout_source_record_receipt=(
                primary_closeout_source_record_receipt
            ),
        )

    def manual_complement_provenance(self) -> dict[str, object]:
        return {
            "schema": 1,
            "policy_version": (
                "source-record-v10-manual-current-complement-v3"
            ),
            "completed_template_review_scope": (
                "all_current_generated_groups_without_authenticated_overlay"
            ),
            "current_source_record_audit_sha256": self.raw[
                "source_record_audit_sha256"
            ],
            "generated_judgment_keys_sha256": EVIDENCE.canonical_json_digest(
                sorted(self.expected)
            ),
            "template_reviewer": "fixture reviewer",
            "template_validated_at": "2026-08-13T00:00:00Z",
            "output_sidecar_path": "audit/source_record_match_llm.json",
        }

    def selected_revalidation_provenance(self) -> dict[str, object]:
        """Minimal marker; replay remains the authority in the shared gate."""

        return {"schema": 1, "policy_version": "fixture-selected-rebind"}

    def current_response(self) -> dict[str, object]:
        return {
            "classification": "validated_source_assumption",
            "prompt_version": PROMPT,
            "source_record_audit_sha256": self.raw["source_record_audit_sha256"],
            "validator": "fixture reviewer",
            "validated_at": "2026-08-13T00:00:00Z",
        }

    def loaded_differential_response(self) -> dict[str, object]:
        return DIFFERENTIAL._LoadedSourceRecordDifferentialRevalidationItem(  # type: ignore[attr-defined]
            {
                **self.current_response(),
                DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD: {
                    "schema": 1
                },
            }
        )

    def authenticated_differential_lane(
        self, items: dict[str, dict[str, object]]
    ) -> UNION.AuthenticatedCurrentOverlayLane:
        return UNION.AuthenticatedCurrentOverlayLane(
            label="differential",
            items=items,
            _loader_token=UNION._LOADED_LANE_SENTINEL,
            _is_loaded=(
                DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item
            ),
            _copy_loaded=(
                DIFFERENTIAL.copy_loaded_source_record_differential_revalidation_item
            ),
            _issued_items=list(items.values()),
        )

    def test_complete_canonical_sidecar_needs_no_complement_marker(self) -> None:
        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {key: {} for key in self.expected},
        }
        self.assertEqual(self.coverage_error(sidecar, set()), "")

    def test_marked_complement_accepts_exact_authenticated_effective_coverage(self) -> None:
        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": {}},
            "manual_current_complement": self.manual_complement_provenance(),
        }
        self.assertEqual(self.coverage_error(sidecar, self.expected), "")

    def test_primary_closeout_receipt_discharges_only_missing_runtime_strict_rows(self) -> None:
        """A downstream reader need not duplicate runtime-only strict receipts."""

        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": {}},
            "manual_current_complement": self.manual_complement_provenance(),
        }
        self.assertIn(
            "does not have exact authenticated effective coverage",
            self.coverage_error(sidecar, {"first current group"}),
        )
        self.assertEqual(
            self.coverage_error(
                sidecar,
                {"first current group"},
                primary_closeout_source_record_receipt=True,
            ),
            "",
        )

    def test_completed_legacy_complement_provenance_remains_structurally_valid(self) -> None:
        for policy_version in (
            "source-record-v10-manual-current-complement-v1",
            "source-record-v10-manual-current-complement-v2",
        ):
            with self.subTest(policy_version=policy_version):
                provenance = self.manual_complement_provenance()
                provenance["policy_version"] = policy_version
                sidecar = {
                    "schema": 1,
                    "paper": PAPER,
                    "items": {"first current group": {}},
                    "manual_current_complement": provenance,
                }
                self.assertEqual(self.coverage_error(sidecar, self.expected), "")

    def test_selected_rebind_accepts_only_a_replayed_exact_union(self) -> None:
        """A selected rebind supersedes stale inherited manual provenance only by replay."""

        stale_manual = self.manual_complement_provenance()
        stale_manual["current_source_record_audit_sha256"] = "0" * 64
        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": self.current_response()},
            "manual_current_complement": stale_manual,
            "current_selected_semantic_revalidation": (
                self.selected_revalidation_provenance()
            ),
        }
        with mock.patch.object(
            CURRENT, "validate_selected_rebound_sidecar", return_value=[]
        ) as replay:
            self.assertEqual(self.coverage_error(sidecar, self.expected), "")
        replay.assert_called_once()

        with mock.patch.object(
            CURRENT,
            "validate_selected_rebound_sidecar",
            return_value=["attestation bytes changed"],
        ):
            self.assertIn(
                "not an authenticated selected-plus-overlay union",
                self.coverage_error(sidecar, self.expected),
            )

    def test_full_authenticated_overlay_supersedes_stale_selected_marker(self) -> None:
        """An exact current overlay needs no impossible empty selected rebind."""

        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": {}},
            "current_selected_semantic_revalidation": (
                self.selected_revalidation_provenance()
            ),
        }
        effective_items = {
            key: self.loaded_differential_response() for key in self.expected
        }
        with mock.patch.object(
            CURRENT,
            "validate_selected_rebound_sidecar",
            side_effect=AssertionError("stale selected provenance must not be replayed"),
        ):
            self.assertEqual(
                self.coverage_error(
                    sidecar,
                    self.expected,
                    effective_items=effective_items,
                ),
                "",
            )

    def test_full_overlay_path_rejects_plain_response_for_an_omitted_slot(self) -> None:
        """Coverage cannot infer overlay provenance from current-looking JSON."""

        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": {}},
            "current_selected_semantic_revalidation": (
                self.selected_revalidation_provenance()
            ),
        }
        effective_items = {
            "first current group": self.loaded_differential_response(),
            "second current group": self.current_response(),
        }
        with mock.patch.object(
            CURRENT,
            "validate_selected_rebound_sidecar",
            return_value=["stale selected attestation"],
        ):
            self.assertIn(
                "not an authenticated selected-plus-overlay union",
                self.coverage_error(
                    sidecar,
                    self.expected,
                    effective_items=effective_items,
                ),
            )

    def test_selected_rebind_union_reaches_generator_and_repository_consumers(self) -> None:
        """Both independent readers count the replayed selected-plus-overlay union."""

        stale_manual = self.manual_complement_provenance()
        stale_manual["current_source_record_audit_sha256"] = "0" * 64
        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_audit_sha256": self.raw["source_record_audit_sha256"],
            "validator": "fixture reviewer",
            "validated_at": "2026-08-13T00:00:00Z",
            "items": {"first current group": self.current_response()},
            "manual_current_complement": stale_manual,
            "current_selected_semantic_revalidation": (
                self.selected_revalidation_provenance()
            ),
        }
        self.sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
        overlay = {"second current group": self.loaded_differential_response()}
        lane = self.authenticated_differential_lane(overlay)
        with (
            mock.patch.object(
                CURRENT, "validate_selected_rebound_sidecar", return_value=[]
            ),
            mock.patch.object(
                UNION,
                "load_authenticated_current_overlay_lanes",
                return_value=(lane,),
            ),
            mock.patch.object(
                SOURCE_RECORD_AUDIT,
                "source_record_overlay_labels_with_artifacts",
                return_value=("differential",),
            ),
            mock.patch.object(
                REPOSITORY,
                "source_record_overlay_labels_with_artifacts",
                return_value=("differential",),
            ),
            mock.patch.object(
                CONCLUSION,
                "source_record_overlay_labels_with_artifacts",
                return_value=("differential",),
            ),
            mock.patch.object(
                CONCLUSION,
                "PAPERS",
                self.paper_dir.parent,
            ),
        ):
            summary_items = SOURCE_RECORD_AUDIT.current_source_record_judgments(
                self.paper_dir, PAPER, self.raw
            )
            repository_items = REPOSITORY.source_record_judgment_items(
                self.sidecar_path,
                PAPER,
                current_raw_audit=self.raw,
                paper_dir=self.paper_dir,
            )
            conclusion_items = CONCLUSION.current_judgments(PAPER, self.raw)

        self.assertEqual(set(summary_items), self.expected)
        self.assertEqual(set(repository_items), self.expected)
        self.assertEqual(set(conclusion_items), self.expected)

    def test_unlabelled_partial_fragment_is_rejected_even_if_an_overlay_fills_it(self) -> None:
        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": {}},
        }
        self.assertIn(
            "unlabelled partial fragment",
            self.coverage_error(sidecar, self.expected),
        )

    def test_integrity_gate_reports_an_unlabelled_canonical_fragment(self) -> None:
        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": {}},
        }
        (self.paper_dir / "status.json").write_text(
            json.dumps({"status": "formalized"}), encoding="utf-8"
        )
        (self.paper_dir / "audit" / "source_record_audit.json").write_text(
            json.dumps(self.raw), encoding="utf-8"
        )
        self.sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
        (self.paper_dir / "audit" / "paper_statement_map.json").write_text(
            json.dumps({"items": {}}), encoding="utf-8"
        )

        with (
            mock.patch.object(
                EVIDENCE, "source_record_audit_identity_error", return_value=""
            ),
            mock.patch.object(
                EVIDENCE,
                "current_source_record_judgment_items",
                return_value={key: {} for key in self.expected},
            ),
        ):
            findings = EVIDENCE.check_source_record_judgments(
                self.paper_dir, "formalized"
            )

        self.assertEqual(len(findings), 1)
        self.assertIn("unlabelled partial fragment", findings[0].message)

    def test_repository_loader_fails_closed_for_an_unlabelled_fragment(self) -> None:
        """Standalone repository checks cannot bypass the evidence gate."""

        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "items": {"first current group": {}},
        }
        self.sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")

        with mock.patch.object(
            REPOSITORY,
            "source_record_overlay_labels_with_artifacts",
            return_value=(),
        ):
            loaded = REPOSITORY.source_record_judgment_items(
                self.sidecar_path,
                PAPER,
                current_raw_audit=self.raw,
                paper_dir=self.paper_dir,
            )

        self.assertEqual(loaded, {})


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
