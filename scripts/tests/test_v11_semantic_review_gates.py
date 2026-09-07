#!/usr/bin/env python3
"""Adversarial regressions for the v11 raw semantic-review closeout gates."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as integrity  # noqa: E402
from scripts import reissue_library_semantic_review as library_reissue  # noqa: E402
from scripts import reissue_v11_raw_source_spec_screening as reissue  # noqa: E402
from scripts import review_dashboard  # noqa: E402
from scripts import review_dashboard_packet  # noqa: E402
from scripts import semantic_review_decision_queue as review_decision_queue  # noqa: E402
from scripts.current_closeout import review_surface  # noqa: E402
from scripts.semantic_prerequisite_projection import (  # noqa: E402
    V11_LEAN_TARGET_PROTOCOL,
)
from scripts.lean_signature_manifest import (  # noqa: E402
    DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL,
    TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL,
    TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL,
    parse_direct_library_dependency_surface_output,
    parse_transparent_paper_declaration_display_output,
    parse_transparent_library_declaration_display_output,
)


def digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def canonical_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


class _Dashboard:
    def __init__(self, *, kind: str = "def") -> None:
        self.kind = kind

    def parse_review_source_declarations(self, _path: Path) -> list[tuple[object, ...]]:
        return [
            (
                self.kind,
                "SourceSpec",
                "Fixture.SourceSpec",
                "def SourceSpec : Prop := True",
                None,
                1,
                Path("PaperInterface.lean"),
            )
        ]

    @staticmethod
    def source_semantic_input_bundle(
        _record: object, *, require_context_roles: bool
    ) -> tuple[str, str, str]:
        assert require_context_roles
        return "verbatim source", digest("verbatim source"), ""

    @staticmethod
    def source_anchor_file_error(_folder: Path, _record: object) -> str:
        return ""

    @staticmethod
    def statement_digest(value: str) -> str:
        return digest(value)

    @staticmethod
    def human_review_library_prerequisites(
        _folder: Path,
        _claims: object,
        *,
        require_build: bool = True,
        semantic_targets_override: object | None = None,
        semantic_target_errors_override: object | None = None,
    ) -> list[object]:
        return []


class V11RawSemanticReviewGateTests(unittest.TestCase):
    def setUp(self) -> None:
        source = "verbatim source"
        self.item = {
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": source,
                    "quoted_text_sha256": digest(source),
                }
            ],
            "semantic_contract": {
                "spec_declaration": "Fixture.SourceSpec",
                "evidence_declaration": "Fixture.SourceProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        }

    @staticmethod
    def _semantic_target() -> dict[str, object]:
        atoms = [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {"tag": "const", "name": "True"},
                "display": "True",
            }
        ]
        semantic_atoms = [
            {key: value for key, value in atom.items() if key != "display"}
            for atom in atoms
        ]
        return {
            "display": "True",
            "display_sha256": digest("True"),
            "paper_interface_sha256": digest(""),
            "lean_target_protocol": V11_LEAN_TARGET_PROTOCOL,
            "review_claim_manifest_sha256": digest("claim manifest"),
            "review_claim_atoms_sha256": canonical_digest(
                {"schema": 1, "atoms": semantic_atoms}
            ),
            "review_claim_atoms": atoms,
            "library_declarations": (),
        }

    def _lean_surface(
        self,
        *,
        semantic_target: dict[str, object] | None = None,
        paper_prerequisites: list[dict[str, object]] | None = None,
        library_prerequisites: list[dict[str, object]] | None = None,
    ) -> object:
        return integrity._V11LeanReviewSurface(
            semantic_targets={
                "Fixture.SourceSpec": {
                    **self._semantic_target(),
                    **(semantic_target or {}),
                }
            },
            paper_prerequisites=tuple(paper_prerequisites or []),
            library_prerequisites=tuple(library_prerequisites or []),
            source_declarations={
                "Fixture.SourceSpec": {
                    "declaration_kind": "definition",
                    "is_transparent_definition": True,
                    "type_display": "Prop",
                    "source": "def SourceSpec : Prop := True",
                }
            },
            library_source_declarations={},
            semantic_contracts={},
            declaration_inventory={},
            module_sources={},
            build_input_provider=object(),
        )

    def _screening(self, *, judgment: str = "matches") -> dict[str, object]:
        source = "verbatim source"
        _source_text, source_bundle_sha256, source_error = (
            reissue.source_semantic_input_bundle(
                self.item, require_context_roles=True
            )
        )
        self.assertEqual(source_error, "")
        semantic_target = self._semantic_target()
        review_target = reissue.source_review_target_text(semantic_target)
        return {
            "schema": reissue.SCREENING_SCHEMA,
            "paper": "Fixture",
            "prompt_version": reissue.PROMPT_VERSION,
            "validator": "independent semantic reviewer",
            "validated_at": "2026-08-17T00:00:00Z",
            "items": {
                "Fixture.SourceSpec": {
                    "judgment": judgment,
                    "reason": "The raw source assertion and full proposition agree.",
                    "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                    "source_input_bundle_sha256": source_bundle_sha256,
                    "paper_statement_sha256": digest(source),
                    "lean_target_protocol": V11_LEAN_TARGET_PROTOCOL,
                    "semantic_target_declaration": "Fixture.SourceSpec",
                    "lean_expanded_statement_sha256": digest("True"),
                    "review_claim_manifest_sha256": semantic_target[
                        "review_claim_manifest_sha256"
                    ],
                    "review_claim_atoms_sha256": semantic_target[
                        "review_claim_atoms_sha256"
                    ],
                    "source_review_target_sha256": digest(review_target),
                    "paper_interface_sha256": digest(""),
                }
            },
        }

    def _findings(
        self,
        screening: dict[str, object],
        *,
        dashboard: _Dashboard | None = None,
        proof_items: dict[str, object] | None = None,
        paper_prerequisites: list[dict[str, object]] | None = None,
        semantic_target: dict[str, object] | None = None,
    ) -> list[object]:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "source.txt").write_text("verbatim source\n", encoding="utf-8")
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}", encoding="utf-8"
            )
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "direct_spec_dependency_surface": {
                            "schema": 1,
                            "protocol": "lean-elaborated-direct-library-dependencies-v1",
                            "paper_interface_sha256": digest(""),
                            "items": {
                                "Fixture.SourceSpec": {
                                    "spec_source_sha256": digest(
                                        "def SourceSpec : Prop := True"
                                    ),
                                    "direct_library_declarations": [],
                                    "review_owner_declarations": [],
                                }
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "v11_raw_source_spec_screening.json").write_text(
                json.dumps(screening), encoding="utf-8"
            )
            selected_target = {
                **self._semantic_target(),
                **(semantic_target or {}),
            }
            selected_dashboard = dashboard or _Dashboard()
            selected_kind = selected_dashboard.kind
            selected_paper_prerequisites = paper_prerequisites or []
            selected_library_prerequisites = (
                selected_dashboard.human_review_library_prerequisites(
                    folder,
                    [
                        {
                            "library_review_owner_declarations": list(
                                prerequisite.get(
                                    "direct_library_declarations", ()
                                )
                            )
                        }
                        for prerequisite in selected_paper_prerequisites
                    ],
                    require_build=False,
                    semantic_targets_override={},
                    semantic_target_errors_override={},
                )
            )
            lean_surface = integrity._V11LeanReviewSurface(
                semantic_targets={"Fixture.SourceSpec": selected_target},
                paper_prerequisites=tuple(selected_paper_prerequisites),
                library_prerequisites=tuple(selected_library_prerequisites),
                source_declarations={
                    "Fixture.SourceSpec": {
                        "declaration_kind": (
                            "definition" if selected_kind == "def" else selected_kind
                        ),
                        "is_transparent_definition": selected_kind == "def",
                        "type_display": "Prop",
                        "source": "def SourceSpec : Prop := True",
                    }
                },
                library_source_declarations={},
                semantic_contracts={},
                declaration_inventory={},
                module_sources={},
                build_input_provider=object(),
            )
            with mock.patch.object(
                integrity, "source_spec_correspondence_requested", return_value=True
            ), mock.patch.object(
                integrity,
                "_source_map_proof_obligation_items",
                return_value=(proof_items or {"source_claim": self.item}, ""),
            ), mock.patch.object(
                integrity,
                "_v11_lean_review_surface",
                return_value=lean_surface,
            ):
                return integrity.v11_raw_source_spec_screening_findings(
                    folder, "formalized"
                )

    def test_current_raw_source_and_direct_spec_pass(self) -> None:
        self.assertEqual(self._findings(self._screening()), [])

    def test_paperinterface_prose_claim_is_a_direct_proof_obligation(self) -> None:
        """A displayed Spec cannot fall out merely because source prose is unnumbered."""

        payload = {
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "unnumbered_consequence": {
                    "source_kind": "prose_assertion",
                    "claim_bearing": True,
                    "semantic_contract": dict(self.item["semantic_contract"]),
                }
            },
        }
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["SourceSpec"]
                        }
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    integrity,
                    "source_index_byte_pinned_anchor_item_ids",
                    return_value=set(),
                ),
            ):
                selected, error = integrity._source_map_proof_obligation_items(
                    folder, payload
                )

        self.assertEqual(error, "")
        self.assertEqual(set(selected), {"unnumbered_consequence"})

    def test_support_only_paperinterface_spec_is_not_a_paper_claim(self) -> None:
        payload = {
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "proof_support": {
                    "source_kind": "prose_assertion",
                    "source_status": "support_only",
                    "claim_bearing": True,
                    "semantic_contract": dict(self.item["semantic_contract"]),
                }
            },
        }
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["SourceSpec"]
                        }
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    integrity,
                    "source_index_byte_pinned_anchor_item_ids",
                    return_value=set(),
                ),
            ):
                selected, error = integrity._source_map_proof_obligation_items(
                    folder, payload
                )

        self.assertEqual(error, "")
        self.assertEqual(selected, {})

    def test_unrelated_paperinterface_edit_does_not_stale_exact_spec_review(self) -> None:
        screening = self._screening()
        screening["items"]["Fixture.SourceSpec"]["paper_interface_sha256"] = digest(
            "older whole file"
        )
        self.assertEqual(self._findings(screening), [])

    def test_current_v11_lane_supersedes_a_historical_v10_record(self) -> None:
        """The selected direct lane needs no manufactured legacy reissue."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            # This is intentionally stale/malformed.  A current direct lane
            # is what must decide whether it can still block closeout.
            (folder / "audit" / "source_record_audit.json").write_text(
                "{}", encoding="utf-8"
            )
            with mock.patch.object(
                integrity,
                "v11_direct_semantic_review_state",
                return_value=(True, ""),
            ):
                findings = integrity.check_source_record_judgments(
                    folder, "formalized"
                )
        self.assertEqual(findings, [])

    def test_current_v11_lane_supersedes_legacy_semantic_target_labels(self) -> None:
        """One current v11 target decision cannot be reopened by the v10 sidecar."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            (audit / "source_record_audit.json").write_text(
                json.dumps(
                    {
                        "prompt_version": (
                            integrity.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
                        ),
                        "semantic_model_items": [
                            {
                                "judgment_key": "semantic-model::fixture",
                                "dimensions": [{"id": "carrier_and_domain"}],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    integrity,
                    "current_source_record_judgment_items",
                    return_value={
                        "semantic-model::fixture": {
                            "semantic_model_dimensions": {
                                "carrier_and_domain": {}
                            }
                        }
                    },
                ),
                mock.patch.object(
                    integrity,
                    "v11_direct_semantic_review_state",
                    return_value=(True, ""),
                ),
                mock.patch.object(
                    integrity,
                    "semantic_target_disposition_errors",
                    side_effect=AssertionError(
                        "a current v11 lane must suppress the duplicate v10 target check"
                    ),
                ),
            ):
                findings = integrity.source_record_semantic_target_disposition_findings(
                    folder, "formalized"
                )
        self.assertEqual(findings, [])

    def test_incomplete_v11_lane_retains_legacy_semantic_target_labels(self) -> None:
        """The replacement is fail-closed when its own source screen is incomplete."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            (audit / "source_record_audit.json").write_text(
                json.dumps(
                    {
                        "prompt_version": (
                            integrity.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
                        ),
                        "semantic_model_items": [
                            {
                                "judgment_key": "semantic-model::fixture",
                                "dimensions": [{"id": "carrier_and_domain"}],
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    integrity,
                    "current_source_record_judgment_items",
                    return_value={
                        "semantic-model::fixture": {
                            "semantic_model_dimensions": {
                                "carrier_and_domain": {}
                            }
                        }
                    },
                ),
                mock.patch.object(
                    integrity,
                    "v11_direct_semantic_review_state",
                    return_value=(False, "screening is incomplete"),
                ),
                mock.patch.object(
                    integrity,
                    "semantic_target_disposition_errors",
                    return_value=["legacy target error"],
                ) as target_errors,
            ):
                findings = integrity.source_record_semantic_target_disposition_findings(
                    folder, "formalized"
                )
        target_errors.assert_called_once()
        self.assertTrue(
            any("legacy target error" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_incomplete_v11_lane_does_not_suppress_legacy_currentness(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            (folder / "audit" / "source_record_audit.json").write_text(
                "{}", encoding="utf-8"
            )
            with mock.patch.object(
                integrity,
                "v11_direct_semantic_review_state",
                return_value=(False, "missing raw source/Spec row"),
            ):
                findings = integrity.check_source_record_judgments(
                    folder, "formalized"
                )
        self.assertTrue(findings)

    def test_mismatch_and_stale_hash_block_closeout(self) -> None:
        screening = self._screening(judgment="mismatch")
        row = screening["items"]["Fixture.SourceSpec"]  # type: ignore[index]
        assert isinstance(row, dict)
        row["lean_expanded_statement_sha256"] = digest("old statement")
        messages = [finding.message for finding in self._findings(screening)]
        self.assertTrue(any("stale for Lean's current expanded semantic target" in message for message in messages))
        self.assertTrue(any("judgment is `mismatch`" in message for message in messages))

    def test_claim_role_change_invalidates_source_review(self) -> None:
        screening = self._screening()
        row = screening["items"]["Fixture.SourceSpec"]  # type: ignore[index]
        assert isinstance(row, dict)
        row["review_claim_atoms_sha256"] = digest("old claim roles")
        messages = [finding.message for finding in self._findings(screening)]
        self.assertTrue(
            any("premise/conclusion roles" in message for message in messages)
        )

    def test_review_target_pretty_trace_does_not_own_semantic_currentness(self) -> None:
        """The expanded Lean target and protocol, not trace bytes, own reuse."""

        screening = self._screening()
        row = screening["items"]["Fixture.SourceSpec"]  # type: ignore[index]
        assert isinstance(row, dict)
        row["source_review_target_sha256"] = "f" * 64
        self.assertEqual(self._findings(screening), [])

        row["source_review_target_sha256"] = "invalid"
        messages = [finding.message for finding in self._findings(screening)]
        self.assertTrue(
            any("review-target trace" in message for message in messages),
            messages,
        )

    def test_definition_review_row_binds_actual_definition_target(self) -> None:
        screening = self._screening()
        row = screening["items"]["Fixture.SourceSpec"]  # type: ignore[index]
        assert isinstance(row, dict)
        row["lean_target_protocol"] = (
            review_dashboard_packet.V11_DEFINITION_TARGET_PROTOCOL
        )
        row["semantic_review_declaration"] = "Fixture.sourceDefinition"
        target = {
            "display_sha256": digest("True"),
            "paper_interface_sha256": digest(""),
            "lean_target_protocol": (
                review_dashboard_packet.V11_DEFINITION_TARGET_PROTOCOL
            ),
            "semantic_review_declaration": "Fixture.sourceDefinition",
        }
        self.assertEqual(
            self._findings(screening, semantic_target=target),
            [],
        )
        del row["semantic_review_declaration"]
        messages = [
            finding.message
            for finding in self._findings(screening, semantic_target=target)
        ]
        self.assertTrue(
            any("reviews a different Lean declaration" in message for message in messages)
        )

    def test_approved_corrected_target_requires_an_explicit_pinned_record(self) -> None:
        screening = self._screening(judgment="matches_approved_corrected_target")
        messages = [finding.message for finding in self._findings(screening)]
        self.assertTrue(
            any("lacks a corrected-source map record" in message for message in messages)
        )

        corrected = dict(self.item)
        corrected["coverage_status"] = "corrected_source_statement"
        corrected["corrected_target"] = {
            "archival_equivalence_claimed": False,
            "corrected_target_sha256": "a" * 64,
        }
        row = screening["items"]["Fixture.SourceSpec"]  # type: ignore[index]
        assert isinstance(row, dict)
        row["corrected_target_protocol"] = "approved_corrected_target_v1"
        row["corrected_target_sha256"] = "a" * 64
        self.assertEqual(
            self._findings(screening, proof_items={"source_claim": corrected}), []
        )

    def test_corrected_source_statement_cannot_be_relabelled_as_matches(self) -> None:
        corrected = dict(self.item)
        corrected["coverage_status"] = "corrected_source_statement"
        corrected["corrected_target"] = {
            "archival_equivalence_claimed": False,
            "corrected_target_sha256": "a" * 64,
        }
        messages = [
            finding.message
            for finding in self._findings(
                self._screening(judgment="matches"),
                proof_items={"source_claim": corrected},
            )
        ]
        self.assertTrue(
            any("corrected_source_statement requires" in message for message in messages)
        )

    def test_wrapper_or_proof_endpoint_cannot_be_screened_as_spec(self) -> None:
        messages = [
            finding.message
            for finding in self._findings(
                self._screening(), dashboard=_Dashboard(kind="theorem")
            )
        ]
        self.assertTrue(
            any(
                "transparent `def ...Spec : Prop :=`" in message
                for message in messages
            )
        )

    def test_two_source_claims_cannot_share_one_spec(self) -> None:
        messages = [
            finding.message
            for finding in self._findings(
                self._screening(),
                proof_items={"first": self.item, "second": self.item},
            )
        ]
        self.assertTrue(any("one semantic Spec per source claim" in message for message in messages))

    def test_paper_prerequisite_and_its_library_cannot_bypass_review(self) -> None:
        """A retained paper model and its library meaning are both closeout gates."""

        class PrerequisiteLibraryDashboard(_Dashboard):
            @staticmethod
            def human_review_library_prerequisites(
                _folder: Path,
                claims: object,
                *,
                require_build: bool = True,
                semantic_targets_override: object | None = None,
                semantic_target_errors_override: object | None = None,
            ) -> list[dict[str, object]]:
                for claim in claims:  # type: ignore[union-attr]
                    names = claim.get("library_review_owner_declarations", ())
                    if "AppliedModelingLib.Example.onlyThroughPaperModel" in names:
                        return [
                            {
                                "lean_name": "AppliedModelingLib.Example.onlyThroughPaperModel",
                                "semantic_current": False,
                                "semantic_judgment": "not recorded",
                                "semantic_status": "no source-to-library review",
                            }
                        ]
                return []

        messages = [
            finding.message
            for finding in self._findings(
                self._screening(),
                dashboard=PrerequisiteLibraryDashboard(),
                paper_prerequisites=[
                    {
                        "lean_name": "Fixture.SourceModel",
                        "paper_declaration_source": "def SourceModel := True",
                        "paper_semantic_target": "True",
                        "semantic_current": False,
                        "semantic_judgment": "matches",
                        "direct_library_declarations": [
                            "AppliedModelingLib.Example.onlyThroughPaperModel"
                        ],
                    }
                ],
            )
        ]
        self.assertTrue(
            any("paper-local semantic prerequisite has no current raw-source review" in m for m in messages)
        )
        self.assertTrue(
            any("Lean-expanded semantic target has no current raw-source library review" in m for m in messages)
        )

    def test_reissue_writer_refuses_a_wrapper_target(self) -> None:
        with mock.patch.object(
            reissue,
            "source_semantic_input_bundle",
            return_value=("verbatim source", digest("verbatim source"), ""),
        ), mock.patch.object(
            reissue,
            "source_anchor_file_error",
            return_value="",
        ):
            with self.assertRaisesRegex(reissue.ScreeningReissueError, "explicit `def"):
                reissue.reissued_row(
                    "Fixture.SourceSpec",
                    paper_dir=Path("."),
                    source_item="source_claim",
                    record={},
                    interface_item={
                        "kind": "theorem",
                        "lean_statement": "theorem SourceSpec : True := by trivial",
                    },
                    semantic_target={
                        **self._semantic_target(),
                        "display": "True",
                        "display_sha256": digest("True"),
                        "paper_interface_sha256": digest(""),
                    },
                    decision={
                        "source_item": "source_claim",
                        "judgment": "matches",
                        "reason": "not used",
                    },
                )

    def test_reissue_cli_requires_current_v11_graph(self) -> None:
        """Current review writers never accept a presentation cache as authority."""

        with tempfile.TemporaryDirectory() as temp_dir:
            args = SimpleNamespace(
                root=Path(temp_dir),
                paper="Fixture",
                v11_review_graph=False,
                emit_template=None,
                decisions=None,
                validator="",
                replace_current_surface=False,
                write=False,
            )
            with mock.patch.object(reissue, "parse_args", return_value=args):
                with self.assertRaisesRegex(
                    reissue.ScreeningReissueError,
                    "requires --v11-review-graph",
                ):
                    reissue.main()

    def test_reissue_writer_records_definition_review_declaration(self) -> None:
        with mock.patch.object(
            reissue,
            "source_semantic_input_bundle",
            return_value=("verbatim source", digest("verbatim source"), ""),
        ), mock.patch.object(
            reissue,
            "source_anchor_file_error",
            return_value="",
        ):
            row = reissue.reissued_row(
                "Fixture.SourceSpec",
                paper_dir=Path("."),
                source_item="source_claim",
                record={},
                interface_item={
                    "kind": "def",
                    "lean_statement": "def SourceSpec : Prop := True",
                },
                semantic_target={
                    **self._semantic_target(),
                    "display": "fun input => input",
                    "display_sha256": digest("fun input => input"),
                    "paper_interface_sha256": digest(""),
                    "lean_target_protocol": (
                        review_dashboard_packet.V11_DEFINITION_TARGET_PROTOCOL
                    ),
                    "semantic_review_declaration": "Fixture.sourceDefinition",
                },
                decision={
                    "source_item": "source_claim",
                    "judgment": "matches",
                    "reason": "The source and actual Lean definition agree.",
                    "_reviewed_semantic_target_sha256": digest(
                        reissue.source_review_target_text(
                            {
                                **self._semantic_target(),
                                "display": "fun input => input",
                                "display_sha256": digest("fun input => input"),
                            }
                        )
                    ),
                    "_reviewed_source_input_bundle_sha256": digest(
                        "verbatim source"
                    ),
                    "_reviewed_declaration_source_sha256": digest(
                        "def SourceSpec : Prop := True"
                    ),
                    "_reviewed_verbatim_source_input_sha256": digest(
                        "verbatim source"
                    ),
                    "_reviewed_declaration_identity": {
                        "review_claim_atoms_sha256": self._semantic_target()[
                            "review_claim_atoms_sha256"
                        ],
                        "review_claim_manifest_sha256": self._semantic_target()[
                            "review_claim_manifest_sha256"
                        ],
                        "lean_expanded_statement_sha256": digest(
                            "fun input => input"
                        ),
                        "lean_target_protocol": (
                            review_dashboard_packet.V11_DEFINITION_TARGET_PROTOCOL
                        ),
                        "semantic_review_declaration": "Fixture.sourceDefinition",
                        "coverage_status": "",
                        "corrected_target_sha256": "",
                    },
                },
            )
        self.assertEqual(
            row["lean_target_protocol"],
            review_dashboard_packet.V11_DEFINITION_TARGET_PROTOCOL,
        )
        self.assertEqual(
            row["semantic_review_declaration"], "Fixture.sourceDefinition"
        )

    def test_v11_decision_queue_binds_exact_source_and_semantic_target(self) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "source_claim": {
                    "semantic_contract": {
                        "spec_declaration": "Fixture.SourceSpec",
                        "evidence_declaration": "Fixture.SourceProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    }
                }
            },
        }
        semantic_target = {
            **self._semantic_target(),
            "display": "True",
            "display_sha256": digest("True"),
            "paper_interface_sha256": digest("interface"),
            "lean_target_protocol": reissue.LEAN_PROTOCOL,
        }
        interface_item = {
            "kind": "def",
            "lean_statement": "def SourceSpec : Prop := True",
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            paper_dir.mkdir()
            with mock.patch.object(
                reissue.review_queue,
                "source_semantic_input_bundle",
                return_value=("verbatim source", digest("verbatim source"), ""),
            ), mock.patch.object(
                reissue.review_queue,
                "source_anchor_file_error",
                return_value="",
            ):
                queue = reissue.decision_template(
                    paper_dir,
                    source_map,
                    {"Fixture.SourceSpec": semantic_target},
                    {"Fixture.SourceSpec": interface_item},
                )
            self.assertEqual(
                queue["review_material"]["declarations"]
                ["Fixture.SourceSpec"]["declaration_identity"],
                {
                    "review_claim_atoms_sha256": semantic_target[
                        "review_claim_atoms_sha256"
                    ],
                    "review_claim_manifest_sha256": semantic_target[
                        "review_claim_manifest_sha256"
                    ],
                    "lean_expanded_statement_sha256": digest("True"),
                    "lean_target_protocol": reissue.LEAN_PROTOCOL,
                    "semantic_review_declaration": "Fixture.SourceSpec",
                    "coverage_status": "",
                    "corrected_target_sha256": "",
                },
            )
            queue["items"]["Fixture.SourceSpec"].update(
                {
                    "judgment": "matches",
                    "reason": "The exact source proposition and expanded Lean target agree.",
                }
            )
            decision_path = paper_dir / "decisions.json"
            decision_path.write_text(json.dumps(queue), encoding="utf-8")
            decisions = reissue._decision_rows(decision_path, paper="Fixture")
            decision = decisions["Fixture.SourceSpec"]
            self.assertEqual(
                reissue.current_decision_queue_error(
                    decision_path,
                    template=queue,
                    paper="Fixture",
                ),
                "",
            )

            with mock.patch.object(
                reissue,
                "source_semantic_input_bundle",
                return_value=("verbatim source", digest("verbatim source"), ""),
            ), mock.patch.object(
                reissue,
                "source_anchor_file_error",
                return_value="",
            ):
                row = reissue.reissued_row(
                    "Fixture.SourceSpec",
                    paper_dir=paper_dir,
                    source_item="source_claim",
                    record=source_map["items"]["source_claim"],
                    interface_item=interface_item,
                    semantic_target=semantic_target,
                    decision=decision,
                )
                with self.assertRaisesRegex(
                    reissue.ScreeningReissueError,
                    "semantic target changed after review",
                ):
                    reissue.reissued_row(
                        "Fixture.SourceSpec",
                        paper_dir=paper_dir,
                        source_item="source_claim",
                        record=source_map["items"]["source_claim"],
                        interface_item=interface_item,
                        semantic_target={
                            **semantic_target,
                            "display": "False",
                            "display_sha256": digest("False"),
                        },
                        decision=decision,
                    )
                changed_atoms = [
                    {
                        **semantic_target["review_claim_atoms"][0],
                        "canonical": {"tag": "const", "name": "False"},
                    }
                ]
                changed_semantic_atoms = [
                    {key: value for key, value in atom.items() if key != "display"}
                    for atom in changed_atoms
                ]
                with self.assertRaisesRegex(
                    reissue.ScreeningReissueError,
                    "Lean declaration identity changed after review",
                ):
                    reissue.reissued_row(
                        "Fixture.SourceSpec",
                        paper_dir=paper_dir,
                        source_item="source_claim",
                        record=source_map["items"]["source_claim"],
                        interface_item=interface_item,
                        semantic_target={
                            **semantic_target,
                            "review_claim_atoms": changed_atoms,
                            "review_claim_atoms_sha256": canonical_digest(
                                {"schema": 1, "atoms": changed_semantic_atoms}
                            ),
                        },
                        decision=decision,
                    )

        self.assertEqual(row["judgment"], "matches")
        self.assertEqual(row["source_item"], "source_claim")

    def test_v11_direct_queue_excludes_graph_prerequisites(self) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "source_claim": {
                    "semantic_contract": {
                        "spec_declaration": "Fixture.SourceSpec",
                        "evidence_declaration": "Fixture.SourceProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    }
                }
            },
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            paper_dir.mkdir()
            with mock.patch.object(
                reissue.review_queue,
                "source_semantic_input_bundle",
                return_value=("verbatim source", digest("verbatim source"), ""),
            ), mock.patch.object(
                reissue.review_queue,
                "source_anchor_file_error",
                return_value="",
            ):
                payload = reissue.decision_template(
                    paper_dir,
                    source_map,
                    {"Fixture.SourceSpec": self._semantic_target()},
                    {
                        "Fixture.SourceSpec": {
                            "kind": "def",
                            "lean_statement": "def SourceSpec : Prop := True",
                        }
                    },
                )
        self.assertNotIn("supporting_declarations", payload["review_material"])

    def test_current_direct_queue_shows_its_lean_selected_model_context(self) -> None:
        """A source reviewer need not infer a model's meaning from its name."""

        source_map = {"paper": "Fixture", "items": {"source_claim": self.item}}
        semantic_target = {
            **self._semantic_target(),
            "prerequisite_declarations": ["Fixture.SourceModel"],
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            paper_dir.mkdir()
            review_graph = SimpleNamespace(
                context=SimpleNamespace(
                    folder=paper_dir.resolve(), statement_map=source_map
                ),
                target_material=lambda: {
                    "semantic_targets": {"Fixture.SourceSpec": semantic_target},
                    "paper_declaration_sources": {
                        "Fixture.SourceSpec": {
                            "paper_declaration_kind": "def",
                            "paper_declaration_source": "def SourceSpec : Prop := True",
                        },
                        "Fixture.SourceModel": {
                            "paper_declaration_source": "structure SourceModel where",
                            "paper_declaration_sha256": digest(
                                "structure SourceModel where"
                            ),
                        },
                    },
                    "paper_prerequisite_targets": {
                        "Fixture.SourceModel": {
                            "display": "type:\nType",
                            "display_sha256": digest("type:\nType"),
                            "direct_paper_declarations": [],
                            "direct_library_declarations": [],
                        }
                    },
                    "library_semantic_targets": {},
                    "library_declaration_sources": {},
                    "library_semantic_target_errors": {},
                },
            )
            with mock.patch.object(
                reissue.review_queue,
                "source_semantic_input_bundle",
                return_value=("verbatim source", digest("verbatim source"), ""),
            ), mock.patch.object(
                reissue.review_queue,
                "source_anchor_file_error",
                return_value="",
            ):
                payload, _path = reissue.current_decision_template_and_path(
                    paper_dir, review_graph=review_graph
                )

        self.assertEqual(
            payload["items"]["Fixture.SourceSpec"]["supporting_declarations"],
            ["Fixture.SourceModel"],
        )
        self.assertEqual(
            set(payload["review_material"]["supporting_declarations"]),
            {"Fixture.SourceModel"},
        )

    def _nested_direct_context(self, *, library: bool = False) -> tuple[dict, dict]:
        """Lean-owned semantic edges, separately from proof/foundation closure."""

        names = ("Fixture.f", "Fixture.g", "Fixture.h")
        targets = {}
        sources = {}
        for index, name in enumerate(names):
            child = names[index + 1:index + 2]
            body = child[0] if child else "False"
            display = f"type:\nProp\n\nvalue:\n{body}"
            code = f"def {name} : Prop := {body}"
            targets[name] = {
                "display": display,
                "display_sha256": digest(display),
                "direct_paper_declarations": [] if library else list(child),
                "direct_library_declarations": list(child) if library else [],
                "erased_proof_declarations": ["Fixture.proofOnly"],
            }
            sources[name] = (
                {"library_definition": code, "library_definition_sha256": digest(code)}
                if library else
                {"paper_declaration_source": code, "paper_declaration_sha256": digest(code)}
            )
        # These are not semantic edges. The queue must not infer new review
        # targets from ordinary foundation or proof-closure metadata.
        material = {
            "semantic_targets": {"Fixture.SourceSpec": {
                **self._semantic_target(),
                "prerequisite_declarations": [] if library else [names[0]],
                "library_declarations": [names[0]] if library else [],
                "erased_proof_declarations": ["Fixture.proofOnly"],
                "foundation_declarations": ["Nat", "False"],
            }},
            "paper_prerequisite_targets": {} if library else targets,
            "library_semantic_targets": targets if library else {},
            "paper_declaration_sources": {
                **({} if library else sources),
                "Fixture.SourceSpec": {
                    "paper_declaration_kind": "def",
                    "paper_declaration_source": "def SourceSpec : Prop := Fixture.f",
                },
                "Fixture.proofOnly": {"paper_declaration_source": "theorem proofOnly : True := trivial"},
            },
            "library_declaration_sources": sources if library else {},
            "library_semantic_target_errors": {},
        }
        return {
            "paper": "Fixture",
            "semantic_route_schema": 2,
            "items": {"claim": self.item},
        }, material

    def test_direct_queue_shows_non_routed_predicate_context_without_extra_judgments(self) -> None:
        for library in (False, True):
            with self.subTest(library=library):
                source_map, material = self._nested_direct_context(library=library)
                with tempfile.TemporaryDirectory() as temporary, mock.patch.object(
                    reissue.review_queue, "source_semantic_input_bundle",
                    return_value=("verbatim source", digest("verbatim source"), ""),
                ), mock.patch.object(reissue.review_queue, "source_anchor_file_error", return_value=""):
                    payload = reissue._current_decision_template(
                        Path(temporary), source_map=source_map, review_targets=material
                    )
                self.assertEqual(set(payload["items"]), {"Fixture.SourceSpec"})
                support = payload["review_material"]["supporting_declarations"]
                self.assertEqual(set(support), {"Fixture.f", "Fixture.g", "Fixture.h"})
                self.assertIn("False", support["Fixture.h"]["semantic_target"])
                self.assertNotIn("Fixture.proofOnly", support)
                self.assertNotIn("Nat", support)
                self.assertNotIn("False", support)

    def test_direct_context_includes_semantics_below_source_routed_boundary(self) -> None:
        for library in (False, True):
            with self.subTest(library=library):
                source_map, material = self._nested_direct_context(library=library)
                source_map["items"]["definition"] = {
                    "source_kind": "definition", "claim_bearing": True,
                    "inventory_role": "source_semantic_declaration",
                    "lean_declarations": ["Fixture.g"],
                }
                source_map[
                    "library_semantic_prerequisite_sources" if library
                    else "paper_semantic_prerequisite_sources"
                ] = {"Fixture.g": "definition"}
                support, by_spec = reissue._direct_review_support(
                    material, material["semantic_targets"]
                )
                self.assertEqual(set(support), {"Fixture.f", "Fixture.g", "Fixture.h"})
                self.assertEqual(by_spec, {"Fixture.SourceSpec": ("Fixture.f", "Fixture.g", "Fixture.h")})
                # Separate review of g does not tell this reviewer what the
                # constructor in its body means. Include h as context, not a row.
                self.assertIn("False", support["Fixture.h"]["semantic_target"])

    def test_direct_context_rejects_unavailable_semantic_child(self) -> None:
        source_map, material = self._nested_direct_context()
        del material["paper_prerequisite_targets"]["Fixture.g"]
        with self.assertRaisesRegex(reissue.ScreeningReissueError, "dependency edge leaves"):
            reissue._direct_review_support(
                material, material["semantic_targets"]
            )

    def test_library_boundary_queue_retains_nested_context_without_helper_rows(self) -> None:
        source_map, material = self._nested_direct_context(library=True)
        source_map["items"]["definition"] = {
            "source_location": "source.txt:1", "source_kind": "definition",
            "claim_bearing": True, "inventory_role": "source_semantic_declaration",
            "lean_declarations": ["Fixture.g"],
        }
        source_map["library_semantic_prerequisite_sources"] = {"Fixture.g": "definition"}
        name = "Fixture.g"
        target = material["library_semantic_targets"][name]
        declaration = material["library_declaration_sources"][name]
        entry = {
            "lean_name": name,
            "library_semantic_target": target["display"],
            "library_semantic_target_sha256": target["display_sha256"],
            "source_item": "definition", "verbatim_source_input": "Source definition.",
            "source_input_bundle_sha256": digest("source bundle"),
            "source_anchor_bundle_sha256": digest("source anchors"),
            "elaborated_signature_sha256": digest("canonical g identity"),
            "library_source_path": "models/Definitions.lean",
            "library_line_start": 1, "library_line_end": 1,
            **declaration,
        }
        with tempfile.TemporaryDirectory() as temporary, mock.patch.object(
            library_reissue.review_queue, "_source_context", return_value={
                "source_locator": "source.txt:1",
                "verbatim_source_input": "Source definition.",
                "verbatim_source_input_sha256": digest("Source definition."),
                "source_input_bundle_sha256": digest("source bundle"),
            }
        ):
            payload = library_reissue._enrich_decision_template(
                {"schema": 1, "paper": "Fixture", "items": {name: {
                    "source_item": "definition", "candidate_source_items": ["definition"],
                    "judgment": "matches", "reason": "The displayed meanings agree.",
                }}},
                paper_dir=Path(temporary), source_map=source_map, entries=[entry],
                review_graph=SimpleNamespace(target_material=lambda: material),
            )
        self.assertEqual(set(payload["items"]), {name})
        support = payload["review_material"]["supporting_declarations"]
        self.assertEqual(
            set(support),
            {
                "Fixture.f",
                "Fixture.g",
                "Fixture.h",
                "source_claim_use:Fixture.SourceSpec",
            },
        )
        self.assertIn("False", support["Fixture.h"]["semantic_target"])
        decisions = library_reissue.review_queue.validated_queue_items(payload, paper="Fixture")
        self.assertEqual(
            decisions[name]["_reviewed_supporting_declarations_sha256"],
            library_reissue.review_queue.selected_supporting_declarations_sha256(
                support, payload["items"][name]["supporting_declarations"]
            ),
        )
        graph = SimpleNamespace(
            context=SimpleNamespace(statement_map=source_map),
            specifications=list(reissue.EvidenceRouteSet.from_source_map(source_map).result_specifications()),
            semantic_targets=material["semantic_targets"],
            paper_prerequisite_targets=material["paper_prerequisite_targets"],
            library_semantic_targets=material["library_semantic_targets"],
            target_material=lambda: material,
            project_library_prerequisites=lambda _folder, *, ledger: [entry],
        )
        with tempfile.TemporaryDirectory() as temporary:
            issued = library_reissue.reissue(
                Path(temporary), decisions, validator="independent reviewer", review_graph=graph
            )
            self.assertEqual(set(issued["items"]), {name})
            # g is unchanged, but its non-routed predicate context is not.
            child = material["library_semantic_targets"]["Fixture.h"]
            child["display"] = "type:\nProp\n\nvalue:\nTrue"
            child["display_sha256"] = digest(child["display"])
            with self.assertRaisesRegex(
                library_reissue.LibraryReviewReissueError, "supporting semantic context changed"
            ):
                library_reissue.reissue(
                    Path(temporary), decisions, validator="independent reviewer", review_graph=graph
                )

    def test_corrected_target_is_displayed_and_part_of_delta_identity(self) -> None:
        target_digest = digest("approved correction")
        approval_excerpt = (
            "The maintainer approved this exact corrected mathematical target "
            "and expressly disclaimed archival equivalence."
        )
        source_map = {
            "paper": "Fixture",
            "items": {
                "source_claim": {
                    "coverage_status": "corrected_source_statement",
                    "source_note": (
                        "The corrected endpoint preserves the advertised result "
                        "under the approved repaired statement."
                    ),
                    "corrected_target": {
                        "statement": "Approved corrected mathematical target.",
                        "corrected_target_sha256": target_digest,
                        "archival_equivalence_claimed": False,
                        "archival_source_locator": "source.txt:10-12",
                        "governing_defect_ids": ["FIXTURE-1"],
                        "approval": {
                            "kind": "explicit_user_instruction",
                            "recorded_at": "2026-09-01",
                            "reference": "Maintainer approval fixture.",
                            "artifact_protocol": (
                                "unique_normalized_artifact_excerpt_v1"
                            ),
                            "artifact_excerpt": approval_excerpt,
                            "artifact_excerpt_sha256": digest(approval_excerpt),
                        },
                    },
                    "semantic_contract": {
                        "spec_declaration": "Fixture.SourceSpec",
                        "evidence_declaration": "Fixture.SourceProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                }
            },
        }
        semantic_target = {
            **self._semantic_target(),
            "display": "True",
            "display_sha256": digest("True"),
            "paper_interface_sha256": digest("interface"),
            "lean_target_protocol": reissue.LEAN_PROTOCOL,
        }
        interface_item = {
            "kind": "def",
            "lean_statement": "def SourceSpec : Prop := True",
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            paper_dir.mkdir()
            with (
                mock.patch.object(
                    reissue.review_queue,
                    "source_semantic_input_bundle",
                    return_value=(
                        "verbatim archival source",
                        digest("source bundle"),
                        "",
                    ),
                ),
                mock.patch.object(
                    reissue.review_queue,
                    "source_anchor_file_error",
                    return_value="",
                ),
            ):
                queue = reissue.decision_template(
                    paper_dir,
                    source_map,
                    {"Fixture.SourceSpec": semantic_target},
                    {"Fixture.SourceSpec": interface_item},
                )
        source_context = queue["review_material"]["source_items"]["source_claim"]
        self.assertEqual(
            source_context["approved_corrected_target"]["statement"],
            "Approved corrected mathematical target.",
        )
        self.assertEqual(
            source_context["approved_corrected_target"]["approval_record"]
            ["artifact_excerpt"],
            approval_excerpt,
        )
        self.assertEqual(
            source_context["approved_corrected_target"]["scope_note"],
            source_map["items"]["source_claim"]["source_note"],
        )
        declaration = queue["review_material"]["declarations"]["Fixture.SourceSpec"]
        identity = declaration["declaration_identity"]
        self.assertEqual(identity["corrected_target_sha256"], target_digest)
        stable_target_digest = source_context["approved_corrected_target"][
            "corrected_target_review_sha256"
        ]
        prior = {
            "source_item": "source_claim",
            "source_input_protocol": reissue.SOURCE_PROTOCOL,
            "source_input_bundle_sha256": digest("source bundle"),
            "paper_statement_sha256": reissue.statement_digest(
                "verbatim archival source"
            ),
            "lean_target_protocol": reissue.LEAN_PROTOCOL,
            "semantic_target_declaration": "Fixture.SourceSpec",
            "lean_expanded_statement_sha256": digest("True"),
            "review_claim_manifest_sha256": identity[
                "review_claim_manifest_sha256"
            ],
            "review_claim_atoms_sha256": identity["review_claim_atoms_sha256"],
            "source_review_target_sha256": declaration[
                "semantic_target_sha256"
            ],
            "judgment": reissue.APPROVED_CORRECTED_TARGET_MATCH,
            "reason": "Reviewed against the displayed approved correction.",
            "corrected_target_protocol": reissue.CORRECTED_TARGET_REVIEW_PROTOCOL,
            "corrected_target_review_sha256": stable_target_digest,
        }
        self.assertTrue(
            reissue._unchanged_screening_judgment(
                prior,
                declaration_context=declaration,
                source_context=source_context,
            )
        )
        renderer_changed = {
            **declaration,
            "semantic_target_sha256": digest("equivalent new renderer output"),
        }
        self.assertTrue(
            reissue._unchanged_screening_judgment(
                prior,
                declaration_context=renderer_changed,
                source_context=source_context,
            )
        )
        renamed_source_navigation = {**prior, "source_item": "old_source_key"}
        self.assertTrue(
            reissue._unchanged_screening_judgment(
                renamed_source_navigation,
                declaration_context=declaration,
                source_context=source_context,
            )
        )
        changed_claim = {
            **declaration,
            "declaration_identity": {
                **identity,
                "lean_expanded_statement_sha256": digest("changed premise"),
            },
        }
        self.assertFalse(
            reissue._unchanged_screening_judgment(
                prior,
                declaration_context=changed_claim,
                source_context=source_context,
            )
        )
        changed_atom_view = {
            **declaration,
            "declaration_identity": {
                **identity,
                "review_claim_atoms_sha256": digest("changed conclusion atom"),
            },
        }
        self.assertTrue(
            reissue._unchanged_screening_judgment(
                prior,
                declaration_context=changed_atom_view,
                source_context=source_context,
            )
        )
        changed_source = {
            **source_context,
            "source_input_bundle_sha256": digest("changed source bundle"),
        }
        self.assertFalse(
            reissue._unchanged_screening_judgment(
                prior,
                declaration_context=declaration,
                source_context=changed_source,
            )
        )
        changed_record_identity = dict(identity)
        changed_record_identity["corrected_target_sha256"] = digest(
            "same correction in a changed aggregate memo"
        )
        self.assertTrue(
            reissue._unchanged_screening_judgment(
                prior,
                declaration_context={
                    **declaration,
                    "declaration_identity": changed_record_identity,
                },
                source_context=source_context,
            )
        )
        changed = dict(prior)
        changed["corrected_target_review_sha256"] = digest("old correction")
        self.assertFalse(
            reissue._unchanged_screening_judgment(
                changed,
                declaration_context=declaration,
                source_context=source_context,
            )
        )

        renamed_queue = {
            "items": {
                "Renamed.SourceSpec": {"source_item": "source_claim"},
            },
            "review_material": {
                "declarations": {"Renamed.SourceSpec": declaration},
                "source_items": {"source_claim": source_context},
            },
        }
        bindings = reissue._current_screening_reuse_bindings(
            renamed_queue,
            {"Fixture.SourceSpec": prior},
        )
        self.assertEqual(
            bindings["Renamed.SourceSpec"][0], "Fixture.SourceSpec"
        )

        collision_queue = {
            "items": {
                name: {"source_item": "source_claim"}
                for name in ("Renamed.FirstSpec", "Renamed.SecondSpec")
            },
            "review_material": {
                "declarations": {
                    name: declaration
                    for name in ("Renamed.FirstSpec", "Renamed.SecondSpec")
                },
                "source_items": {"source_claim": source_context},
            },
        }
        self.assertEqual(
            reissue._current_screening_reuse_bindings(
                collision_queue,
                {"Fixture.SourceSpec": prior},
            ),
            {},
        )

    def test_source_spec_reissue_rebinds_a_unique_semantic_rename(self) -> None:
        old_name = "Fixture.OldSourceSpec"
        new_name = "Fixture.SourceSpec"
        source_item = "source_claim"
        source_text = "verbatim source"
        source_digest = digest("source bundle")
        source_map = {
            "paper": "Fixture",
            "items": {
                source_item: {
                    "coverage_status": "covered",
                    "semantic_contract": {
                        "spec_declaration": new_name,
                        "evidence_declaration": "Fixture.SourceProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                }
            },
        }
        semantic_target = self._semantic_target()
        lean_statement = "def SourceSpec : Prop := True"
        interface_items = {
            new_name: {"kind": "def", "lean_statement": lean_statement}
        }

        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            (paper_dir / "audit").mkdir(parents=True)
            with (
                mock.patch.object(
                    reissue.review_queue,
                    "source_semantic_input_bundle",
                    return_value=(source_text, source_digest, ""),
                ),
                mock.patch.object(
                    reissue.review_queue,
                    "source_anchor_file_error",
                    return_value="",
                ),
                mock.patch.object(
                    reissue,
                    "source_semantic_input_bundle",
                    return_value=(source_text, source_digest, ""),
                ),
                mock.patch.object(
                    reissue,
                    "source_anchor_file_error",
                    return_value="",
                ),
            ):
                queue = reissue.decision_template(
                    paper_dir,
                    source_map,
                    {new_name: semantic_target},
                    interface_items,
                )
                declaration = queue["review_material"]["declarations"][new_name]
                source_context = queue["review_material"]["source_items"][source_item]
                identity = declaration["declaration_identity"]
                prior = {
                    "source_item": "old_source_navigation",
                    "source_input_protocol": reissue.SOURCE_PROTOCOL,
                    "source_input_bundle_sha256": source_digest,
                    "paper_statement_sha256": reissue.statement_digest(source_text),
                    "lean_target_protocol": reissue.LEAN_PROTOCOL,
                    "semantic_target_declaration": old_name,
                    "lean_expanded_statement_sha256": identity[
                        "lean_expanded_statement_sha256"
                    ],
                    "review_claim_manifest_sha256": identity[
                        "review_claim_manifest_sha256"
                    ],
                    "review_claim_atoms_sha256": identity[
                        "review_claim_atoms_sha256"
                    ],
                    "source_review_target_sha256": digest("old target display"),
                    "judgment": "matches",
                    "reason": "The exact source and Lean claim agree.",
                }
                self.assertTrue(
                    reissue._unchanged_screening_judgment(
                        prior,
                        declaration_context=declaration,
                        source_context=source_context,
                    )
                )
                (paper_dir / reissue.SCREENING_RELATIVE).write_text(
                    json.dumps(
                        {
                            "schema": reissue.SCREENING_SCHEMA,
                            "paper": "Fixture",
                            "prompt_version": reissue.PROMPT_VERSION,
                            "validator": "prior reviewer",
                            "validated_at": "2026-08-24T00:00:00+00:00",
                            "items": {old_name: prior},
                        }
                    ),
                    encoding="utf-8",
                )
                review_targets = {
                    "semantic_targets": {new_name: semantic_target},
                    "paper_prerequisite_targets": {},
                    "library_semantic_targets": {},
                    "paper_declaration_sources": {
                        new_name: {
                            "paper_declaration_source": lean_statement,
                            "paper_declaration_kind": "def",
                        }
                    },
                }
                graph = SimpleNamespace(
                    context=SimpleNamespace(
                        folder=paper_dir.resolve(),
                        statement_map=source_map,
                    ),
                    semantic_targets={new_name: semantic_target},
                    target_material=lambda: review_targets,
                )

                payload = reissue.reissue(
                    paper_dir,
                    {},
                    validator="",
                    review_graph=graph,
                )

        self.assertEqual(set(payload["items"]), {new_name})
        self.assertEqual(payload["validator"], "prior reviewer")
        self.assertEqual(payload["items"][new_name]["source_item"], source_item)
        self.assertEqual(
            payload["items"][new_name]["semantic_target_declaration"], new_name
        )
        self.assertEqual(
            payload["items"][new_name]["reason"],
            "The exact source and Lean claim agree.",
        )
        self.assertEqual(
            payload["items"][new_name]["source_review_target_sha256"],
            digest("old target display"),
        )

    def test_source_spec_reuse_requires_reviewer_provenance_not_prompt_spelling(
        self,
    ) -> None:
        row = {"judgment": "matches", "reason": "Exact semantic match."}
        missing_reviewer = {
            "schema": reissue.SCREENING_SCHEMA,
            "paper": "Fixture",
            "prompt_version": reissue.PROMPT_VERSION,
            "items": {"Fixture.SourceSpec": row},
        }
        self.assertEqual(
            reissue._reusable_screening_items(
                missing_reviewer,
                paper="Fixture",
            ),
            {},
        )

        review_compatible_prompt_refresh = {
            **missing_reviewer,
            "prompt_version": "older presentation wording",
            "validator": "prior reviewer",
            "validated_at": "2026-08-24T00:00:00+00:00",
        }
        self.assertEqual(
            reissue._reusable_screening_items(
                review_compatible_prompt_refresh,
                paper="Fixture",
            ),
            {"Fixture.SourceSpec": row},
        )

    def test_current_v11_queue_path_is_exact_material_content_address(self) -> None:
        material_digest = "a" * 64
        template = {
            "schema": 3,
            "paper": "Fixture",
            "items": {},
            "review_material_sha256": material_digest,
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            paper_dir.mkdir()
            review_graph = SimpleNamespace(
                context=SimpleNamespace(
                    folder=paper_dir.resolve(),
                    statement_map={
                        "paper": "Fixture",
                        "semantic_route_schema": 2,
                        "items": {},
                    },
                ),
                target_material=lambda: {
                    "semantic_targets": {},
                    "paper_declaration_sources": {},
                    "paper_prerequisite_targets": {},
                    "library_semantic_targets": {},
                },
            )
            with mock.patch.object(
                reissue,
                "decision_template",
                return_value=template,
            ):
                actual, path = reissue.current_decision_template_and_path(
                    paper_dir,
                    review_graph=review_graph,
                )

        self.assertEqual(actual, template)
        self.assertEqual(
            path.name,
            "v11_raw_source_spec_reissue_decisions_" + material_digest + ".json",
        )

    def test_content_address_cutover_preserves_exact_prior_reviewer_work(self) -> None:
        """Changing queue storage cannot discard identity-matched judgments."""

        template = {
            "schema": 3,
            "paper": "Fixture",
            "review_context_protocol": (
                reissue.review_queue.QUEUE_PROTOCOL
            ),
            "items": {
                "Fixture.SourceSpec": {
                    "source_item": "source_claim",
                    "candidate_source_items": ["source_claim"],
                    "judgment": "",
                    "reason": "",
                }
            },
            "review_material": {
                "declarations": {
                    "Fixture.SourceSpec": {
                        "semantic_target": "True",
                        "semantic_target_sha256": digest("True"),
                        "declaration_source": "def SourceSpec : Prop := True",
                        "declaration_source_sha256": digest(
                            "def SourceSpec : Prop := True"
                        ),
                    }
                },
                "source_items": {
                    "source_claim": {
                        "source_locator": "source.txt:1",
                        "verbatim_source_input": "Source claim.",
                        "verbatim_source_input_sha256": digest("Source claim."),
                        "source_input_bundle_sha256": digest("source bundle"),
                    }
                },
            },
        }
        template["review_material_sha256"] = canonical_digest(
            template["review_material"]
        )
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            audit = paper_dir / "audit"
            audit.mkdir(parents=True)
            prior = json.loads(json.dumps(template))
            prior["items"]["Fixture.SourceSpec"].update(
                {
                    "judgment": "matches",
                    "reason": "The exact source and expanded Lean statement agree.",
                }
            )
            legacy_path = audit / "v11_raw_source_spec_reissue_decisions.json"
            legacy_path.write_text(json.dumps(prior), encoding="utf-8")

            reused = reissue._matching_legacy_current_queue(
                paper_dir,
                template=template,
            )
            self.assertIsNotNone(reused)
            assert reused is not None
            self.assertEqual(
                reused["items"]["Fixture.SourceSpec"]["judgment"],
                "matches",
            )

            template["items"]["Fixture.SourceSpec"]["source_item"] = "other"
            self.assertIsNone(
                reissue._matching_legacy_current_queue(
                    paper_dir,
                    template=template,
                )
            )

    def test_lean_direct_dependency_transport_rejects_partial_or_unsorted_output(
        self,
    ) -> None:
        """Python accepts only Lean's complete, canonical direct inventory."""

        requested = ["Fixture.first", "Fixture.second"]
        valid = (
            DIRECT_LIBRARY_DEPENDENCY_SURFACE_SENTINEL
            + json.dumps(
                {
                    "schema": "1",
                    "roots": [
                        {
                            "declaration": "Fixture.first",
                            "direct_library_declarations": [
                                "AppliedModelingLib.A.first",
                            ],
                        },
                        {
                            "declaration": "Fixture.second",
                            "direct_library_declarations": [],
                        },
                    ],
                }
            )
        )
        self.assertEqual(
            parse_direct_library_dependency_surface_output(valid, requested),
            {
                "Fixture.first": ("AppliedModelingLib.A.first",),
                "Fixture.second": (),
            },
        )
        unsorted = valid.replace(
            '["AppliedModelingLib.A.first"]',
            '["AppliedModelingLib.Z.last", "AppliedModelingLib.A.first"]',
        )
        self.assertEqual(
            parse_direct_library_dependency_surface_output(unsorted, requested), {}
        )
        partial = valid.replace(
            ', {"declaration": "Fixture.second", "direct_library_declarations": []}',
            '',
        )
        self.assertEqual(
            parse_direct_library_dependency_surface_output(partial, requested), {}
        )

    def test_lean_library_target_transport_rejects_hidden_self_reference(self) -> None:
        """A library card cannot accept a declaration name in place of its target."""

        name = "AppliedModelingLib.FairDivision.Bundle"
        valid = (
            TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SENTINEL
            + json.dumps(
                {
                    "schema": "3",
                    "items": [
                        {
                            "declaration": name,
                            "review_owner_declaration": name,
                            "source_module": "AppliedModelingLib.FairDivision.Basic",
                            "source_line_start": 10,
                            "source_column_start": 0,
                            "source_line_end": 10,
                            "source_column_end": 42,
                            "declaration_kind": "definition",
                            "root_expanded": True,
                            "direct_library_declarations": [],
                            "erased_proof_declarations": [],
                            "display": "(Item : Type) → Finset Item",
                        }
                    ],
                }
            )
        )
        parsed = parse_transparent_library_declaration_display_output(valid, [name])
        self.assertEqual(parsed[name]["declaration_kind"], "definition")
        self.assertTrue(parsed[name]["root_expanded"])
        self.assertEqual(parsed[name]["review_owner_declaration"], name)

        self_reference = valid.replace(
            '"direct_library_declarations": []',
            '"direct_library_declarations": ["AppliedModelingLib.FairDivision.Bundle"]',
        )
        self.assertEqual(
            parse_transparent_library_declaration_display_output(self_reference, [name]),
            {},
        )

    def test_paper_prerequisite_transport_requires_lean_closure_and_target(self) -> None:
        """A paper-local wrapper cannot omit its retained semantic dependency."""

        root = "Fixture.SourceModel"
        dependency = "Fixture.SourcePolicy"
        valid = (
            TRANSPARENT_PAPER_DECLARATION_DISPLAY_SENTINEL
            + json.dumps(
                {
                    "schema": "2",
                    "items": [
                        {
                            "declaration": root,
                            "declaration_kind": "definition",
                            "root_expanded": True,
                            "direct_paper_declarations": [dependency],
                            "direct_library_declarations": [
                                "AppliedModelingLib.FairDivision.Bundle"
                            ],
                            "erased_proof_declarations": [],
                            "display": "∀ x, Fixture.SourcePolicy x",
                        },
                        {
                            "declaration": dependency,
                            "declaration_kind": "non_definition",
                            "root_expanded": False,
                            "direct_paper_declarations": [],
                            "direct_library_declarations": [],
                            "erased_proof_declarations": [],
                            "display": "Type → Prop",
                        },
                    ],
                }
            )
        )
        parsed = parse_transparent_paper_declaration_display_output(valid, [root])
        self.assertEqual(set(parsed), {root, dependency})
        self.assertEqual(parsed[root]["direct_paper_declarations"], (dependency,))
        self_reference = valid.replace(
            '"direct_paper_declarations": ["Fixture.SourcePolicy"]',
            '"direct_paper_declarations": ["Fixture.SourceModel"]',
        )
        self.assertEqual(
            parse_transparent_paper_declaration_display_output(self_reference, [root]),
            {},
        )

    def test_material_library_review_is_a_closeout_gate(self) -> None:
        class LibraryDashboard(_Dashboard):
            @staticmethod
            def human_review_library_prerequisites(
                _folder: Path,
                _claims: object,
                *,
                require_build: bool = True,
                semantic_targets_override: object | None = None,
                semantic_target_errors_override: object | None = None,
            ) -> list[dict[str, object]]:
                return [
                    {
                        "lean_name": "AppliedModelingLib.Example.definition",
                        "semantic_current": False,
                        "semantic_judgment": "matches",
                        "semantic_status": "stale source or library declaration",
                    }
                ]

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}", encoding="utf-8"
            )
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "direct_spec_dependency_surface": {
                            "schema": 1,
                            "protocol": "lean-elaborated-direct-library-dependencies-v1",
                            "paper_interface_sha256": digest(""),
                            "items": {
                                "Fixture.SourceSpec": {
                                    "spec_source_sha256": digest(
                                        "def SourceSpec : Prop := True"
                                    ),
                                    "direct_library_declarations": [],
                                    "review_owner_declarations": [],
                                }
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                integrity, "source_spec_correspondence_requested", return_value=True
            ), mock.patch.object(
                integrity,
                "_source_map_proof_obligation_items",
                return_value=({"source_claim": self.item}, ""),
            ), mock.patch.object(
                integrity,
                "_v11_lean_review_surface",
                return_value=self._lean_surface(
                    library_prerequisites=[
                        {
                            "lean_name": "AppliedModelingLib.Example.definition",
                            "semantic_current": False,
                            "semantic_judgment": "matches",
                            "semantic_status": "stale source or library declaration",
                        }
                    ]
                ),
            ):
                findings = integrity.material_library_semantic_review_findings(
                    folder, "formalized"
                )
        self.assertTrue(
            any("not a current `matches`" in finding.message for finding in findings)
        )

    def test_recorded_library_dependency_projection_is_not_acceptance_authority(
        self,
    ) -> None:
        """A stale derived projection cannot invalidate current graph evidence."""

        class CleanLibraryDashboard(_Dashboard):
            @staticmethod
            def library_review_owner_declaration(name: object) -> str:
                return str(name)

            @staticmethod
            def human_review_library_prerequisites(
                _folder: Path,
                _claims: object,
                *,
                require_build: bool = True,
                semantic_targets_override: object | None = None,
                semantic_target_errors_override: object | None = None,
            ) -> list[dict[str, object]]:
                return []

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}", encoding="utf-8"
            )
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "direct_spec_dependency_surface": {
                            "schema": 1,
                            "protocol": "lean-elaborated-direct-library-dependencies-v1",
                            "paper_interface_sha256": digest("old interface"),
                            "items": {
                            "Fixture.SourceSpec": {
                                "spec_source_sha256": digest("old Spec"),
                                "semantic_target_sha256": digest("old target"),
                                "direct_library_declarations": [
                                    "AppliedModelingLib.Example.projection"
                                ],
                                    "review_owner_declarations": [],
                                }
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                integrity, "source_spec_correspondence_requested", return_value=True
            ), mock.patch.object(
                integrity,
                "_source_map_proof_obligation_items",
                return_value=({"source_claim": self.item}, ""),
            ), mock.patch.object(
                integrity,
                "_v11_lean_review_surface",
                return_value=self._lean_surface(
                    semantic_target={
                        "display_sha256": digest("True"),
                        "library_declarations": (
                            "AppliedModelingLib.Example.projection",
                        ),
                    }
                ),
            ):
                messages = [
                    finding.message
                    for finding in integrity.material_library_semantic_review_findings(
                        folder, "formalized"
                    )
                ]

        self.assertEqual(messages, [])

    def test_current_graph_requires_library_review_from_direct_source_definitions(self) -> None:
        """Standalone source roots cannot hide an unreviewed library dependency."""

        direct_name = "Fixture.SourceDefinition"
        direct_target = {
            "display": "Nat",
            "display_sha256": digest("Nat"),
            "direct_paper_declarations": (),
            "direct_library_declarations": ("AppliedModelingLib.Example.Model",),
        }

        class CleanLibraryDashboard(_Dashboard):
            @staticmethod
            def library_review_owner_declaration(name: object) -> str:
                return str(name)

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}", encoding="utf-8"
            )
            result_target = self._semantic_target()
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            lean_surface = integrity._V11LeanReviewSurface(
                semantic_targets={"Fixture.SourceSpec": result_target},
                paper_prerequisites=(),
                library_prerequisites=(
                    {
                        "lean_name": "AppliedModelingLib.Example.Model",
                        "semantic_current": False,
                        "semantic_judgment": "not recorded",
                        "semantic_status": "no exact source-to-library judgment",
                    },
                ),
                source_declarations={},
                library_source_declarations={},
                semantic_contracts={},
                declaration_inventory={},
                module_sources={},
                build_input_provider=object(),
                paper_semantic_targets={direct_name: direct_target},
            )
            routes = SimpleNamespace(
                source_semantic_declarations=lambda: (direct_name,)
            )
            with (
                mock.patch.object(
                    integrity, "source_spec_correspondence_requested", return_value=True
                ),
                mock.patch.object(
                    integrity,
                    "_source_map_proof_obligation_items",
                    return_value=({"source_claim": self.item}, ""),
                ),
                mock.patch.object(
                    integrity, "typed_route_validation_required", return_value=True
                ),
                mock.patch.object(
                    integrity.EvidenceRouteSet,
                    "from_source_map",
                    return_value=routes,
                ),
                mock.patch.object(
                    integrity, "_v11_lean_review_surface", return_value=lean_surface
                ),
            ):
                findings = integrity.material_library_semantic_review_findings(
                    folder, "formalized"
                )

        self.assertTrue(
            any(
                "AppliedModelingLib.Example.Model: material library semantic review is not a current `matches` verdict"
                in finding.message
                for finding in findings
            )
        )

    def test_library_navigation_drift_does_not_stale_semantic_judgment(self) -> None:
        """Path, line, and pretty-source hashes are provenance, not meaning."""

        name = "AppliedModelingLib.Example.Model"
        source_sha = "a" * 64
        target_sha = "b" * 64
        current_target_sha = digest("Nat")
        semantic_identity_sha = "d" * 64
        ledger = {
            "schema": review_dashboard.LIBRARY_SEMANTIC_REVIEW_SCHEMA,
            "paper": "Fixture",
            "prompt_version": (
                review_dashboard.REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION
            ),
            "target_protocol": review_dashboard.LIBRARY_SEMANTIC_TARGET_PROTOCOL,
            "items": {
                name: {
                    "library_declaration": name,
                    "library_definition_sha256": "0" * 64,
                    "library_source_path": "AppliedModelingLib/Old.lean",
                    "library_line_start": 999,
                    "library_line_end": 1000,
                    "library_semantic_target_sha256": target_sha,
                    "elaborated_signature_sha256": semantic_identity_sha,
                    "library_semantic_target_protocol": (
                        review_dashboard.LIBRARY_SEMANTIC_TARGET_PROTOCOL
                    ),
                    "source_item": "model",
                    "source_input_bundle_sha256": source_sha,
                    "judgment": "matches",
                    "reason": "The exact source and semantic target agree.",
                    "validator": "reviewer",
                    "validator_type": "llm_as_judge",
                    "validated_at": "2026-08-23T00:00:00Z",
                }
            }
        }
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "Fixture"
            folder.mkdir()
            definition = "def Model : Nat := 0"
            source_path = root / "AppliedModelingLib" / "Example.lean"
            source_path.parent.mkdir()
            source_path.write_text(definition + "\n", encoding="utf-8")
            with (
                mock.patch.object(review_dashboard, "ROOT", root),
                mock.patch(
                    "scripts.current_closeout.review_surface.ROOT", root
                ),
                mock.patch(
                    "scripts.semantic_prerequisite_projection.source_anchor_file_error",
                    return_value="",
                ),
                mock.patch(
                    "scripts.semantic_prerequisite_projection.source_semantic_input_bundle",
                    return_value=("verbatim source", source_sha, ""),
                ),
            ):
                entries = review_dashboard.human_review_library_prerequisites(
                    folder,
                    [{"library_review_owner_declarations": [name]}],
                    semantic_targets_override={
                        name: {
                            "display": "Nat",
                            "display_sha256": current_target_sha,
                            "elaborated_signature_sha256": semantic_identity_sha,
                            "declaration_kind": "definition",
                            "review_owner_declaration": name,
                            "source_module": "AppliedModelingLib.Example",
                            "source_line_start": 1,
                            "source_column_start": 0,
                            "source_line_end": 1,
                            "source_column_end": len(definition),
                        }
                    },
                    semantic_target_errors_override={},
                    source_map_payload={"items": {"model": {}}},
                    ledger_payload=ledger,
                )

        self.assertEqual(len(entries), 1)
        self.assertTrue(entries[0]["semantic_current"])
        self.assertEqual(entries[0]["library_source_path"], "AppliedModelingLib/Example.lean")

    def test_graph_native_reusable_source_override_avoids_module_path_guess(
        self,
    ) -> None:
        name = "OtherPaper.Model"
        definition = "def Model : Nat := 0"
        definition_sha = digest(definition)
        target_display = "Nat"
        source_sha = "a" * 64
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            with (
                mock.patch.object(
                    review_surface,
                    "lean_graph_library_declaration_sources",
                    side_effect=AssertionError("current graph guessed a source path"),
                ),
                mock.patch(
                    "scripts.semantic_prerequisite_projection.source_anchor_file_error",
                    return_value="",
                ),
                mock.patch(
                    "scripts.semantic_prerequisite_projection.source_semantic_input_bundle",
                    return_value=("verbatim source", source_sha, ""),
                ),
            ):
                entries = review_dashboard.human_review_library_prerequisites(
                    folder,
                    [{"library_review_owner_declarations": [name]}],
                    semantic_targets_override={
                        name: {
                            "display": target_display,
                            "display_sha256": digest(target_display),
                            "elaborated_signature_sha256": "b" * 64,
                            "declaration_kind": "definition",
                            "review_owner_declaration": name,
                            "source_module": "OtherPaper.Model",
                        }
                    },
                    semantic_target_errors_override={},
                    declaration_sources_override={
                        name: {
                            "library_definition": definition,
                            "library_definition_sha256": definition_sha,
                            "library_definition_error": "",
                            "library_source_path": "papers/OtherPaper/Model.lean",
                            "library_line_start": 1,
                            "library_line_end": 1,
                        }
                    },
                    source_map_payload={"items": {"model": {}}},
                    ledger_payload={
                        "schema": review_dashboard.LIBRARY_SEMANTIC_REVIEW_SCHEMA,
                        "paper": "Fixture",
                        "prompt_version": (
                            review_dashboard.REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION
                        ),
                        "target_protocol": (
                            review_dashboard.LIBRARY_SEMANTIC_TARGET_PROTOCOL
                        ),
                        "items": {
                            name: {
                                "library_declaration": name,
                                "library_definition_sha256": definition_sha,
                                "library_semantic_target_sha256": digest(
                                    target_display
                                ),
                                "elaborated_signature_sha256": "b" * 64,
                                "library_semantic_target_protocol": (
                                    review_dashboard.LIBRARY_SEMANTIC_TARGET_PROTOCOL
                                ),
                                "source_item": "model",
                                "source_input_bundle_sha256": source_sha,
                                "judgment": "matches",
                                "validator": "reviewer",
                                "validated_at": "2026-08-28T00:00:00Z",
                            }
                        },
                    },
                )

        self.assertEqual(len(entries), 1)
        self.assertEqual(
            entries[0]["library_source_path"], "papers/OtherPaper/Model.lean"
        )

    def test_library_reissue_requires_exact_material_decision_coverage(self) -> None:
        """A reissue may not quietly omit a new material reusable declaration."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "paper": "Fixture",
                        "semantic_route_schema": 2,
                        "items": {},
                    }
                ),
                encoding="utf-8",
            )
            decisions = {
                "AppliedModelingLib.Example.first": {
                    "judgment": "matches",
                    "reason": "The selected source clause has this exact meaning.",
                }
            }
            entries = [
                {
                    "lean_name": "AppliedModelingLib.Example.first",
                    "library_definition": "def first : Prop := True",
                    "library_definition_sha256": digest("first"),
                    "verbatim_source_input": "source first",
                    "source_input_bundle_sha256": digest("source first"),
                },
                {
                    "lean_name": "AppliedModelingLib.Example.second",
                    "library_definition": "def second : Prop := True",
                    "library_definition_sha256": digest("second"),
                    "verbatim_source_input": "source second",
                    "source_input_bundle_sha256": digest("source second"),
                },
            ]
            review_graph = SimpleNamespace(
                context=SimpleNamespace(
                    statement_map={
                        "paper": "Fixture",
                        "semantic_route_schema": 2,
                        "items": {},
                    }
                ),
                specifications=[],
                semantic_targets={},
                paper_prerequisite_targets={},
                library_semantic_targets={
                    str(entry["lean_name"]): {} for entry in entries
                },
                project_library_prerequisites=lambda _folder, *, ledger: entries,
            )
            with self.assertRaisesRegex(
                library_reissue.LibraryReviewReissueError,
                "semantically changed declarations: AppliedModelingLib.Example.second",
            ):
                library_reissue.reissue(
                    folder,
                    decisions,
                    validator="independent reviewer",
                    review_graph=review_graph,
                )

    def test_library_decision_template_routes_only_along_typed_lean_edges(self) -> None:
        result_route = SimpleNamespace(
            source_item_id="theorem1",
            semantic_declarations=(),
        )
        model_route = SimpleNamespace(
            source_item_id="source_model",
            semantic_declarations=("AppliedModelingLib.Example.SourceOnly",),
        )
        routes = SimpleNamespace(
            routes=(result_route, model_route),
            result_route_by_specification=lambda: {
                "Fixture.claimSpec": result_route
            },
        )
        semantic_targets = {
            "Fixture.claimSpec": {
                "prerequisite_declarations": ["Fixture.Model"],
                "library_declarations": [
                    "AppliedModelingLib.Example.Root",
                    "OtherPaper.ReusedRoot",
                ],
            }
        }
        paper_targets = {
            "Fixture.Model": {
                "direct_paper_declarations": [],
                "direct_library_declarations": ["AppliedModelingLib.Example.PaperDep"],
            }
        }
        library_targets = {
            "AppliedModelingLib.Example.Root": {
                "direct_library_declarations": ["AppliedModelingLib.Example.Shared"]
            },
            "AppliedModelingLib.Example.PaperDep": {
                "direct_library_declarations": ["AppliedModelingLib.Example.Shared"]
            },
            "AppliedModelingLib.Example.Shared": {"direct_library_declarations": []},
            "AppliedModelingLib.Example.SourceOnly": {"direct_library_declarations": []},
            "OtherPaper.ReusedRoot": {"direct_library_declarations": []},
        }
        with mock.patch.object(
            library_reissue.EvidenceRouteSet,
            "from_source_map",
            return_value=routes,
        ):
            payload = library_reissue.decision_template(
                {
                    "items": {"source_model": {}},
                    "library_semantic_prerequisite_sources": {
                        "AppliedModelingLib.Example.Root": "source_model"
                    },
                },
                semantic_targets,
                paper_targets,
                library_targets,
                paper="Fixture",
            )

        self.assertEqual(payload["unrouted_declarations"], [])
        self.assertEqual(
            payload["items"]["AppliedModelingLib.Example.Root"]["source_item"],
            "source_model",
        )
        self.assertEqual(
            payload["items"]["AppliedModelingLib.Example.Shared"]["source_item"],
            "",
        )
        self.assertEqual(
            payload["items"]["AppliedModelingLib.Example.Shared"][
                "candidate_source_items"
            ],
            ["source_model", "theorem1"],
        )
        self.assertEqual(
            payload["items"]["AppliedModelingLib.Example.SourceOnly"]["source_item"],
            "source_model",
        )
        self.assertEqual(
            payload["items"]["OtherPaper.ReusedRoot"]["source_item"],
            "theorem1",
        )
        self.assertTrue(
            all(not row["judgment"] and not row["reason"] for row in payload["items"].values())
        )

    def test_library_decision_template_accepts_empty_lean_library_surface(self) -> None:
        result_route = SimpleNamespace(
            source_item_id="theorem1",
            semantic_declarations=(),
        )
        routes = SimpleNamespace(
            routes=(result_route,),
            result_route_by_specification=lambda: {
                "Fixture.claimSpec": result_route
            },
        )
        review_graph = SimpleNamespace(
            context=SimpleNamespace(statement_map={}),
            semantic_targets={
                "Fixture.claimSpec": {
                    "prerequisite_declarations": ["Fixture.Model"],
                    "library_declarations": [],
                }
            },
            paper_prerequisite_targets={
                "Fixture.Model": {
                    "direct_paper_declarations": [],
                    "direct_library_declarations": [],
                }
            },
            library_semantic_targets={},
            project_library_prerequisites=lambda _folder, *, ledger: [],
        )
        with (
            tempfile.TemporaryDirectory() as temporary,
            mock.patch.object(
                library_reissue.EvidenceRouteSet,
                "from_source_map",
                return_value=routes,
            ),
        ):
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            self.assertIsNone(
                library_reissue.current_changed_decision_template_and_path(
                    folder,
                    review_graph=review_graph,
                )
            )

    def test_library_reissue_reuses_exact_unchanged_semantic_judgment(self) -> None:
        """Routing refresh does not require a second unchanged source judgment."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            name = "AppliedModelingLib.Example.Model"
            source_sha = digest("source")
            target_sha = digest("target")
            current_target_sha = digest("new renderer output")
            semantic_identity_sha = digest("semantic identity")
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "items": {
                            name: {
                                "library_declaration": name,
                                "library_semantic_target_protocol": library_reissue.TARGET_PROTOCOL,
                                "library_semantic_target_sha256": target_sha,
                                "elaborated_signature_sha256": semantic_identity_sha,
                                "source_input_bundle_sha256": source_sha,
                                "judgment": "matches",
                                "reason": "The exact source and semantic target match.",
                                "validator": "prior reviewer",
                                "validator_type": "llm_as_judge",
                                "validated_at": "2026-08-24T00:00:00+00:00",
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            entries = [
                {
                    "lean_name": name,
                    "library_source_path": "AppliedModelingLib/Example.lean",
                    "library_line_start": 2,
                    "library_line_end": 2,
                    "library_definition": "def Model : Prop := True",
                    "library_definition_sha256": digest("new navigation bytes"),
                    "library_semantic_target": "Prop",
                    "library_semantic_target_sha256": current_target_sha,
                    "elaborated_signature_sha256": semantic_identity_sha,
                    "verbatim_source_input": "source",
                    "source_input_bundle_sha256": source_sha,
                    "source_anchor_bundle_sha256": source_sha,
                }
            ]
            review_graph = SimpleNamespace(
                context=SimpleNamespace(
                    statement_map={
                        "paper": "Fixture",
                        "semantic_route_schema": 2,
                        "items": {},
                    }
                ),
                specifications=[],
                semantic_targets={},
                paper_prerequisite_targets={},
                library_semantic_targets={name: {}},
                project_library_prerequisites=lambda _folder, *, ledger: entries,
            )
            payload = library_reissue.reissue(
                folder,
                {},
                validator="unused new reviewer",
                review_graph=review_graph,
            )

            row = payload["items"][name]
            self.assertNotIn("direct_spec_dependency_surface", payload)
            self.assertEqual(row["judgment"], "matches")
            self.assertEqual(row["validator"], "prior reviewer")
            self.assertEqual(
                row["library_definition_sha256"], digest("new navigation bytes")
            )
            changed = (
                library_reissue.current_changed_decision_template_and_path(
                    folder,
                    review_graph=review_graph,
                )
            )
            self.assertIsNone(changed)

    def test_library_reissue_rebinds_a_unique_semantic_rename(self) -> None:
        """A declaration rename refreshes the ledger without another verdict."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            old_name = "AppliedModelingLib.Example.OldModel"
            new_name = "AppliedModeling.Example.Model"
            source_sha = digest("source")
            semantic_identity_sha = digest("semantic identity")
            (folder / "audit" / "library_semantic_review.json").write_text(
                json.dumps(
                    {
                        "items": {
                            old_name: {
                                "library_declaration": old_name,
                                "library_semantic_target_protocol": library_reissue.TARGET_PROTOCOL,
                                "elaborated_signature_sha256": semantic_identity_sha,
                                "source_input_bundle_sha256": source_sha,
                                "judgment": "matches",
                                "reason": "The exact source and semantic target match.",
                                "validator": "prior reviewer",
                                "validator_type": "llm_as_judge",
                                "validated_at": "2026-08-24T00:00:00+00:00",
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            entries = [
                {
                    "lean_name": new_name,
                    "label": "Model",
                    "library_source_path": "AppliedModeling/Example.lean",
                    "library_line_start": 2,
                    "library_line_end": 2,
                    "library_definition": "def Model : Prop := True",
                    "library_definition_sha256": digest("new declaration bytes"),
                    "library_semantic_target": "Prop",
                    "library_semantic_target_sha256": digest("new renderer"),
                    "elaborated_signature_sha256": semantic_identity_sha,
                    "verbatim_source_input": "source",
                    "source_input_bundle_sha256": source_sha,
                    "source_anchor_bundle_sha256": source_sha,
                    "source_item": "",
                    "source_locator": "paper.txt:1",
                }
            ]
            review_graph = SimpleNamespace(
                context=SimpleNamespace(
                    statement_map={
                        "paper": "Fixture",
                        "semantic_route_schema": 2,
                        "items": {},
                    }
                ),
                specifications=[],
                semantic_targets={},
                paper_prerequisite_targets={},
                library_semantic_targets={new_name: {}},
                project_library_prerequisites=lambda _folder, *, ledger: entries,
            )

            payload = library_reissue.reissue(
                folder,
                {},
                validator="",
                review_graph=review_graph,
            )

            self.assertEqual(set(payload["items"]), {new_name})
            self.assertEqual(payload["items"][new_name]["validator"], "prior reviewer")
            self.assertEqual(
                payload["items"][new_name]["library_declaration"], new_name
            )

    def test_library_changed_only_template_omits_reusable_rows(self) -> None:
        """Changed-only review queues preserve exact prior reviewer authority."""

        stable = "AppliedModelingLib.Example.Stable"
        changed = "AppliedModelingLib.Example.Changed"
        source_sha = digest("source")
        target_sha = digest("target")
        current_target_sha = digest("new renderer output")
        semantic_identity_sha = digest("semantic identity")
        existing = {
            stable: {
                "library_semantic_target_protocol": library_reissue.TARGET_PROTOCOL,
                "library_semantic_target_sha256": target_sha,
                "semantic_supporting_declarations_sha256": digest("old context renderer"),
                "elaborated_signature_sha256": semantic_identity_sha,
                "source_input_bundle_sha256": source_sha,
                "judgment": "matches",
                "reason": "The exact source and semantic target match.",
                "validator": "prior reviewer",
                "validator_type": "llm_as_judge",
                "validated_at": "2026-08-24T00:00:00+00:00",
            }
        }
        payload = {
            "items": {stable: {}, changed: {}},
            "unrouted_declarations": [stable, changed],
        }
        entries = [
            {
                "lean_name": stable,
                "library_semantic_target_sha256": current_target_sha,
                "semantic_supporting_declarations_sha256": digest("new context renderer"),
                "elaborated_signature_sha256": semantic_identity_sha,
                "source_input_bundle_sha256": source_sha,
            },
            {
                "lean_name": changed,
                "library_semantic_target_sha256": digest("changed target"),
                "elaborated_signature_sha256": digest("changed semantic identity"),
                "source_input_bundle_sha256": source_sha,
            },
        ]

        filtered, filtered_entries = review_decision_queue.changed_only_template_surface(
            payload,
            entries,
            existing,
            reusable_judgment=library_reissue._unchanged_semantic_judgment,
        )

        self.assertEqual(set(filtered["items"]), {changed})
        self.assertEqual(filtered["unrouted_declarations"], [changed])
        self.assertEqual([entry["lean_name"] for entry in filtered_entries], [changed])

    def test_library_legacy_row_adopts_only_exact_current_named_code(self) -> None:
        """A pre-signature judgment migrates by exact code, never by its name."""

        declaration_sha = digest("def Model : Prop := True")
        source_sha = digest("source")
        prior = {
            "library_semantic_target_protocol": library_reissue.TARGET_PROTOCOL,
            "library_semantic_target_sha256": digest("old renderer"),
            "library_definition_sha256": declaration_sha,
            "source_input_bundle_sha256": source_sha,
            "judgment": "matches",
            "reason": "The exact source and declaration code match.",
            "validator": "prior reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-24T00:00:00+00:00",
        }
        entry = {
            "library_semantic_target_sha256": digest("new renderer"),
            "elaborated_signature_sha256": digest("current Lean identity"),
            "current_named_library_definition_sha256": declaration_sha,
            "source_input_bundle_sha256": source_sha,
        }

        self.assertIsNotNone(
            library_reissue._unchanged_semantic_judgment(prior, entry)
        )
        entry["current_named_library_definition_sha256"] = digest("changed code")
        self.assertIsNone(
            library_reissue._unchanged_semantic_judgment(prior, entry)
        )

    def test_library_reissue_refuses_unavailable_source_or_definition(self) -> None:
        """A decision cannot manufacture evidence when either input is absent."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            decisions = {
                "AppliedModelingLib.Example.missing": {
                    "judgment": "matches",
                    "reason": "A reviewer supplied a judgment.",
                }
            }
            entries = [
                {
                    "lean_name": "AppliedModelingLib.Example.missing",
                    "library_definition": "",
                    "library_definition_error": "not found",
                    "verbatim_source_input": "source text",
                    "source_input_bundle_sha256": digest("source text"),
                }
            ]
            review_graph = SimpleNamespace(
                context=SimpleNamespace(
                    statement_map={
                        "paper": "Fixture",
                        "semantic_route_schema": 2,
                        "items": {},
                    }
                ),
                specifications=[],
                semantic_targets={},
                paper_prerequisite_targets={},
                library_semantic_targets={
                    "AppliedModelingLib.Example.missing": {}
                },
                project_library_prerequisites=lambda _folder, *, ledger: entries,
            )
            with self.assertRaisesRegex(
                library_reissue.LibraryReviewReissueError,
                "exact bounded library declaration is unavailable",
            ):
                library_reissue.reissue(
                    folder,
                    decisions,
                    validator="independent reviewer",
                    review_graph=review_graph,
                )

    def test_library_reissue_reports_material_missing_from_routed_template(self) -> None:
        """An inconsistent graph fails with the typed writer error, not KeyError."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            name = "AppliedModelingLib.Example.unrouted"
            source_sha = digest("source")
            entry = {
                "lean_name": name,
                "library_source_path": "AppliedModelingLib/Example.lean",
                "library_line_start": 2,
                "library_line_end": 2,
                "library_definition": "def unrouted : Prop := True",
                "library_definition_sha256": digest(
                    "def unrouted : Prop := True"
                ),
                "library_semantic_target": "Prop",
                "library_semantic_target_sha256": digest("Prop"),
                "elaborated_signature_sha256": digest("semantic identity"),
                "verbatim_source_input": "source",
                "source_input_bundle_sha256": source_sha,
                "source_anchor_bundle_sha256": source_sha,
            }
            review_graph = SimpleNamespace(
                context=SimpleNamespace(
                    statement_map={
                        "paper": "Fixture",
                        "semantic_route_schema": 2,
                        "items": {},
                    }
                ),
                specifications=[],
                semantic_targets={},
                paper_prerequisite_targets={},
                library_semantic_targets={},
                project_library_prerequisites=lambda _folder, *, ledger: [entry],
            )

            with self.assertRaisesRegex(
                library_reissue.LibraryReviewReissueError,
                "current library review template has no source-routed entry",
            ):
                library_reissue.reissue(
                    folder,
                    {name: {
                        "judgment": "matches",
                        "reason": "A reviewer supplied a judgment.",
                    }},
                    validator="independent reviewer",
                    review_graph=review_graph,
                )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
