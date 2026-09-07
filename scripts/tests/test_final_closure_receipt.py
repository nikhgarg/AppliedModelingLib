#!/usr/bin/env python3
"""Regression tests for the canonical final-closure receipt."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from typing import Any, Mapping
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import final_closure_receipt as receipt  # noqa: E402


class FinalClosureReceiptTests(unittest.TestCase):
    def test_focused_build_rejects_zero_exit_lean_panic(self) -> None:
        completed = SimpleNamespace(
            returncode=0,
            stdout="Build completed successfully.\n",
            stderr=(
                "PANIC at Lean.Expr.appArg! Lean.Expr:926:15: application expected\n"
                "backtrace:\n...\n"
            ),
        )
        with mock.patch.object(
            receipt.subprocess, "run", return_value=completed
        ) as run:
            with self.assertRaisesRegex(
                receipt.FinalClosureReceiptError, "Lean PANIC output"
            ):
                receipt._focused_build(Path("/tmp/fixture"), "lake build Fixture")

        run.assert_called_once_with(
            ["lake", "build", "Fixture"],
            cwd=Path("/tmp/fixture"),
            check=False,
            stdout=receipt.subprocess.PIPE,
            stderr=receipt.subprocess.PIPE,
            text=True,
        )

    def make_paper(self, root: Path, paper: str = "Fixture") -> Path:
        folder = root / "papers" / paper
        audit = folder / "audit"
        audit.mkdir(parents=True)
        (folder / "source.txt").write_text("Theorem 1. True.\n", encoding="utf-8")
        (folder / "FINAL_VALIDATION_REPORT.md").write_text(
            "# Direct row review\n\n"
            "## 1. Human Verdict\n\n"
            "Formalized.\n\n"
            "## 12. Detailed Formalization Evidence\n\n"
            "Every selected source row was reviewed.\n",
            encoding="utf-8",
        )
        (folder / "PaperInterface.lean").write_text(
            "namespace Fixture\nend Fixture\n", encoding="utf-8"
        )
        source_sha = hashlib.sha256((folder / "source.txt").read_bytes()).hexdigest()
        (audit / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": source_sha,
                    "items": {},
                }
            ),
            encoding="utf-8",
        )
        (folder / "status.json").write_text(
            json.dumps({"build_target": "true"}), encoding="utf-8"
        )
        return folder

    @staticmethod
    def render_historical_receipt(payload: Mapping[str, Any]) -> str:
        """Render an immutable legacy fixture without retaining a live writer."""

        def toml_scalar(value: Any) -> str:
            if isinstance(value, int) and not isinstance(value, bool):
                return str(value)
            return json.dumps(str(value), ensure_ascii=True)

        lines = ["+++"]
        for key in (
            "schema",
            "paper",
            "closure_status",
            "evidence_lane",
            "closed_at",
        ):
            lines.append(f"{key} = {toml_scalar(payload[key])}")
        lines.append("")
        for key in (
            "source_artifact",
            "statement_map",
            "paper_interface_closure",
            "review_ledger",
            "raw_source_record",
            "focused_build",
            "focused_build_receipt",
            "engine",
            "protocol",
        ):
            value = payload.get(key)
            if not isinstance(value, Mapping):
                continue
            lines.append(f"[{key}]")
            lines.extend(
                f"{field} = {toml_scalar(scalar)}"
                for field, scalar in value.items()
            )
            lines.append("")
        lines.extend(
            [
                "+++",
                "",
                "# Historical Final Closure Receipt Fixture",
                "",
            ]
        )
        return "\n".join(lines)

    def write_historical_receipt(
        self,
        root: Path,
        paper: str = "Fixture",
        *,
        schema: int = 2,
        evidence_lane: str = receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
        review_ledger_path: str = "FINAL_VALIDATION_REPORT.md",
        interface_closure_sha256: str = "a" * 64,
        protocol_sha256: str = "b" * 64,
        commit: str = "c" * 40,
        engine_tree_sha256: str = "d" * 64,
        engine_sequence: int = 1,
    ) -> Path:
        """Create test-only schema-2--4 bytes for historical-reader regressions."""

        folder = root / "papers" / paper
        map_path = folder / "audit" / "paper_statement_map.json"
        source_map = json.loads(map_path.read_text(encoding="utf-8"))
        source_path = folder / source_map["source_artifact_path"]
        ledger_path = folder / review_ledger_path
        content_start = (
            receipt.REPORT_EVIDENCE_START_MARKER
            if ledger_path.name == "FINAL_VALIDATION_REPORT.md"
            else None
        )
        review_ledger: dict[str, Any] = {
            "path": ledger_path.relative_to(root).as_posix(),
            "sha256": hashlib.sha256(
                receipt._review_ledger_selected_bytes(
                    ledger_path,
                    content_start=content_start,
                )
            ).hexdigest(),
        }
        if content_start is not None:
            review_ledger["content_start"] = content_start
        payload: dict[str, Any] = {
            "schema": schema,
            "paper": paper,
            "closure_status": "current",
            "evidence_lane": evidence_lane,
            "source_artifact": {
                "path": source_path.relative_to(root).as_posix(),
                "sha256": receipt._sha256_file(source_path),
            },
            "statement_map": {
                "path": map_path.relative_to(root).as_posix(),
                "sha256": receipt._sha256_file(map_path),
            },
            "paper_interface_closure": {
                "root": "PaperInterface.lean",
                "sha256": interface_closure_sha256,
            },
            "review_ledger": review_ledger,
            "focused_build": {
                "command": "true",
                "target": paper,
                "result": "passed",
                "commit": commit,
            },
            "protocol": {
                "formalization_review_protocol_sha256": protocol_sha256,
            },
            "closed_at": "2026-08-24",
        }
        if evidence_lane == receipt.RAW_SOURCE_RECORD_LANE:
            raw_path = folder / "audit" / "source_record_audit.json"
            payload["raw_source_record"] = {
                "path": raw_path.relative_to(root).as_posix(),
                "sha256": receipt._sha256_file(raw_path),
            }
        if schema in {3, receipt.RECEIPT_SCHEMA}:
            build_path = receipt.focused_build_receipt_path(root, paper)
            payload["focused_build_receipt"] = {
                "path": build_path.relative_to(root).as_posix(),
                "sha256": receipt._sha256_file(build_path),
            }
        if schema == receipt.RECEIPT_SCHEMA:
            payload["engine"] = {
                "revision_sequence": engine_sequence,
                "engine_tree_sha256": engine_tree_sha256,
                "formalization_review_protocol_sha256": protocol_sha256,
            }
        path = receipt.final_closure_receipt_path(root, paper)
        path.write_text(self.render_historical_receipt(payload), encoding="utf-8")
        return path

    def test_current_interface_closure_snapshots_only_the_selected_closure(self) -> None:
        """Receipt checks must not eagerly read every Lean file in the repo."""

        root = Path("/tmp/fixture-root")
        provider = mock.Mock()
        provider.record_for_entrypoint = None
        provider.identity_for_entrypoint.return_value = ("a" * 64, None)
        provider.finalization_problems.return_value = ()
        with mock.patch.object(
            receipt, "WorktreeImportClosureProvider", return_value=provider
        ) as provider_factory:
            identity = receipt._current_interface_closure(root, "Fixture")

        self.assertEqual(identity, "a" * 64)
        provider_factory.assert_called_once_with(
            root, eager_source_snapshot=False
        )
        provider.identity_for_entrypoint.assert_called_once_with(
            "papers/Fixture/PaperInterface.lean"
        )
        provider.finalization_problems.assert_called_once_with()

    def test_current_v11_closure_can_select_complete_proof_interface_root(self) -> None:
        """The v11 carrier must include both Specs and proof endpoints."""

        root = Path("/tmp/fixture-root")
        provider = mock.Mock()
        provider.record_for_entrypoint = None
        provider.identity_for_entrypoint.return_value = ("b" * 64, None)
        provider.finalization_problems.return_value = ()
        identity = receipt._current_interface_closure(
            root,
            "Fixture",
            closure_provider_factory=lambda _root: provider,
            entrypoint="papers/Fixture/ProofInterface.lean",
        )

        self.assertEqual(identity, "b" * 64)
        provider.identity_for_entrypoint.assert_called_once_with(
            "papers/Fixture/ProofInterface.lean"
        )

    def test_fresh_v11_carrier_uses_complete_paper_build_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.ProofInterface\nimport Fixture.PaperInterface\n",
                encoding="utf-8",
            )
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            carrier = receipt.lean_import_closure_receipt_path(root, "Fixture")

            def materialize(
                _root: Path,
                _paper: str,
                *,
                persist_saved_closure: bool,
                entrypoint: str,
            ) -> str:
                self.assertTrue(persist_saved_closure)
                self.assertEqual(entrypoint, "papers/Fixture.lean")
                carrier.parent.mkdir(parents=True)
                carrier.write_text("{}\n", encoding="utf-8")
                return "a" * 64

            with (
                mock.patch.object(
                    receipt,
                    "_current_interface_closure",
                    side_effect=materialize,
                ),
                mock.patch.object(
                    receipt,
                    "validated_lean_import_closure_receipt_payload",
                    return_value={
                        "lean_import_closure": {
                            "lean_loaded_modules": [
                                "Fixture.PaperInterface",
                            ]
                        }
                    },
                ),
            ):
                self.assertEqual(
                    receipt.record_current_lean_import_closure_receipt(
                        root, "Fixture"
                    ),
                    carrier,
                )

    def test_current_interface_closure_revalidates_saved_lean_record(self) -> None:
        """A receipt-bound saved graph avoids rerunning Lean, not validation."""

        root = Path("/tmp/fixture-root")
        expected = "a" * 64
        closure = {"canonical": "Lean-emitted closure"}
        provider = mock.Mock()
        provider.identity_from_saved_closure.return_value = (expected, None)
        provider.finalization_problems.return_value = ()
        with (
            mock.patch.object(
                receipt,
                "_saved_interface_closure_candidates",
                return_value=[closure],
            ),
            mock.patch.object(
                receipt,
                "lean_import_closure_payload_sha256",
                return_value=expected,
            ),
        ):
            identity = receipt._current_interface_closure(
                root,
                "Fixture",
                closure_provider_factory=lambda _root: provider,
                expected_identity=expected,
            )

        self.assertEqual(identity, expected)
        provider.identity_from_saved_closure.assert_called_once_with(
            "papers/Fixture/PaperInterface.lean", closure
        )
        provider.finalization_problems.assert_called_once_with()
        provider.identity_for_entrypoint.assert_not_called()

    def test_stale_saved_lean_record_falls_back_to_live_lean(self) -> None:
        """A saved carrier mismatch cannot make a stale closure current."""

        root = Path("/tmp/fixture-root")
        expected = "a" * 64
        stale = {"canonical": "stale closure"}
        provider = mock.Mock()
        provider.record_for_entrypoint = None
        provider.identity_from_saved_closure.return_value = (
            None,
            SimpleNamespace(reason="source changed"),
        )
        provider.identity_for_entrypoint.return_value = (expected, None)
        provider.finalization_problems.return_value = ()
        with (
            mock.patch.object(
                receipt,
                "_saved_interface_closure_candidates",
                return_value=[stale],
            ),
            mock.patch.object(
                receipt,
                "lean_import_closure_payload_sha256",
                return_value=expected,
            ),
        ):
            identity = receipt._current_interface_closure(
                root,
                "Fixture",
                closure_provider_factory=lambda _root: provider,
                expected_identity=expected,
            )

        self.assertEqual(identity, expected)
        provider.identity_from_saved_closure.assert_called_once()
        provider.identity_for_entrypoint.assert_called_once_with(
            "papers/Fixture/PaperInterface.lean"
        )

    def test_lean_closure_carrier_is_canonical_compact_json(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            payload = {
                "schema": 1,
                "paper": "Fixture",
                "nested": {"value": [1, 2, 3]},
            }
            with mock.patch.object(
                receipt,
                "_lean_import_closure_receipt_payload",
                return_value=payload,
            ):
                path = receipt._write_lean_import_closure_receipt(
                    root, "Fixture", {"unused": True}
                )

            text = path.read_text(encoding="utf-8")
            self.assertEqual(
                text,
                json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n",
            )

    def test_validate_historical_direct_review_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                path = self.write_historical_receipt(root)
                self.assertTrue(path.is_file())
                self.assertTrue(path.read_text(encoding="utf-8").startswith("+++\n"))
                current = receipt.validate_final_closure_receipt(
                    root,
                    "Fixture",
                    required_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                )
            self.assertEqual(current.payload["paper"], "Fixture")

    def test_direct_receipt_fails_after_a_pinned_ledger_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                self.write_historical_receipt(root)
                (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                    "# Direct row review\n\n"
                    "## 1. Human Verdict\n\n"
                    "Formalized.\n\n"
                    "## 12. Detailed Formalization Evidence\n\n"
                    "Changed direct row review.\n",
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError, "review_ledger.*stale"
                ):
                    receipt.validate_final_closure_receipt(
                        root,
                        "Fixture",
                        required_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    )

    def test_stale_protocol_stops_before_transitive_lean_validation(self) -> None:
        """Conclusive cheap staleness must not launch an impossible Lean check."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.make_paper(root)
            self.write_historical_receipt(root, protocol_sha256="b" * 64)
            with (
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="c" * 64,
                ),
                mock.patch.object(
                    receipt,
                    "_current_interface_closure",
                    side_effect=AssertionError(
                        "transitive Lean validation ran after conclusive staleness"
                    ),
                ) as closure,
                self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError,
                    "formalization review protocol digest is stale",
                ),
            ):
                receipt.validate_final_closure_receipt(root, "Fixture")

            closure.assert_not_called()

    def test_final_receipt_can_reuse_a_current_pinned_build_record(self) -> None:
        """A split run remains strict when the build record pins Lean inputs."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.make_paper(root)
            registration = SimpleNamespace(
                revision_sequence=1,
                engine_tree_sha256="d" * 64,
                review_semantic_class_sha256="b" * 64,
            )
            engine_ledger = {
                "revisions": [
                    {
                        "sequence": 1,
                        "engine_tree_sha256": "d" * 64,
                        "formalization_review_protocol_sha256": "b" * 64,
                        "relation_to_previous": "bootstrap",
                    }
                ]
            }
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ) as protocol_digest,
                mock.patch.object(
                    receipt,
                    "validate_runtime_engine_registration",
                    return_value=registration,
                ),
                mock.patch.object(
                    receipt,
                    "validated_runtime_engine_revision_ledger",
                    return_value=engine_ledger,
                ),
            ):
                build_record = receipt.record_focused_build_receipt(root, "Fixture")
                self.assertTrue(build_record.is_file())
                path = self.write_historical_receipt(
                    root, schema=receipt.RECEIPT_SCHEMA
                )
                current = receipt.validate_final_closure_receipt(root, "Fixture")

                # A merge may linearize and renumber the engine ledger.  The
                # receipt's portable engine digest, not its old display
                # sequence, remains the authoritative anchor.
                renumbered = dict(current.payload)
                renumbered["engine"] = dict(current.payload["engine"])
                renumbered["engine"]["revision_sequence"] = 17
                path.write_text(
                    self.render_historical_receipt(renumbered), encoding="utf-8"
                )
                receipt.validate_final_closure_receipt(root, "Fixture")
                path.write_text(
                    self.render_historical_receipt(dict(current.payload)),
                    encoding="utf-8",
                )

                registration.revision_sequence = 2
                registration.engine_tree_sha256 = "e" * 64
                registration.review_semantic_class_sha256 = "b" * 64
                engine_ledger["revisions"].append(
                    {
                        "sequence": 2,
                        "engine_tree_sha256": "e" * 64,
                        "formalization_review_protocol_sha256": "b" * 64,
                        "relation_to_previous": "review_compatible",
                    }
                )
                receipt.validate_final_closure_receipt(root, "Fixture")

                unknown_engine = dict(current.payload)
                unknown_engine["engine"] = dict(current.payload["engine"])
                unknown_engine["engine"]["engine_tree_sha256"] = "1" * 64
                path.write_text(
                    self.render_historical_receipt(unknown_engine), encoding="utf-8"
                )
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError,
                    "engine revision does not match registered history",
                ):
                    receipt.validate_final_closure_receipt(root, "Fixture")
                path.write_text(
                    self.render_historical_receipt(dict(current.payload)),
                    encoding="utf-8",
                )

                registration.revision_sequence = 3
                registration.engine_tree_sha256 = "f" * 64
                registration.review_semantic_class_sha256 = "c" * 64
                engine_ledger["revisions"].append(
                    {
                        "sequence": 3,
                        "engine_tree_sha256": "f" * 64,
                        "formalization_review_protocol_sha256": "c" * 64,
                        "relation_to_previous": "review_semantics_changed",
                    }
                )
                protocol_digest.return_value = "c" * 64
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError,
                    "formalization review protocol digest is stale",
                ):
                    receipt.validate_final_closure_receipt(root, "Fixture")

            self.assertTrue(path.is_file())
            self.assertEqual(current.payload["schema"], 4)
            self.assertIn("focused_build_receipt", current.payload)
            self.assertEqual(current.payload["engine"]["revision_sequence"], 1)

    def test_strict_closeout_can_record_an_already_observed_build(self) -> None:
        """The orchestrator path writes pins without running Lean twice."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(receipt, "_focused_build") as focused_build,
            ):
                path = receipt.record_focused_build_receipt(
                    root, "Fixture", run_build=False
                )
                receipt.validate_focused_build_receipt(root, "Fixture")

            self.assertTrue(path.is_file())
            focused_build.assert_not_called()

    def test_strict_finalizer_records_authenticated_generic_lean_closure(self) -> None:
        """A passed v11 build reuses its plan closure without a second Lean root."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            (folder / "status.json").write_text(
                json.dumps({"build_target": "lake build +Fixture"}),
                encoding="utf-8",
            )
            closure_path = folder / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json"

            def closure(identity: str) -> dict[str, object]:
                return {
                    "entrypoint": "papers/Fixture/ProofInterface.lean",
                    "identity": identity,
                }

            def closure_receipt(identity: str) -> dict[str, object]:
                return {
                    "lean_import_closure": closure(identity),
                    "lean_import_closure_sha256": identity,
                }

            current = closure_receipt("a" * 64)
            closure_path.write_text(json.dumps(current), encoding="utf-8")
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(receipt, "_current_interface_closure") as legacy_root,
                mock.patch.object(
                    receipt,
                    "validated_lean_import_closure_receipt_payload",
                    side_effect=lambda value, **_kwargs: value,
                ),
                mock.patch.object(
                    receipt,
                    "validated_lean_import_closure_payload",
                    side_effect=lambda value: value,
                ),
                mock.patch.object(
                    receipt,
                    "lean_import_closure_payload_sha256",
                    side_effect=lambda value: value["identity"],
                ),
            ):
                path = receipt.record_focused_build_receipt(
                    root,
                    "Fixture",
                    run_build=False,
                    persist_saved_closure=False,
                    authenticated_lean_import_closure_receipt=current,
                )
                payload = json.loads(path.read_text(encoding="utf-8"))
                self.assertEqual(
                    payload["schema"],
                    receipt.AUTHENTICATED_CLOSURE_FOCUSED_BUILD_RECEIPT_SCHEMA,
                )
                self.assertEqual(
                    payload["lean_entrypoint"],
                    "papers/Fixture/ProofInterface.lean",
                )
                legacy_root.assert_not_called()

                closure_path.write_text(
                    json.dumps(closure_receipt("b" * 64)), encoding="utf-8"
                )
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError,
                    "Lean import closure is stale",
                ):
                    receipt.validate_focused_build_receipt(root, "Fixture")

    def test_focused_build_binds_lean_closure_not_audit_or_report_bytes(self) -> None:
        """Build reuse follows compiled Lean inputs, not mixed closeout files."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            status_path = folder / "status.json"
            map_path = folder / "audit" / "paper_statement_map.json"
            source_path = folder / "source.txt"
            report_path = folder / "FINAL_VALIDATION_REPORT.md"
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
            ):
                receipt.record_focused_build_receipt(
                    root, "Fixture", run_build=False
                )
                status_path.write_text(
                    json.dumps(
                        {
                            "build_target": "true",
                            "human_summary": "Improved human summary.",
                        }
                    ),
                    encoding="utf-8",
                )
                map_path.unlink()
                source_path.unlink()
                report_path.write_text("Rewritten report.\n", encoding="utf-8")

                current = receipt.validate_focused_build_receipt(root, "Fixture")

            self.assertEqual(
                current["schema"], receipt.FOCUSED_BUILD_RECEIPT_SCHEMA
            )
            self.assertEqual(
                current["paper_interface_closure_sha256"], "a" * 64
            )
            self.assertNotIn("formalization_review_protocol_sha256", current)
            self.assertNotIn("statement_map_sha256", current)
            self.assertNotIn("source_artifact_sha256", current)

    def test_focused_build_stales_on_lean_closure_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.make_paper(root)
            current_closure = "a" * 64

            def current_interface_closure(
                *_args: object, **kwargs: object
            ) -> str:
                expected = kwargs.get("expected_identity")
                if expected is not None and expected != current_closure:
                    raise receipt.FinalClosureReceiptError(
                        "PaperInterface transitive import-closure SHA-256 is stale"
                    )
                return current_closure

            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt,
                    "_current_interface_closure",
                    side_effect=current_interface_closure,
                ),
            ):
                receipt.record_focused_build_receipt(
                    root, "Fixture", run_build=False
                )
                current_closure = "b" * 64

                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError,
                    "transitive import-closure.*stale",
                ):
                    receipt.validate_focused_build_receipt(root, "Fixture")

    def test_legacy_focused_build_receipt_retains_full_input_validation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            audit = folder / "audit"
            status_path = folder / "status.json"
            map_path = audit / "paper_statement_map.json"
            source_path = folder / "source.txt"
            interface_path = folder / "PaperInterface.lean"
            payload = {
                "schema": 1,
                "paper": "Fixture",
                "command": "true",
                "target": "Fixture",
                "result": "passed",
                "commit": "c" * 40,
                "status_sha256": receipt._sha256_file(status_path),
                "statement_map_sha256": receipt._sha256_file(map_path),
                "source_artifact_sha256": receipt._sha256_file(source_path),
                "paper_interface_sha256": receipt._sha256_file(interface_path),
                "formalization_review_protocol_sha256": "b" * 64,
            }
            receipt_path = receipt.focused_build_receipt_path(root, "Fixture")
            receipt_path.write_text(json.dumps(payload), encoding="utf-8")
            with mock.patch.object(
                receipt,
                "formalization_review_protocol_digest",
                return_value="b" * 64,
            ):
                receipt.validate_focused_build_receipt(root, "Fixture")
                status_path.write_text(
                    json.dumps(
                        {"build_target": "true", "human_summary": "New copy"}
                    ),
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError, "status_sha256.*stale"
                ):
                    receipt.validate_focused_build_receipt(root, "Fixture")

    def test_schema_three_receipt_retains_its_focused_build_pin(self) -> None:
        """Adding engine provenance must not invalidate existing schema 3 receipts."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.make_paper(root)
            registration = SimpleNamespace(
                revision_sequence=1,
                engine_tree_sha256="d" * 64,
                review_semantic_class_sha256="b" * 64,
            )
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
                mock.patch.object(
                    receipt,
                    "validate_runtime_engine_registration",
                    return_value=registration,
                ),
                mock.patch.object(
                    receipt,
                    "validated_runtime_engine_revision_ledger",
                    return_value={
                        "revisions": [
                            {
                                "sequence": 1,
                                "engine_tree_sha256": "d" * 64,
                                "formalization_review_protocol_sha256": "b" * 64,
                                "relation_to_previous": "bootstrap",
                            }
                        ]
                    },
                ),
            ):
                receipt.record_focused_build_receipt(root, "Fixture", run_build=False)
                path = self.write_historical_receipt(root, schema=3)
                current = receipt.validate_final_closure_receipt(root, "Fixture")
            self.assertEqual(current.payload["schema"], 3)
            self.assertIn("focused_build_receipt", current.payload)

    def test_v11_direct_lane_refuses_a_report_in_place_of_its_screening_ledger(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "build_target": "true",
                        "review_surface": {
                            "require_source_spec_correspondence": True
                        },
                    }
                ),
                encoding="utf-8",
            )
            self.write_historical_receipt(root)
            with (
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
                self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError,
                    "must bind `audit/v11_raw_source_spec_screening.json`",
                ),
            ):
                receipt.validate_final_closure_receipt(root, "Fixture")

    def test_direct_receipt_allows_only_structural_source_absence(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt,
                    "_current_interface_closure",
                    return_value="a" * 64,
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                self.write_historical_receipt(root)
                (folder / "source.txt").unlink()
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError, "canonical source bytes"
                ):
                    receipt.validate_final_closure_receipt(root, "Fixture")
                receipt.validate_final_closure_receipt(
                    root,
                    "Fixture",
                    allow_missing_source_bytes=True,
                )

    def test_report_front_matter_change_does_not_stale_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                self.write_historical_receipt(root)
                report = folder / "FINAL_VALIDATION_REPORT.md"
                report.write_text(
                    report.read_text(encoding="utf-8").replace(
                        "Formalized.", "Formalized without caveat."
                    ),
                    encoding="utf-8",
                )
                receipt.validate_final_closure_receipt(
                    root,
                    "Fixture",
                    required_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                )

    def test_graph_receipt_exposes_current_terminal_validation_route(self) -> None:
        parsed = receipt.FinalClosureReceipt(
            path=Path("papers/Fixture/FINAL_CLOSURE_RECEIPT.md"),
            payload={"schema": receipt.ACCEPTED_GRAPH_RECEIPT_SCHEMA},
        )
        verified = SimpleNamespace(
            terminal_validation_route="lean_semantic_recovery",
            terminal_validation_detail=(
                "Lean import-closure source bytes changed: Fixture.Support.lean"
            ),
        )
        with (
            mock.patch.object(
                receipt, "load_final_closure_receipt", return_value=parsed
            ),
            mock.patch(
                "scripts.obligation_closure_credential."
                "validate_obligation_closure_receipt",
                return_value=verified,
            ),
        ):
            current = receipt.validate_final_closure_receipt(
                Path("/repo"), "Fixture"
            )

        self.assertEqual(
            current.terminal_validation_route, "lean_semantic_recovery"
        )
        self.assertIn("Fixture.Support.lean", current.terminal_validation_detail)

    def test_check_cli_distinguishes_current_semantic_recovery_from_staleness(
        self,
    ) -> None:
        current = receipt.FinalClosureReceipt(
            path=Path("papers/Fixture/FINAL_CLOSURE_RECEIPT.md"),
            payload={"schema": receipt.ACCEPTED_GRAPH_RECEIPT_SCHEMA},
            terminal_validation_route="lean_semantic_recovery",
            terminal_validation_detail=(
                "Lean import-closure source bytes changed: Fixture.Support.lean"
            ),
        )
        output = io.StringIO()
        with (
            mock.patch.object(
                receipt, "validate_final_closure_receipt", return_value=current
            ),
            contextlib.redirect_stdout(output),
        ):
            self.assertEqual(
                receipt.main(["--paper", "Fixture", "--check"]), 0
            )

        rendered = output.getvalue()
        self.assertIn("current via Lean semantic recovery", rendered)
        self.assertIn("Fixture.Support.lean", rendered)
        self.assertNotIn("stale", rendered.lower())

    def test_import_closure_accelerator_diagnostic_never_grants_acceptance(
        self,
    ) -> None:
        class Provider:
            def __init__(self, _root: Path, *, lean_import_closure_payload: object):
                self.payload = lean_import_closure_payload

            def finalize_unchanged(self) -> bool:
                return True

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            carrier = {"lean_import_closure": {"entrypoint": "fixture"}}
            path = folder / "audit" / receipt.LEAN_IMPORT_CLOSURE_RECEIPT_NAME
            path.write_text(json.dumps(carrier), encoding="utf-8")
            with (
                mock.patch.object(
                    receipt,
                    "validated_lean_import_closure_receipt_payload",
                    return_value=carrier,
                ),
            ):
                result = receipt.diagnose_import_closure_accelerators(
                    root,
                    provider_factory=Provider,
                )

        self.assertIs(result["acceptance_credential"], False)
        self.assertIs(result["diagnostic_only"], True)
        self.assertEqual(result["paper_count"], 1)
        self.assertEqual(result["exact_count"], 1)
        self.assertEqual(result["miss_count"], 0)

    def test_import_closure_accelerator_reports_complete_provider_problem(
        self,
    ) -> None:
        class Provider:
            def __init__(self, _root: Path, *, lean_import_closure_payload: object):
                del lean_import_closure_payload
                raise ValueError(
                    "Lean import-closure source validation found 2 problem(s):\n"
                    "- first changed source\n- second changed source"
                )

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            carrier = {"lean_import_closure": {"entrypoint": "fixture"}}
            path = folder / "audit" / receipt.LEAN_IMPORT_CLOSURE_RECEIPT_NAME
            path.write_text(json.dumps(carrier), encoding="utf-8")
            with (
                mock.patch.object(
                    receipt,
                    "validated_lean_import_closure_receipt_payload",
                    return_value=carrier,
                ),
            ):
                result = receipt.diagnose_exact_import_closure_accelerator(
                    root,
                    "Fixture",
                    provider_factory=Provider,
                )

        self.assertIs(result["exact_accelerator_current"], False)
        self.assertIn("2 problem(s)", result["problem"])
        self.assertIn("first changed source", result["problem"])
        self.assertIn("second changed source", result["problem"])

    def test_import_closure_diagnostic_cli_allows_repository_scope_without_paper(
        self,
    ) -> None:
        payload = {
            "schema": 1,
            "acceptance_credential": False,
            "diagnostic_only": True,
            "paper_count": 0,
            "exact_count": 0,
            "miss_count": 0,
            "items": [],
        }
        output = io.StringIO()
        with (
            mock.patch.object(
                receipt,
                "diagnose_import_closure_accelerators",
                return_value=payload,
            ) as diagnose,
            contextlib.redirect_stdout(output),
        ):
            self.assertEqual(
                receipt.main(["--diagnose-import-closure-accelerators"]),
                0,
            )

        diagnose.assert_called_once_with(receipt.ROOT, paper=None)
        self.assertEqual(json.loads(output.getvalue()), payload)

    def test_legacy_receipt_writer_is_not_a_runtime_entrypoint(self) -> None:
        self.assertFalse(hasattr(receipt, "issue_final_closure_receipt"))
        with (
            contextlib.redirect_stderr(io.StringIO()),
            self.assertRaises(SystemExit) as raised,
        ):
            receipt._parser().parse_args(["--paper", "Fixture", "--write"])
        self.assertEqual(raised.exception.code, 2)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
