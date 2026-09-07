#!/usr/bin/env python3
"""Focused runtime behavior tests for strict source-record identity replay."""

from __future__ import annotations

from contextlib import redirect_stderr
import fcntl
import hashlib
import io
import json
import tempfile
import time
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import audit_evidence_integrity as evidence


class SourceRecordIdentityRuntimeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "Fixture"
        self.paper.mkdir(parents=True)
        helper = (
            self.root
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py"
        )
        helper.parent.mkdir(parents=True)
        helper.write_text("# fixture identity helper\n", encoding="utf-8")

    @staticmethod
    def _fingerprint() -> dict[str, object]:
        return {
            "schema": 10,
            "paper": "Fixture",
            "max_depth": 4,
            "no_lean": False,
            "paper_statement_map_semantic_sha256": "c" * 64,
        }

    def _raw(self) -> dict[str, object]:
        return {
            "paper_statement_map_sha256": "a" * 64,
            "source_record_input_fingerprint": self._fingerprint(),
            "lean_import_closure": {
                "external_import_modules": ["External.One", "External.Two"]
            },
        }

    def _identity_payload(self) -> dict[str, object]:
        return {
            "paper": "Fixture",
            "paper_statement_map_sha256": "a" * 64,
            "paper_statement_map_semantic_sha256": "c" * 64,
            "source_record_input_fingerprint": self._fingerprint(),
        }

    def _write_current_identity_context_fixture(self) -> dict[str, object]:
        audit_dir = self.paper / "audit"
        audit_dir.mkdir()
        statement_map = {"schema": 1, "items": {"fixture": {"source": "x"}}}
        statement_map_bytes = (
            json.dumps(statement_map, sort_keys=True).encode("utf-8") + b"\n"
        )
        (audit_dir / "paper_statement_map.json").write_bytes(statement_map_bytes)
        raw = {
            "paper": "Fixture",
            "source_record_audit_sha256": "a" * 64,
            "paper_statement_map_sha256": hashlib.sha256(
                statement_map_bytes
            ).hexdigest(),
        }
        (audit_dir / "source_record_audit.json").write_text(
            json.dumps(raw, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return raw

    def test_runtime_identity_context_rejects_forged_stale_and_wrong_paper_reuse(
        self,
    ) -> None:
        raw = self._write_current_identity_context_fixture()
        with mock.patch.object(
            evidence,
            "source_record_audit_identity_error",
            return_value="",
        ) as strict_gate:
            context = evidence.prepare_current_source_record_identity_context(
                self.paper,
                "Fixture",
                raw,
            )
        self.assertIsNotNone(context)
        self.assertFalse(isinstance(context, dict))
        self.assertEqual(strict_gate.call_count, 1)

        # Reuse must be purely local live-input checking: it may not replay the
        # external strict gate hidden behind the opaque capability.
        with mock.patch.object(
            evidence,
            "source_record_audit_identity_error",
            side_effect=AssertionError("identity helper must not replay"),
        ):
            self.assertEqual(
                evidence.current_source_record_identity_context_error(
                    context,
                    paper_dir=self.paper,
                    paper="Fixture",
                    current_raw_audit=raw,
                ),
                "",
            )
            self.assertIn(
                "private capability",
                evidence.current_source_record_identity_context_error(
                    {},
                    paper_dir=self.paper,
                    paper="Fixture",
                    current_raw_audit=raw,
                ),
            )
            self.assertIn(
                "another paper",
                evidence.current_source_record_identity_context_error(
                    context,
                    paper_dir=self.paper,
                    paper="Other",
                    current_raw_audit=raw,
                ),
            )
            stale = dict(raw)
            stale["new_unchecked_raw_field"] = True
            self.assertIn(
                "canonical raw bytes",
                evidence.current_source_record_identity_context_error(
                    context,
                    paper_dir=self.paper,
                    paper="Fixture",
                    current_raw_audit=stale,
                ),
            )

            (self.paper / "audit" / "paper_statement_map.json").write_text(
                '{"schema": 1, "items": {"fixture": {"source": "changed"}}}\n',
                encoding="utf-8",
            )
            self.assertIn(
                "stale for live raw/map/watch inputs",
                evidence.current_source_record_identity_context_error(
                    context,
                    paper_dir=self.paper,
                    paper="Fixture",
                    current_raw_audit=raw,
                ),
            )

    def test_current_multilane_loader_runs_one_strict_identity_gate(self) -> None:
        """Every current lane receives one opaque context, never a string bypass."""

        raw = self._write_current_identity_context_fixture()
        map_digest = raw["paper_statement_map_sha256"]
        prevalidated: list[object] = []
        semantic_contexts: list[object] = []

        def from_payload(
            _raw: object,
            payload: object,
            **kwargs: object,
        ) -> dict[str, dict[str, object]]:
            prevalidated.append(kwargs.get("prevalidated_source_record_identity_error"))
            items = payload.get("items", {}) if isinstance(payload, dict) else {}
            return {
                str(key): dict(value)
                for key, value in items.items()
                if isinstance(value, dict)
            }

        def lane(key: str) -> dict[str, dict[str, object]]:
            return {key: {"classification": "fixture"}}

        class OverlayError(ValueError):
            pass

        def load_lanes(
            *_args: object,
            lane_labels: object = (),
            source_record_identity_context: object | None = None,
            **_kwargs: object,
        ) -> tuple[SimpleNamespace, ...]:
            semantic_contexts.append(source_record_identity_context)
            return tuple(
                SimpleNamespace(
                    label=label,
                    items=lane(
                        {
                            "differential": "differential",
                            "semantic_rebind": "semantic",
                        }[label]
                    ),
                )
                for label in lane_labels
            )

        overlay_union = SimpleNamespace(
            SourceRecordAuthenticatedOverlayUnionError=OverlayError,
            load_authenticated_current_overlay_lanes=load_lanes,
        )

        def present_lanes(
            _folder: object, *, lane_labels: object = ()
        ) -> tuple[str, ...]:
            return ("differential", "semantic_rebind")

        with (
            mock.patch.object(
                evidence,
                "source_record_audit_identity_error",
                return_value="",
            ) as strict_gate,
            mock.patch.object(
                evidence,
                "_current_source_record_judgment_items_from_payload",
                side_effect=from_payload,
            ),
            mock.patch.object(
                evidence,
                "source_record_overlay_labels_with_artifacts",
                side_effect=present_lanes,
            ),
            mock.patch.object(
                evidence, "_authenticated_overlay_union_module", return_value=overlay_union
            ),
            mock.patch.object(
                evidence,
                "_project_current_source_record_response_association_pins",
                side_effect=lambda _raw, items, **_kwargs: dict(items),
            ),
            mock.patch.object(
                evidence,
                "load_configured_assumption_formalization_regularity_context",
                return_value=(None, ""),
            ),
        ):
            loaded = evidence.current_source_record_judgment_items(
                raw,
                {"items": {}},
                folder=self.paper,
                expected_paper_statement_map_sha256=str(map_digest),
            )

        self.assertEqual(strict_gate.call_count, 1)
        self.assertEqual(len(prevalidated), 3)
        self.assertEqual(set(prevalidated), {""})
        self.assertEqual(len(semantic_contexts), 1)
        self.assertIsNotNone(semantic_contexts[0])
        self.assertEqual(
            set(loaded),
            {
                "differential",
                "semantic",
            },
        )

    def test_runtime_identity_context_defers_while_a_producer_holds_the_lock(
        self,
    ) -> None:
        """A minted context cannot race an exclusive raw-audit publication."""

        raw = self._write_current_identity_context_fixture()
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "source_record_audit_identity_error",
                return_value="",
            ),
        ):
            context = evidence.prepare_current_source_record_identity_context(
                self.paper,
                "Fixture",
                raw,
            )
            self.assertIsNotNone(context)
            lock_path = self.root / evidence.SOURCE_RECORD_AUDIT_LOCK_RELATIVE_PATH
            lock_path.parent.mkdir(parents=True, exist_ok=True)
            with lock_path.open("a+", encoding="utf-8") as holder:
                fcntl.flock(holder.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                error = evidence.current_source_record_identity_context_error(
                    context,
                    paper_dir=self.paper,
                    paper="Fixture",
                    current_raw_audit=raw,
                )
        self.assertTrue(error.startswith("source-record identity revalidation deferred:"), error)

    def test_successful_context_reuse_never_replays_the_fingerprint_helper(
        self,
    ) -> None:
        """The current-v10 reuse branch skips only the external fingerprint scan."""

        raw = self._write_current_identity_context_fixture()
        raw["prompt_version"] = evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        raw["source_record_policy_version"] = (
            evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        )
        (self.paper / "audit" / "source_record_audit.json").write_text(
            json.dumps(raw, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "source_record_audit_identity_error",
                return_value="",
            ),
        ):
            context = evidence.prepare_current_source_record_identity_context(
                self.paper,
                "Fixture",
                raw,
            )
        self.assertIsNotNone(context)

        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(evidence, "source_record_audit_receipt_error", return_value=""),
            mock.patch.object(
                evidence,
                "source_record_semantic_contract_revalidation_context",
                return_value=(None, ""),
            ),
            mock.patch.object(
                evidence,
                "source_record_effective_semantic_surface_error",
                return_value="",
            ),
            mock.patch.object(
                evidence,
                "source_record_raw_scan_completeness_error",
                return_value="",
            ),
            mock.patch.object(
                evidence,
                "source_record_raw_reusable_item_metadata_error",
                return_value="",
            ),
            mock.patch.object(
                evidence,
                "source_record_current_input_fingerprint_error",
                return_value="",
            ) as fingerprint_helper,
            mock.patch.object(evidence.subprocess, "run") as subprocess_run,
        ):
            error = evidence.current_source_record_identity_context_error(
                context,
                paper_dir=self.paper,
                paper="Fixture",
                current_raw_audit=raw,
            )
        self.assertEqual(error, "")
        fingerprint_helper.assert_not_called()
        subprocess_run.assert_not_called()

    def test_busy_raw_scan_defers_without_launching_identity_helper(self) -> None:
        busy = evidence.SourceRecordIdentityRevalidationBusy("raw scan owns lock")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_identity_read_lock",
                side_effect=busy,
            ),
            mock.patch.object(evidence.subprocess, "run") as run,
        ):
            error = evidence._source_record_current_input_fingerprint_error(
                self.paper,
                self._raw(),
                verify_watch_inputs=False,
            )

        self.assertIn("identity revalidation deferred", error)
        self.assertIn("raw scan owns lock", error)
        run.assert_not_called()

    def test_read_lock_refuses_an_actual_exclusive_raw_holder(self) -> None:
        lock_path = self.root / evidence.SOURCE_RECORD_AUDIT_LOCK_RELATIVE_PATH
        lock_path.parent.mkdir(parents=True)
        with lock_path.open("a+", encoding="utf-8") as holder:
            fcntl.flock(holder.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaises(evidence.SourceRecordIdentityRevalidationBusy):
                with evidence._source_record_identity_read_lock(self.root):
                    self.fail("shared identity lock must not run beside raw generation")

    def test_strict_identity_emits_bounded_lifecycle_progress(self) -> None:
        output = io.StringIO()

        def delayed_identity(*_args: object, **_kwargs: object) -> SimpleNamespace:
            time.sleep(0.15)
            return SimpleNamespace(
                returncode=0,
                stdout=json.dumps(self._identity_payload()),
                stderr="",
            )

        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "SOURCE_RECORD_IDENTITY_PROGRESS_HEARTBEAT_SECONDS",
                0.01,
            ),
            mock.patch.object(
                evidence.subprocess,
                "run",
                side_effect=delayed_identity,
            ) as run,
            redirect_stderr(output),
        ):
            error = evidence._source_record_current_input_fingerprint_error(
                self.paper,
                self._raw(),
                verify_watch_inputs=False,
            )

        self.assertEqual(error, "")
        diagnostics = output.getvalue()
        self.assertIn("started (2 external module artifact(s)", diagnostics)
        self.assertIn("still running", diagnostics)
        self.assertIn("finished", diagnostics)
        self.assertEqual(
            run.call_args.kwargs["timeout"],
            evidence.SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS,
        )

    def test_timeout_is_an_explicit_nonacceptance(self) -> None:
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence.subprocess,
                "run",
                side_effect=evidence.subprocess.TimeoutExpired(
                    "identity",
                    evidence.SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS,
                ),
            ),
            redirect_stderr(io.StringIO()),
        ):
            error = evidence._source_record_current_input_fingerprint_error(
                self.paper,
                self._raw(),
                verify_watch_inputs=False,
            )

        self.assertIn("timed out", error)
        self.assertIn("no evidence result was accepted", error)


if __name__ == "__main__":
    unittest.main()
