"""Focused tests for byte-pinned cited-source context artifacts."""

from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts import prepare_v11_source_map as preparer
from scripts import source_manifest_validation as source_validation
from scripts.configured_paper_inputs import current_v11_transaction_input_paths
from scripts.current_closeout.evidence_transaction import CurrentV11EvidenceSnapshotRoot


class CitedSourceArtifactRegistryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp_dir = tempfile.TemporaryDirectory()
        self.root = Path(self.temp_dir.name)
        self.folder = self.root / "papers" / "Fixture"
        self.audit = self.folder / "audit"
        self.audit.mkdir(parents=True)
        self.primary_path = self.folder / "primary.txt"
        self.cited_path = self.folder / "sources" / "cited.txt"
        self.provenance_path = self.folder / "sources" / "cited.provenance.json"
        self.cited_path.parent.mkdir(parents=True)
        self.primary_path.write_text("Primary claim.\n", encoding="utf-8")
        self.cited_path.write_text(
            "Cited model premise.\nCited prior result.\n", encoding="utf-8"
        )
        source_digest = hashlib.sha256(self.cited_path.read_bytes()).hexdigest()
        provenance = {
            "schema": 1,
            "source_url": "https://example.test/cited",
            "source_version": "Exact fixture version",
            "source_artifact_sha256": source_digest,
            "original_repository_path": "sources/original.txt",
            "paper_local_copy_path": "sources/cited.txt",
        }
        self.provenance_path.write_text(
            json.dumps(provenance, sort_keys=True) + "\n", encoding="utf-8"
        )
        self.payload = {
            "source_artifact_path": "primary.txt",
            "source_artifact_sha256": hashlib.sha256(
                self.primary_path.read_bytes()
            ).hexdigest(),
            "source_anchor_evidence_required": True,
            "cited_source_artifacts_schema": 1,
            "cited_source_artifacts": [
                {
                    "id": "cited_fixture",
                    "path": "sources/cited.txt",
                    "sha256": source_digest,
                    "provenance_path": "sources/cited.provenance.json",
                    "provenance_sha256": hashlib.sha256(
                        self.provenance_path.read_bytes()
                    ).hexdigest(),
                    "source_url": "https://example.test/cited",
                    "semantic_roles": ["prior_result", "stated_antecedent"],
                }
            ],
            "items": {
                "primary": {
                    "source_location": "primary.txt:1",
                    "source_anchor_evidence": [self._anchor("primary.txt", 1)],
                    "semantic_context_requirements": [
                        {
                            "semantic_role": "prior_result",
                            "cited_source_artifact_id": "cited_fixture",
                            "source_anchor_evidence": [
                                self._anchor("sources/cited.txt", 2)
                            ],
                        }
                    ],
                },
                "cited_prerequisite": {
                    "source_location": "sources/cited.txt:1",
                    "cited_source_artifact_id": "cited_fixture",
                    "cited_source_role": "stated_antecedent",
                    "inventory_role": "source_semantic_declaration",
                    "source_anchor_evidence": [
                        self._anchor("sources/cited.txt", 1)
                    ],
                },
            },
        }
        self.old_root = source_validation.ROOT
        source_validation.ROOT = self.root

    def tearDown(self) -> None:
        source_validation.ROOT = self.old_root
        self.temp_dir.cleanup()

    def _anchor(self, relative: str, line: int) -> dict[str, object]:
        text = (self.folder / relative).read_text(encoding="utf-8").splitlines()[
            line - 1
        ]
        return {
            "path": relative,
            "line_start": line,
            "line_end": line,
            "quoted_text": text,
            "quoted_text_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
        }

    def _findings(
        self,
        payload: dict[str, object],
        *,
        frozen: dict[Path, bytes | None] | None = None,
    ) -> list[str]:
        findings = source_validation.source_anchor_evidence_findings(
            self.folder,
            "formalized",
            self.audit / "paper_statement_map.json",
            payload,
            file_bytes_override=frozen,
        )
        return [finding.message for finding in findings]

    def test_separately_pinned_cited_prerequisite_and_context_are_valid(self) -> None:
        self.assertEqual(self._findings(self.payload), [])
        self.assertEqual(
            source_validation.semantic_context_requirement_findings(
                self.folder,
                "formalized",
                self.audit / "paper_statement_map.json",
                self.payload,
            ),
            [],
        )

    def test_noncanonical_anchor_still_requires_a_typed_cited_reference(self) -> None:
        payload = copy.deepcopy(self.payload)
        del payload["items"]["cited_prerequisite"]["cited_source_artifact_id"]
        del payload["items"]["cited_prerequisite"]["cited_source_role"]
        self.assertTrue(
            any("does not identify the canonical pinned source artifact" in error for error in self._findings(payload))
        )

    def test_primary_result_cannot_move_to_a_cited_artifact(self) -> None:
        payload = copy.deepcopy(self.payload)
        item = payload["items"]["cited_prerequisite"]
        item.pop("inventory_role")
        item["source_kind"] = "theorem"
        item["source_claim_atoms"] = [{"id": "primary.claim"}]
        item["semantic_contract"] = {"spec_declaration": "Fixture.claimSpec"}
        self.assertTrue(
            any(
                "is not an explicit source_semantic_declaration or support_only prerequisite"
                in error
                for error in self._findings(payload)
            )
        )

        item["inventory_role"] = "source_semantic_declaration"
        self.assertTrue(
            any(
                "cannot carry a primary source claim atom or semantic contract" in error
                for error in self._findings(payload)
            )
        )

    def test_role_and_exact_quote_remain_fail_closed(self) -> None:
        payload = copy.deepcopy(self.payload)
        payload["items"]["cited_prerequisite"]["cited_source_role"] = "model"
        self.assertTrue(
            any("unregistered semantic role `model`" in error for error in self._findings(payload))
        )

        payload = copy.deepcopy(self.payload)
        anchor = payload["items"]["cited_prerequisite"]["source_anchor_evidence"][0]
        anchor["quoted_text"] = "Invented citation text."
        anchor["quoted_text_sha256"] = hashlib.sha256(
            anchor["quoted_text"].encode("utf-8")
        ).hexdigest()
        self.assertTrue(
            any("does not equal the exact normalized source" in error for error in self._findings(payload))
        )

    def test_registry_rejects_duplicate_unsafe_and_unpinned_descriptors(self) -> None:
        boolean_schema = copy.deepcopy(self.payload)
        boolean_schema["cited_source_artifacts_schema"] = True
        self.assertTrue(any("schema must be 1" in error for error in self._findings(boolean_schema)))

        duplicate = copy.deepcopy(self.payload)
        duplicate["cited_source_artifacts"].append(
            copy.deepcopy(duplicate["cited_source_artifacts"][0])
        )
        self.assertTrue(any("duplicates cited source artifact" in error for error in self._findings(duplicate)))

        unsafe = copy.deepcopy(self.payload)
        unsafe["cited_source_artifacts"][0]["path"] = "../outside.txt"
        self.assertTrue(any("path escapes the paper folder" in error for error in self._findings(unsafe)))

        unpinned = copy.deepcopy(self.payload)
        unpinned["cited_source_artifacts"][0]["sha256"] = "0" * 64
        self.assertTrue(any("sha256 mismatch" in error for error in self._findings(unpinned)))

    def test_provenance_is_authenticated_and_required_in_frozen_runs(self) -> None:
        mismatch = copy.deepcopy(self.payload)
        mismatch["cited_source_artifacts"][0]["source_url"] = (
            "https://example.test/wrong"
        )
        self.assertTrue(
            any("provenance_path source_url does not match" in error for error in self._findings(mismatch))
        )

        frozen = {
            self.primary_path.resolve(): self.primary_path.read_bytes(),
            self.cited_path.resolve(): self.cited_path.read_bytes(),
            self.provenance_path.resolve(): self.provenance_path.read_bytes(),
        }
        self.assertEqual(self._findings(self.payload, frozen=frozen), [])
        frozen.pop(self.provenance_path.resolve())
        self.assertTrue(
            any("frozen input bundle omits" in error for error in self._findings(self.payload, frozen=frozen))
        )

    def test_provenance_does_not_require_an_originating_repository(self) -> None:
        provenance = json.loads(self.provenance_path.read_text(encoding="utf-8"))
        provenance.pop("original_repository_path")
        self.provenance_path.write_text(
            json.dumps(provenance, sort_keys=True) + "\n", encoding="utf-8"
        )
        payload = copy.deepcopy(self.payload)
        payload["cited_source_artifacts"][0]["provenance_sha256"] = hashlib.sha256(
            self.provenance_path.read_bytes()
        ).hexdigest()
        self.assertEqual(self._findings(payload), [])

        provenance["schema"] = True
        self.provenance_path.write_text(
            json.dumps(provenance, sort_keys=True) + "\n", encoding="utf-8"
        )
        payload["cited_source_artifacts"][0]["provenance_sha256"] = hashlib.sha256(
            self.provenance_path.read_bytes()
        ).hexdigest()
        self.assertTrue(any("schema must be 1" in error for error in self._findings(payload)))

    def test_current_transaction_selects_cited_text_and_provenance(self) -> None:
        selected = set(
            current_v11_transaction_input_paths(
                self.folder,
                status_bytes=json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {
                            "require_source_spec_correspondence": True,
                            "assumption_names": [],
                        },
                    }
                ).encode("utf-8"),
                statement_map_bytes=json.dumps(self.payload).encode("utf-8"),
                repository_root=self.root,
            )
        )
        self.assertIn(self.cited_path.resolve(), selected)
        self.assertIn(self.provenance_path.resolve(), selected)

    def test_current_transaction_mutation_guard_covers_both_cited_inputs(self) -> None:
        status = {
            "status": "formalized",
            "review_surface": {
                "require_source_spec_correspondence": True,
                "assumption_names": [],
            },
        }
        (self.folder / "status.json").write_text(
            json.dumps(status) + "\n", encoding="utf-8"
        )
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(self.payload) + "\n", encoding="utf-8"
        )
        (self.root / "papers" / "audit_config.json").write_text(
            '{"schema": 1}\n', encoding="utf-8"
        )
        context = CurrentV11EvidenceSnapshotRoot.acquire(
            self.folder, repository_root=self.root
        ).build_v11(None)
        selected = {snapshot.path for snapshot in context.input_snapshots}
        self.assertIn(self.cited_path.resolve(), selected)
        self.assertIn(self.provenance_path.resolve(), selected)

        self.cited_path.write_text("Changed cited source.\n", encoding="utf-8")
        self.provenance_path.write_text('{"changed": true}\n', encoding="utf-8")
        changed = set(context.changed_input_paths())
        self.assertIn(self.cited_path.resolve(), changed)
        self.assertIn(self.provenance_path.resolve(), changed)

    def test_preparer_projects_registry_and_cited_reference_metadata(self) -> None:
        registry = copy.deepcopy(self.payload["cited_source_artifacts"])
        prepared = preparer.prepare(
            {"paper": "Fixture", "items": {}},
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": [],
                "cited_source_artifacts_schema": 1,
                "cited_source_artifacts": registry,
            },
        )
        self.assertEqual(prepared["cited_source_artifacts"], registry)

        items: dict[str, dict[str, object]] = {"claim": {}}
        preparer._apply_semantic_context_requirements(
            items,
            {
                "semantic_context_requirements": {
                    "claim": [
                        {
                            "semantic_role": "prior_result",
                            "source_location": "sources/cited.txt:2",
                            "cited_source_artifact_id": "cited_fixture",
                        }
                    ]
                }
            },
            folder=self.folder,
        )
        self.assertEqual(
            items["claim"]["semantic_context_requirements"][0][
                "cited_source_artifact_id"
            ],
            "cited_fixture",
        )


if __name__ == "__main__":
    unittest.main()
