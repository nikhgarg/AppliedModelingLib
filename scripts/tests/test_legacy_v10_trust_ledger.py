#!/usr/bin/env python3
"""Regressions for the portable immutable legacy-v10 trust ledger."""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from formalization_protocol import (  # noqa: E402
    IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
    IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
    IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
    IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
    IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
)
from legacy_v10_trust_ledger import (  # noqa: E402
    ENGINE_SOURCE_PATHS,
    LegacyV10TrustLedgerError,
    encode_trust_ledger,
    evaluate_saved_status_reuse,
    generate_trust_ledger_payload,
    material_association_comparison_errors,
    validate_trust_ledger_payload,
)
from lean_import_closure import WorktreeImportClosureProvider  # noqa: E402
from scripts import review_dashboard  # noqa: E402
from scripts.tests.test_theorem_realization_transition import (  # noqa: E402
    artifact_payloads,
    two_item_artifact_payloads,
)
from source_coverage_scope import (  # noqa: E402
    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    source_item_coverage_sha256,
)
from theorem_realization_transition import (  # noqa: E402
    MATERIAL_ARTIFACT_PATHS,
    STATUS_PATH,
    theorem_realization_reissue_requirement,
)


MANIFEST_RELATIVE = "config/legacy_v10_material_identity_manifest.json"


class LegacyV10TrustLedgerTests(unittest.TestCase):
    def git(self, root: Path, *args: str) -> None:
        subprocess.run(
            ["git", *args],
            cwd=root,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )

    def complete_saved_status_sidecars(
        self, label: str, payloads: dict[str, object]
    ) -> dict[str, object]:
        completed = copy.deepcopy(payloads)
        statement_map = completed["audit/paper_statement_map.json"]
        statement_review = completed["audit/statement_match_llm.json"]
        statement_review.update(
            {
                "schema": 1,
                "paper": label,
                "prompt_version": "statement-match-v10-fixture",
                "validator": "fixture-reviewer",
                "validator_type": "test",
                "validated_at": "2026-07-31T00:00:00Z",
            }
        )
        review_by_paper_digest: dict[str, str] = {}
        for key, item in statement_review["items"].items():
            item.update(
                {
                    "tex_statement_sha256": item["paper_statement_sha256"],
                    "judgment": "matches",
                    "resolution": "",
                    "reason": "Fixture semantic comparison is exact.",
                }
            )
            review_by_paper_digest[item["paper_statement_sha256"]] = key

        coverage_items: dict[str, object] = {}
        for source_key, source_item in statement_map["items"].items():
            paper_digest = source_item["source_anchor_evidence"][0][
                "quoted_text_sha256"
            ]
            coverage_items[source_key] = {
                "coverage": "covered",
                "review_rows": [review_by_paper_digest[paper_digest]],
                "support_declarations": [],
                "reason": "The reviewed statement directly covers this source item.",
                "source_evidence": source_item["statement"],
            }
        completed["audit/paper_coverage_llm.json"] = {
            "schema": 1,
            "paper": label,
            "audit_kind": "source_to_dashboard_llm",
            "source_grounded": True,
            "seed_scaffold": False,
            "prompt_version": "paper-coverage-v10-fixture",
            "validator": "fixture-reviewer",
            "validator_type": "test",
            "validated_at": "2026-07-31T00:00:00Z",
            "items": coverage_items,
        }
        completed["status.json"]["review_surface"] = {
            "include_names": list(statement_review["items"]),
            "assumption_names": [],
        }
        return completed

    def closure_provider(self, root: Path) -> WorktreeImportClosureProvider:
        def graph_loader(_root: Path, entry_module: str, _timeout: int):
            return tuple(sorted((entry_module, "AppliedModelingLib.FixtureBase"))), ""

        return WorktreeImportClosureProvider(
            root,
            module_graph_loader=graph_loader,
        )

    def write_artifacts(self, folder: Path, payloads: dict[str, object]) -> None:
        for relative in MATERIAL_ARTIFACT_PATHS:
            path = folder / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(payloads[relative], indent=2), encoding="utf-8")
        coverage = folder / "audit/paper_coverage_llm.json"
        coverage.write_text(
            json.dumps(payloads["audit/paper_coverage_llm.json"], indent=2),
            encoding="utf-8",
        )
        statement_map = payloads["audit/paper_statement_map.json"]
        full_inventory, selected_inventory, mode, mode_error = (
            review_dashboard.paper_coverage_inventory(folder)
        )
        if mode_error or not selected_inventory:
            raise AssertionError(mode_error or "fixture source selection is empty")
        coverage_payload = json.loads(coverage.read_text(encoding="utf-8"))
        for key, source_item in selected_inventory.items():
            coverage_item = coverage_payload["items"].get(key)
            if not isinstance(coverage_item, dict):
                raise AssertionError(f"fixture coverage row {key} is unavailable")
            coverage_item["source_item_coverage_digest_schema"] = (
                SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
            )
            coverage_item["source_item_coverage_sha256"] = source_item_coverage_sha256(
                source_item, mode
            )
        coverage_payload["paper_statement_inventory_sha256"] = (
            review_dashboard.paper_coverage_inventory_digest(
                selected_inventory,
                mode=mode,
                statement_map_payload=statement_map,
            )
        )
        coverage.write_text(json.dumps(coverage_payload, indent=2), encoding="utf-8")

    def manifest_protocol(self) -> dict[str, object]:
        payload = json.loads(
            (ROOT / "config/formalization_audit_protocol.json").read_text(
                encoding="utf-8"
            )
        )
        baseline = payload["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]
        baseline.clear()
        baseline.update(
            {
                "authority": IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
                "manifest_path": MANIFEST_RELATIVE,
                "manifest_sha256": "0" * 64,
                "manifest_schema": IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
                "material_identity_schema": IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
                "engine_id": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
                "engine_schema": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
                "rule": "Fixture immutable semantic transition ledger.",
            }
        )
        return payload

    def prepare_root(
        self,
        root: Path,
        papers: dict[str, dict[str, object]],
        *,
        selected: list[str] | None = None,
    ) -> tuple[dict[str, object], dict[str, object], Path]:
        self.git(root, "init", "-q")
        self.git(root, "config", "user.email", "fixture@example.invalid")
        self.git(root, "config", "user.name", "Fixture")
        for relative in ENGINE_SOURCE_PATHS:
            destination = root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, destination)
        protocol = self.manifest_protocol()
        protocol_path = root / "config/formalization_audit_protocol.json"
        protocol_path.parent.mkdir(parents=True, exist_ok=True)
        protocol_path.write_text(json.dumps(protocol, indent=2), encoding="utf-8")
        for label, payloads in papers.items():
            completed = self.complete_saved_status_sidecars(label, payloads)
            folder = root / "papers" / label
            source_bytes = f"{label} canonical fixture source\n".encode("utf-8")
            statement_map = completed["audit/paper_statement_map.json"]
            statement_map["source_artifact_path"] = "paper.txt"
            statement_map["source_artifact_sha256"] = hashlib.sha256(
                source_bytes
            ).hexdigest()
            self.write_artifacts(folder, completed)
            (folder / "paper.txt").write_bytes(source_bytes)
            (folder / "PaperInterface.lean").write_text(
                "import AppliedModelingLib.FixtureBase\n\n"
                f"namespace {label}\n\n"
                "theorem paperInterfaceFixture : True := by trivial\n\n"
                f"end {label}\n",
                encoding="utf-8",
            )
        base = root / "AppliedModelingLib/FixtureBase.lean"
        base.parent.mkdir(parents=True, exist_ok=True)
        base.write_text(
            "namespace AppliedModelingLib\n\n"
            "theorem fixtureBase : True := by trivial\n\n"
            "end AppliedModelingLib\n",
            encoding="utf-8",
        )
        (root / "Scratch.lean").write_text(
            "theorem unimportedScratch : True := by trivial\n", encoding="utf-8"
        )
        (root / "lean-toolchain").write_text(
            (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
            encoding="utf-8",
        )
        (root / "lake-manifest.json").write_text('{"version": 7}\n')
        libraries = "".join(
            f'\n[[lean_lib]]\nname = "{label}"\nsrcDir = "papers"\n' for label in papers
        )
        (root / "lakefile.toml").write_text(
            'name = "Fixture"\n\n[[lean_lib]]\nname = "AppliedModelingLib"\n'
            + libraries
        )
        self.git(root, "add", ".")
        self.git(root, "commit", "-qm", "fixture baseline")
        manifest = generate_trust_ledger_payload(
            root=root,
            selected_paper_folders=selected or list(papers),
            protocol=protocol,
            closure_provider=self.closure_provider(root),
        )
        raw = encode_trust_ledger(manifest)
        manifest_path = root / MANIFEST_RELATIVE
        manifest_path.write_bytes(raw)
        baseline = protocol["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]
        baseline["manifest_sha256"] = hashlib.sha256(raw).hexdigest()
        protocol_path.write_text(json.dumps(protocol, indent=2), encoding="utf-8")
        return protocol, manifest, manifest_path

    def requirement(self, root: Path, folder: str, protocol: dict[str, object]):
        status = json.loads(
            (root / "papers" / folder / STATUS_PATH).read_text(encoding="utf-8")
        )
        return theorem_realization_reissue_requirement(
            root,
            root / "papers" / folder,
            status,
            protocol=protocol,
        )

    def saved_status_reuse(self, root: Path, folder: str, protocol: dict[str, object]):
        baseline = protocol["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]
        return evaluate_saved_status_reuse(
            root=root,
            folder=root / "papers" / folder,
            baseline=baseline,
            protocol=protocol,
            closure_provider=self.closure_provider(root),
        )

    def rewrite_manifest(
        self,
        protocol: dict[str, object],
        manifest_path: Path,
        manifest: dict[str, object],
    ) -> None:
        raw = encode_trust_ledger(manifest)
        manifest_path.write_bytes(raw)
        protocol["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]["manifest_sha256"] = hashlib.sha256(raw).hexdigest()

    def direct_review_receipt(self, label: str) -> dict[str, object]:
        """A structurally complete canonical direct-review closure receipt."""

        return {
            "schema": 2,
            "paper": label,
            "closure_status": "current",
            "evidence_lane": "direct-source-row-review",
            "source_artifact": {"path": "paper.txt", "sha256": "1" * 64},
            "statement_map": {
                "path": "audit/paper_statement_map.json",
                "sha256": "2" * 64,
            },
            "paper_interface_closure": {
                "root": "PaperInterface.lean",
                "sha256": "3" * 64,
            },
            "review_ledger": {
                "path": "FINAL_VALIDATION_REPORT.md",
                "sha256": "4" * 64,
                "content_start": "## 12. Detailed Formalization Evidence",
            },
            "focused_build": {
                "command": "lake build Fixture",
                "target": label,
                "result": "passed",
                "commit": "5" * 40,
            },
            "protocol": {"formalization_review_protocol_sha256": "6" * 64},
            "closed_at": "2026-08-16",
        }

    def test_saved_status_reuse_detects_imported_lean_change(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            baseline = self.saved_status_reuse(root, "Fixture", protocol)
            path = root / "AppliedModelingLib/FixtureBase.lean"
            path.write_text(path.read_text() + "\n-- imported semantic change\n")
            changed = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertFalse(baseline.required, baseline.reason)
        self.assertTrue(changed.required)
        self.assertIn("unstaged_imported_module", changed.reason)

    def test_saved_status_reuse_detects_statement_verdict_change(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            path = root / "papers/Fixture/audit/statement_match_llm.json"
            payload = json.loads(path.read_text())
            payload["items"]["theorem_one"].update(
                {"judgment": "uncertain", "resolution": ""}
            )
            path.write_text(json.dumps(payload))

            changed = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertTrue(changed.required)
        self.assertIn("disposition changed", changed.reason)

    def test_saved_status_reuse_detects_coverage_verdict_change(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            path = root / "papers/Fixture/audit/paper_coverage_llm.json"
            payload = json.loads(path.read_text())
            payload["items"]["theorem_one_navigation_key"]["coverage"] = (
                "conditional_boundary"
            )
            path.write_text(json.dumps(payload))

            changed = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertTrue(changed.required)
        self.assertIn("disposition changed", changed.reason)

    def test_saved_status_reuse_detects_toolchain_change(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            (root / "lean-toolchain").write_text("leanprover/lean4:v4.20.0\n")

            changed = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertTrue(changed.required)
        self.assertIn("control_file_unstaged", changed.reason)

    def test_saved_status_reuse_revalidates_canonical_source_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            source = root / "papers/Fixture/paper.txt"
            original = source.read_bytes()
            source.write_bytes(b"changed canonical source bytes\n")
            changed = self.saved_status_reuse(root, "Fixture", protocol)
            source.write_bytes(original)
            restored = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertTrue(changed.required)
        self.assertIn("canonical source artifact bytes disagree", changed.reason)
        self.assertFalse(restored.required, restored.reason)

    def test_saved_status_reuse_marks_immutable_structural_source_fallback(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            (root / "papers/Fixture/paper.txt").unlink()

            structural = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertFalse(structural.required, structural.reason)
        self.assertEqual(
            structural.canonical_source_state,
            "structural_checkout_immutable_attestation",
        )
        self.assertEqual(
            len(structural.coverage_source_bindings),
            structural.coverage_counts["total"],
        )

    def test_saved_status_reuse_ignores_unimported_scratch_change(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            (root / "Scratch.lean").write_text(
                "theorem changedUnimportedScratch : False := by sorry\n"
            )

            unchanged = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertFalse(unchanged.required, unchanged.reason)

    def test_saved_status_reuse_never_invokes_live_graph_on_unchanged_receipt(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )

            def forbidden_loader(_root: Path, _module: str, _timeout: int):
                raise AssertionError("ordinary saved-status reuse invoked Lean")

            baseline = protocol["audit_versions"]["theorem_realization"][
                "legacy_v10_transition_baseline"
            ]
            unchanged = evaluate_saved_status_reuse(
                root=root,
                folder=root / "papers/Fixture",
                baseline=baseline,
                protocol=protocol,
                closure_provider=WorktreeImportClosureProvider(
                    root, module_graph_loader=forbidden_loader
                ),
            )

        self.assertFalse(unchanged.required, unchanged.reason)

    def test_saved_status_reuse_ignores_resolvable_navigation_renames(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            before = self.saved_status_reuse(root, "Fixture", protocol)
            folder = root / "papers/Fixture/audit"
            review_path = folder / "statement_match_llm.json"
            review = json.loads(review_path.read_text())
            review["items"]["renamed_review_row"] = review["items"].pop("theorem_one")
            review_path.write_text(json.dumps(review))
            status_path = root / "papers/Fixture/status.json"
            status = json.loads(status_path.read_text())
            status["review_surface"]["include_names"] = ["renamed_review_row"]
            status_path.write_text(json.dumps(status))

            map_path = folder / "paper_statement_map.json"
            statement_map = json.loads(map_path.read_text())
            statement_map["items"]["renamed_source_row"] = statement_map["items"].pop(
                "theorem_one_navigation_key"
            )
            map_path.write_text(json.dumps(statement_map))

            coverage_path = folder / "paper_coverage_llm.json"
            coverage = json.loads(coverage_path.read_text())
            coverage_item = coverage["items"].pop("theorem_one_navigation_key")
            coverage_item["review_rows"] = ["renamed_review_row"]
            coverage["items"]["renamed_source_row"] = coverage_item
            coverage_path.write_text(json.dumps(coverage))

            source_record_path = folder / "source_record_audit.json"
            source_record = json.loads(source_record_path.read_text())
            for section in ("boundary_input_items", "semantic_model_items"):
                for item in source_record[section]:
                    item["row"] = "renamed_review_row"
            source_record_path.write_text(json.dumps(source_record))

            unchanged = self.saved_status_reuse(root, "Fixture", protocol)

        self.assertFalse(unchanged.required, unchanged.reason)
        self.assertEqual(
            unchanged.coverage_source_bindings,
            before.coverage_source_bindings,
        )
        self.assertIsInstance(unchanged.coverage_source_bindings, tuple)
        self.assertEqual(
            len(unchanged.coverage_source_bindings),
            unchanged.coverage_counts["total"],
        )
        self.assertTrue(
            all(
                set(binding)
                == {
                    "source_map_item_semantic_sha256",
                    "source_item_semantic_sha256",
                }
                for binding in unchanged.coverage_source_bindings
            )
        )

    def test_material_association_comparison_ignores_receipt_schema_upgrade(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            _protocol, candidate, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            previous = copy.deepcopy(candidate)
            previous["schema"] = 1
            previous["engine"]["schema"] = 1
            previous["entries"][0]["schema"] = 1

            unchanged = material_association_comparison_errors(previous, candidate)
            changed = copy.deepcopy(candidate)
            changed["entries"][0]["material_identity_sha256"] = "f" * 64
            errors = material_association_comparison_errors(previous, changed)

        self.assertEqual(unchanged, [])
        self.assertTrue(errors)
        self.assertIn("material_identity_sha256", errors[0])

    def test_generator_accepts_current_canonical_direct_review_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, manifest_path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            direct = self.direct_review_receipt("Fixture")
            with mock.patch(
                "legacy_v10_trust_ledger._current_direct_source_row_review_receipt",
                return_value=(direct, ""),
            ):
                manifest = generate_trust_ledger_payload(
                    root=root,
                    selected_paper_folders=["Fixture"],
                    protocol=protocol,
                    closure_provider=self.closure_provider(root),
                )
            self.rewrite_manifest(protocol, manifest_path, manifest)
            validated = validate_trust_ledger_payload(
                manifest, root=root, protocol=protocol
            )
            reuse = self.saved_status_reuse(root, "Fixture", protocol)

        evidence = validated["entries"][0]["closeout_evidence"]
        self.assertEqual(evidence["kind"], "direct-source-row-review")
        self.assertTrue(reuse.required)
        self.assertIn("direct-source-row-review", reuse.reason)

    def test_generator_does_not_fall_back_from_an_invalid_direct_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            with mock.patch(
                "legacy_v10_trust_ledger._current_direct_source_row_review_receipt",
                return_value=(None, "source artifact pin is stale"),
            ):
                with self.assertRaisesRegex(
                    LegacyV10TrustLedgerError, "direct closeout receipt is invalid"
                ):
                    generate_trust_ledger_payload(
                        root=root,
                        selected_paper_folders=["Fixture"],
                        protocol=protocol,
                        closure_provider=self.closure_provider(root),
                    )

    def test_navigation_and_declaration_renames_do_not_reopen(self) -> None:
        payloads = artifact_payloads()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"OriginalFolder": payloads}
            )
            renamed = root / "papers" / "RenamedFolder"
            (root / "papers" / "OriginalFolder").rename(renamed)
            source_map = json.loads(
                (renamed / "audit/paper_statement_map.json").read_text()
            )
            item = source_map["items"].pop("theorem_one_navigation_key")
            item["lean_declarations"] = ["Renamed.theorem"]
            source_map["items"]["renamed_navigation_key"] = item
            (renamed / "audit/paper_statement_map.json").write_text(
                json.dumps(source_map)
            )
            statement_review = json.loads(
                (renamed / "audit/statement_match_llm.json").read_text()
            )
            judgment = statement_review["items"].pop("theorem_one")
            statement_review["items"]["renamed_theorem"] = judgment
            (renamed / "audit/statement_match_llm.json").write_text(
                json.dumps(statement_review)
            )
            source_record = json.loads(
                (renamed / "audit/source_record_audit.json").read_text()
            )
            for section in ("boundary_input_items", "semantic_model_items"):
                for record in source_record[section]:
                    record["row"] = "renamed_theorem"
                    record["reviewed_elaborated_signature_identities"][0][
                        "qualified_declaration"
                    ] = "Renamed.theorem"
                    if "qualified_declaration" in record:
                        record["qualified_declaration"] = "Renamed.theorem"
            (renamed / "audit/source_record_audit.json").write_text(
                json.dumps(source_record)
            )

            result = self.requirement(root, "RenamedFolder", protocol)

        self.assertFalse(result.required, result.reason)

    def test_cross_entry_semantic_association_swap_requires_current_v10_not_v11(self) -> None:
        first = artifact_payloads()
        second = two_item_artifact_payloads()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"First": first, "Second": second}
            )
            path = root / "papers/First/audit/source_record_audit.json"
            current = json.loads(path.read_text())
            current["boundary_input_items"][0]["source_contract_association"] = (
                copy.deepcopy(
                    second["audit/source_record_audit.json"]["boundary_input_items"][1][
                        "source_contract_association"
                    ]
                )
            )
            path.write_text(json.dumps(current))

            result = self.requirement(root, "First", protocol)

        self.assertFalse(result.required)
        self.assertIn("current item-level v10", result.reason)

    def test_dependency_paths_are_navigation_but_dependency_bytes_are_material(
        self,
    ) -> None:
        payloads = artifact_payloads()
        payloads["audit/source_record_audit.json"][
            "source_record_input_fingerprint"
        ] = {
            "schema": 1,
            "source_record_item_digest_schema": 1,
            "source_record_policy_version": "source-record-v10",
            "lean_dependency_identities": [
                {
                    "path": "EconCSLib/OldName.lean",
                    "sha256": "1" * 64,
                    "status": "present",
                }
            ],
            "toolchain_identities": [
                {"path": "lean-toolchain", "sha256": "2" * 64, "status": "present"}
            ],
        }
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(root, {"Fixture": payloads})
            path = root / "papers/Fixture/audit/source_record_audit.json"
            current = json.loads(path.read_text())
            dependency = current["source_record_input_fingerprint"][
                "lean_dependency_identities"
            ][0]
            dependency["path"] = "EconCSLib/Renamed.lean"
            path.write_text(json.dumps(current))
            renamed = self.requirement(root, "Fixture", protocol)

            dependency["sha256"] = "3" * 64
            path.write_text(json.dumps(current))
            changed = self.requirement(root, "Fixture", protocol)

        self.assertFalse(renamed.required, renamed.reason)
        self.assertFalse(changed.required)
        self.assertIn("current item-level v10", changed.reason)

    def test_available_validator_prompt_identity_requires_current_v10_not_v11(self) -> None:
        payloads = artifact_payloads()
        payloads["audit/statement_match_llm.json"]["schema"] = 1
        payloads["audit/statement_match_llm.json"]["prompt_version"] = (
            "statement-match-v10-semantic-fidelity-seat-stopping"
        )
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(root, {"Fixture": payloads})
            path = root / "papers/Fixture/audit/statement_match_llm.json"
            current = json.loads(path.read_text())
            current["prompt_version"] = "statement-match-v10-weaker"
            path.write_text(json.dumps(current))

            result = self.requirement(root, "Fixture", protocol)

        self.assertFalse(result.required)
        self.assertIn("current item-level v10", result.reason)

    def test_raw_manifest_tampering_fails_exact_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, manifest, manifest_path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            manifest["entries"][0]["navigation"]["title"] = "tampered label"
            manifest_path.write_bytes(encode_trust_ledger(manifest))

            result = self.requirement(root, "Fixture", protocol)

        self.assertTrue(result.required)
        self.assertIn("raw digest mismatches", result.reason)

    def test_generator_identity_excludes_manifest_and_generated_aggregates(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, original, manifest_path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            manifest_path.write_text("not an input to generation\n")
            for relative in (
                "papers/status.json",
                "papers/human_status.json",
                "docs/PAPER_STATUS.md",
                "site/index.html",
            ):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"changed generated aggregate {relative}\n")

            regenerated = generate_trust_ledger_payload(
                root=root,
                selected_paper_folders=["Fixture"],
                protocol=protocol,
                closure_provider=self.closure_provider(root),
            )

        self.assertEqual(original, regenerated)

    def test_cross_entry_component_swap_is_rejected_even_with_new_raw_digest(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, manifest, manifest_path = self.prepare_root(
                root,
                {"First": artifact_payloads(), "Second": two_item_artifact_payloads()},
            )
            entries = manifest["entries"]
            key = "statement_semantic_identities"
            (
                entries[0]["component_sha256s"][key],
                entries[1]["component_sha256s"][key],
            ) = (
                entries[1]["component_sha256s"][key],
                entries[0]["component_sha256s"][key],
            )
            self.rewrite_manifest(protocol, manifest_path, manifest)

            result = self.requirement(root, "First", protocol)

        self.assertTrue(result.required)
        self.assertIn("association is invalid", result.reason)

    def test_absent_entry_requires_v11(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root,
                {"First": artifact_payloads(), "Second": two_item_artifact_payloads()},
                selected=["First"],
            )

            result = self.requirement(root, "Second", protocol)

        self.assertTrue(result.required)
        self.assertIn("no semantic source identity", result.reason)

    def test_duplicate_or_ambiguous_entries_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            manifest["entries"].append(copy.deepcopy(manifest["entries"][0]))

            with self.assertRaisesRegex(
                LegacyV10TrustLedgerError, "duplicate or ambiguous"
            ):
                validate_trust_ledger_payload(manifest, root=root, protocol=protocol)

    def test_stale_protocol_and_engine_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            changed_protocol = copy.deepcopy(protocol)
            changed_protocol["classification"]["source_condition_or_refinement"][
                "operational_review_epoch"
            ] = "v2"
            protocol_result = self.requirement(root, "Fixture", changed_protocol)
            (root / ENGINE_SOURCE_PATHS[0]).write_text(
                (root / ENGINE_SOURCE_PATHS[0]).read_text() + "\n# changed engine\n"
            )
            engine_result = self.requirement(root, "Fixture", protocol)

        self.assertTrue(protocol_result.required)
        self.assertIn("protocol identity is stale", protocol_result.reason)
        self.assertTrue(engine_result.required)
        self.assertIn("engine identity is stale", engine_result.reason)

    def test_dashboard_coverage_dependency_is_pinned_by_engine_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            dashboard = root / "scripts/review_dashboard.py"
            dashboard.write_text(
                dashboard.read_text(encoding="utf-8")
                + "\n# changed coverage selection semantics\n",
                encoding="utf-8",
            )

            result = self.requirement(root, "Fixture", protocol)

        self.assertTrue(result.required)
        self.assertIn("engine identity is stale", result.reason)

    def test_manifest_runtime_is_public_portable_and_never_reads_git_objects(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"PublicFixture": artifact_payloads()}
            )
            with mock.patch(
                "theorem_realization_transition.subprocess.run",
                side_effect=AssertionError("manifest mode must not invoke Git"),
            ):
                result = self.requirement(root, "PublicFixture", protocol)

        self.assertFalse(result.required, result.reason)

    def test_generator_requires_exact_nonduplicate_completed_list(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            protocol, _manifest, _path = self.prepare_root(
                root, {"Fixture": artifact_payloads()}
            )
            with self.assertRaisesRegex(
                LegacyV10TrustLedgerError, "duplicate navigation labels"
            ):
                generate_trust_ledger_payload(
                    root=root,
                    selected_paper_folders=["Fixture", "Fixture"],
                    protocol=protocol,
                )


if __name__ == "__main__":
    unittest.main()
