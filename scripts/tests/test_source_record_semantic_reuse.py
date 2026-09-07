from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import source_record_semantic_reuse as reuse


SHA_A = "a" * 64
SHA_B = "b" * 64
SHA_C = "c" * 64


def fingerprint() -> dict[str, object]:
    return {
        "schema": 10,
        "paper": "Paper",
        "source_record_item_digest_schema": 5,
        "paper_statement_map_semantic_sha256": SHA_A,
        "relevant_status_sha256": SHA_A,
        "source_proof_fidelity_sha256": SHA_A,
        "review_interface_source": {"path": "PaperInterface.lean", "sha256": SHA_A},
        "review_assumption_source": None,
        "lean_dependency_identities": [{"path": "PaperInterface.lean", "sha256": SHA_A}],
        "lean_import_closure_sha256": SHA_A,
        "source_artifact_identities": [{"path": "source.txt", "sha256": SHA_A}],
        "toolchain_identities": [{"path": "lean-toolchain", "sha256": SHA_A}],
        "audit_engine_identities": [{"path": "engine", "surface_semantic_version": "v1"}],
        "formalization_coverage_protocol_sha256": SHA_A,
        "max_depth": 6,
        "no_lean": False,
        "raw_producer_code_identity_schema": 1,
        "raw_producer_code_identities": [
            {"path": "producer.py", "sha256": SHA_A, "status": "present"}
        ],
    }


def raw_audit() -> dict[str, object]:
    return {
        "configured_review_rows": [
            {
                "qualified_declaration": "Paper.Spec",
                "elaborated_signature_sha256": SHA_A,
                "semantic_dependency_sha256": SHA_B,
                "elaborated_proposition_graph_sha256": SHA_C,
            }
        ],
        "semantic_model_items": [
            {"dimensions": [{"id": "expanded_binders_and_domain"}]}
        ],
        "source_proof_fidelity": None,
    }


class SemanticFingerprintProjectionTests(unittest.TestCase):
    def test_container_and_separately_revalidated_coordinates_do_not_stale(self) -> None:
        stored = fingerprint()
        current = copy.deepcopy(stored)
        for field in reuse._SEPARATELY_REVALIDATED_FINGERPRINT_FIELDS:
            current[field] = SHA_B
        current["raw_producer_code_identities"] = [
            {"path": "producer.py", "sha256": SHA_B, "status": "present"}
        ]
        self.assertTrue(reuse.semantic_fingerprint_matches(stored, current))

    def test_source_artifact_change_still_fails_closed(self) -> None:
        stored = fingerprint()
        current = copy.deepcopy(stored)
        current["source_artifact_identities"] = [
            {"path": "source.txt", "sha256": SHA_B}
        ]
        self.assertFalse(reuse.semantic_fingerprint_matches(stored, current))

    def test_protocol_change_still_fails_closed(self) -> None:
        stored = fingerprint()
        current = copy.deepcopy(stored)
        current["formalization_coverage_protocol_sha256"] = SHA_B
        self.assertFalse(reuse.semantic_fingerprint_matches(stored, current))


class SemanticReuseOperationalCacheTests(unittest.TestCase):
    def cached_result(self) -> dict[str, object]:
        return {
            "schema": 1,
            "paper": "Paper",
            "identity_scope": "repository_sources_and_configuration_only",
            "external_artifacts_revalidated": False,
            "current": True,
            "semantic_receipt_reuse": {
                "schema": 1,
                "policy": reuse.POLICY,
                "paper": "Paper",
                "current": True,
                "reviewed_declaration_count": 1,
                "semantic_identity_sha256": SHA_A,
            },
        }

    def test_exact_watched_material_reuses_current_result(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper = root / "papers" / "Paper"
            watched = paper / "PaperInterface.lean"
            watched.parent.mkdir(parents=True)
            watched.write_text("def Claim : Prop := True\n", encoding="utf-8")

            error = reuse.write_semantic_reuse_cache(
                root=root,
                paper_dir=paper,
                raw_audit_file_sha256=SHA_B,
                watched_paths={watched},
                result=self.cached_result(),
            )
            loaded = reuse.load_semantic_reuse_cache(
                root=root,
                paper_dir=paper,
                raw_audit_file_sha256=SHA_B,
            )

        self.assertEqual(error, "")
        self.assertEqual(loaded, self.cached_result())

    def test_watched_change_or_raw_change_is_a_cache_miss(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper = root / "papers" / "Paper"
            watched = paper / "PaperInterface.lean"
            watched.parent.mkdir(parents=True)
            watched.write_text("def Claim : Prop := True\n", encoding="utf-8")
            self.assertEqual(
                reuse.write_semantic_reuse_cache(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_B,
                    watched_paths={watched},
                    result=self.cached_result(),
                ),
                "",
            )

            self.assertIsNone(
                reuse.load_semantic_reuse_cache(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_C,
                )
            )
            watched.write_text("def Claim : Prop := False\n", encoding="utf-8")
            self.assertIsNone(
                reuse.load_semantic_reuse_cache(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_B,
                )
            )

    def test_unwatched_engine_file_does_not_invalidate_semantic_result(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper = root / "papers" / "Paper"
            watched = paper / "PaperInterface.lean"
            watched.parent.mkdir(parents=True)
            watched.write_text("def Claim : Prop := True\n", encoding="utf-8")
            self.assertEqual(
                reuse.write_semantic_reuse_cache(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_B,
                    watched_paths={watched},
                    result=self.cached_result(),
                ),
                "",
            )
            engine = root / "scripts" / "audit.py"
            engine.parent.mkdir()
            engine.write_text("# new verifier implementation\n", encoding="utf-8")

            loaded = reuse.load_semantic_reuse_cache(
                root=root,
                paper_dir=paper,
                raw_audit_file_sha256=SHA_B,
            )

        self.assertEqual(loaded, self.cached_result())

    def test_acceptance_authority_recomputes_semantic_identity_from_raw_rows(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper = root / "papers" / "Paper"
            watched = paper / "PaperInterface.lean"
            statement_map = paper / "audit" / "paper_statement_map.json"
            watched.parent.mkdir(parents=True)
            statement_map.parent.mkdir(parents=True)
            watched.write_text("def Claim : Prop := True\n", encoding="utf-8")
            statement_map.write_text('{"items": {}}\n', encoding="utf-8")
            raw = raw_audit()
            reviewed, semantic_identity = reuse._semantic_identity_from_rows(raw)
            result = self.cached_result()
            result["semantic_receipt_reuse"]["semantic_identity_sha256"] = (
                semantic_identity
            )
            self.assertEqual(
                reuse.write_semantic_reuse_cache(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_B,
                    watched_paths={watched, statement_map},
                    result=result,
                ),
                "",
            )

            authority = reuse.load_current_semantic_reuse_authority(
                root=root,
                paper_dir=paper,
                raw_audit_file_sha256=SHA_B,
                raw_audit=raw,
            )
            self.assertIsNotNone(authority)
            assert authority is not None
            self.assertEqual(authority.reviewed_declarations, reviewed)

            # The acceptance-facing semantic receipt owns the elaborated Lean
            # declarations, not the statement map.  A map rewrite therefore
            # leaves this narrow authority current; source coverage,
            # source-to-Spec, and Spec/proof validators still inspect the
            # exact new map before any closeout can pass.  The scheduling cache
            # remains byte-exact and misses after this edit.
            statement_map.write_text(
                '{"items": {"new_claim": {"source_kind": "theorem"}}}\n',
                encoding="utf-8",
            )
            self.assertIsNone(
                reuse.load_semantic_reuse_cache(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_B,
                )
            )
            authority = reuse.load_current_semantic_reuse_authority(
                root=root,
                paper_dir=paper,
                raw_audit_file_sha256=SHA_B,
                raw_audit=raw,
            )
            self.assertIsNotNone(authority)

            watched.write_text("def Claim : Prop := False\n", encoding="utf-8")
            self.assertIsNone(
                reuse.load_current_semantic_reuse_authority(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_B,
                    raw_audit=raw,
                )
            )
            watched.write_text("def Claim : Prop := True\n", encoding="utf-8")

            authority_path = reuse.semantic_validation_authority_path(paper)
            payload = json.loads(authority_path.read_text(encoding="utf-8"))
            payload["result"]["semantic_receipt_reuse"][
                "semantic_identity_sha256"
            ] = SHA_C
            authority_path.write_text(json.dumps(payload), encoding="utf-8")
            self.assertIsNone(
                reuse.load_current_semantic_reuse_authority(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=SHA_B,
                    raw_audit=raw,
                )
            )

    def test_semantic_control_rebind_avoids_lean_for_presentation_only_status_edit(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper = root / "papers" / "Paper"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            interface = paper / "PaperInterface.lean"
            status = paper / "status.json"
            statement_map = audit / "paper_statement_map.json"
            fidelity = audit / "source_proof_fidelity.json"
            doubled_fidelity = (
                paper
                / "papers"
                / "Paper"
                / "audit"
                / "source_proof_fidelity.json"
            )
            interface.write_text("def Claim : Prop := True\n", encoding="utf-8")
            status.write_text('{"display": "before"}\n', encoding="utf-8")
            statement_map.write_text('{"items": {}}\n', encoding="utf-8")
            fidelity.write_text('{"defects": []}\n', encoding="utf-8")

            raw = raw_audit()
            raw["source_record_input_fingerprint"] = {
                "relevant_status_sha256": SHA_A,
                "source_proof_fidelity_sha256": SHA_C,
            }
            raw_path = audit / "source_record_audit.json"
            raw_path.write_text(json.dumps(raw), encoding="utf-8")
            raw_digest = reuse.hashlib.sha256(raw_path.read_bytes()).hexdigest()
            _reviewed, semantic_identity = reuse._semantic_identity_from_rows(raw)
            result = self.cached_result()
            result["semantic_receipt_reuse"]["semantic_identity_sha256"] = (
                semantic_identity
            )
            self.assertEqual(
                reuse.write_semantic_reuse_cache(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=raw_digest,
                    watched_paths={
                        interface,
                        status,
                        statement_map,
                        doubled_fidelity,
                    },
                    result=result,
                ),
                "",
            )

            status.write_text('{"display": "after"}\n', encoding="utf-8")
            self.assertIsNone(
                reuse.load_current_semantic_reuse_authority(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=raw_digest,
                    raw_audit=raw,
                )
            )
            self.assertEqual(
                reuse.rebind_semantic_validation_authority_controls(
                    root=root,
                    paper_dir=paper,
                    raw_audit=raw,
                    current_status_control_sha256=SHA_B,
                    current_status_file_sha256=reuse.hashlib.sha256(
                        status.read_bytes()
                    ).hexdigest(),
                    current_source_proof_fidelity_sha256=SHA_C,
                    current_source_proof_fidelity_file_sha256=reuse.hashlib.sha256(
                        fidelity.read_bytes()
                    ).hexdigest(),
                    source_proof_fidelity_path=fidelity,
                ),
                "current status controls differ from the canonical raw receipt",
            )
            self.assertEqual(
                reuse.rebind_semantic_validation_authority_controls(
                    root=root,
                    paper_dir=paper,
                    raw_audit=raw,
                    current_status_control_sha256=SHA_A,
                    current_status_file_sha256=reuse.hashlib.sha256(
                        status.read_bytes()
                    ).hexdigest(),
                    current_source_proof_fidelity_sha256=SHA_C,
                    current_source_proof_fidelity_file_sha256=reuse.hashlib.sha256(
                        fidelity.read_bytes()
                    ).hexdigest(),
                    source_proof_fidelity_path=fidelity,
                ),
                "",
            )
            authority = reuse.load_current_semantic_reuse_authority(
                root=root,
                paper_dir=paper,
                raw_audit_file_sha256=raw_digest,
                raw_audit=raw,
            )
            self.assertIsNotNone(authority)
            rebound = json.loads(
                reuse.semantic_validation_authority_path(paper).read_text(
                    encoding="utf-8"
                )
            )
            watched = rebound["watched_repository_material"]
            self.assertIn("papers/Paper/audit/source_proof_fidelity.json", watched)
            self.assertNotIn(
                "papers/Paper/papers/Paper/audit/source_proof_fidelity.json",
                watched,
            )

            status.write_text('{"display": "later"}\n', encoding="utf-8")
            self.assertIsNone(
                reuse.load_current_semantic_reuse_authority(
                    root=root,
                    paper_dir=paper,
                    raw_audit_file_sha256=raw_digest,
                    raw_audit=raw,
                )
            )

class CurrentSemanticVerifierTests(unittest.TestCase):
    def test_explicit_assumption_roles_select_only_nonsuperseded_raw_roots(self) -> None:
        raw = raw_audit()
        raw["configured_review_rows"][0]["row"] = "assumption_boundary"
        raw["semantic_model_configured_assumption_rows"] = [
            "assumption_boundary"
        ]
        selected = reuse.configured_assumption_review_rows(raw)
        self.assertEqual(set(selected), {"Paper.Spec"})

    def test_v11_context_can_skip_historical_mixed_raw_root_inventory(self) -> None:
        error = reuse.current_semantic_review_context_error(
            raw_audit=raw_audit(),
            current_configured_review_declarations=None,
            current_semantic_model_dimension_ids={"expanded_binders_and_domain"},
            current_source_proof_fidelity=None,
            current_source_map_defect_ids=set(),
        )
        self.assertEqual(error, "")

    def test_live_context_inputs_are_normalized_once_for_all_reuse_lanes(self) -> None:
        dimensions, defects = reuse.current_semantic_review_context_inputs(
            status={
                "review_surface": {
                    "semantic_model_review": {
                        "required_dimensions": ["carrier", "domain"]
                    }
                }
            },
            source_map={
                "items": {
                    "claim": {"source_defect_ids": ["D1"]},
                    "other": {},
                }
            },
            source_proof_fidelity={"defects": [{"id": "D1"}]},
        )
        self.assertEqual(dimensions, {"carrier", "domain"})
        self.assertEqual(defects, {"D1"})

    def run_validator(
        self,
        *,
        configured: set[str] | None = None,
        dimensions: set[str] | None = None,
        fidelity: dict[str, object] | None = None,
        defect_ids: set[str] | None = None,
        manifest_matches: bool = True,
    ) -> tuple[dict[str, object] | None, str]:
        raw = raw_audit()
        stored_context = {
            "context_id": "context",
            "import_module": "Paper.ProofInterface",
            "semantic_dependency_modules": ["Paper.ProofInterface"],
            "manifest_cache_context_sha256": SHA_C,
        }
        entry = {
            "context_id": "context",
            "elaborated_signature_sha256": SHA_A,
            "semantic_dependency_sha256": SHA_B,
            "elaborated_proposition_graph_sha256": SHA_C,
        }
        with (
            patch.object(
                reuse,
                "validated_authenticated_manifest_store_entries",
                return_value=(
                    "Paper",
                    {"context": stored_context},
                    {"Paper.Spec": (entry, {"manifest": "stored"})},
                ),
            ),
            patch.object(
                reuse,
                "run_lean_signature_manifests",
                return_value={"Paper.Spec": {"manifest": "current"}},
            ) as run_manifests,
            patch.object(
                reuse,
                "manifest_matches_reviewed_semantic_payload",
                return_value=manifest_matches,
            ),
        ):
            result = reuse.validate_current_semantic_reuse(
                root=Path("."),
                paper_dir=Path("Paper"),
                raw_audit=raw,
                current_import_module="Paper.ProofInterface",
                current_semantic_dependency_modules=("Paper.ProofInterface",),
                current_configured_review_declarations=(
                    {"Paper.Spec"} if configured is None else configured
                ),
                current_semantic_model_dimension_ids=(
                    {"expanded_binders_and_domain"}
                    if dimensions is None
                    else dimensions
                ),
                current_source_proof_fidelity=fidelity,
                current_source_map_defect_ids=(set() if defect_ids is None else defect_ids),
            )
        if result[0] is not None:
            run_manifests.assert_called_once()
        return result

    def test_current_semantic_identities_accept(self) -> None:
        result, error = self.run_validator()
        self.assertEqual(error, "")
        self.assertTrue(result and result["current"])

    def test_changed_configured_root_fails(self) -> None:
        result, error = self.run_validator(configured={"Paper.Other"})
        self.assertIsNone(result)
        self.assertIn("configured review roots differ", error)

    def test_changed_semantic_dimension_fails(self) -> None:
        result, error = self.run_validator(dimensions={"carrier_and_domain"})
        self.assertIsNone(result)
        self.assertIn("semantic-model dimensions differ", error)

    def test_new_proof_convention_fails(self) -> None:
        result, error = self.run_validator(
            fidelity={"model_conventions": [{"id": "new"}], "defects": []}
        )
        self.assertIsNone(result)
        self.assertIn("model_conventions changed", error)

    def test_dedicated_defect_lane_accepts_new_defect_context(self) -> None:
        result, error = self.run_validator(
            fidelity={"defects": [{"id": "D1"}]}, defect_ids={"D1"}
        )
        self.assertEqual(error, "")
        self.assertEqual(result and result["separately_routed_proof_defect_count"], 1)

    def test_unrouted_proof_defect_fails(self) -> None:
        result, error = self.run_validator(
            fidelity={"defects": [{"id": "D1"}]}, defect_ids=set()
        )
        self.assertIsNone(result)
        self.assertIn("not routed to the defect-review lane", error)

    def test_changed_lean_manifest_fails(self) -> None:
        result, error = self.run_validator(manifest_matches=False)
        self.assertIsNone(result)
        self.assertIn("Lean semantic identity changed", error)


if __name__ == "__main__":
    unittest.main()
