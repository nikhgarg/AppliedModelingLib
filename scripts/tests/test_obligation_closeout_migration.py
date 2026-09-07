from __future__ import annotations

import types
import unittest
from unittest import mock

from scripts.obligation_closeout_migration import (
    migrate_accepted_closeout_to_obligation_bundle,
)
from scripts.tests.obligation_historical_fixtures import (
    IM05_AUDIT_DIR,
    IM05_PAPER as PAPER,
    IM05_REPOSITORY_ROOT,
    load_im05_audit_json,
    require_im05_fixture,
)


ENGINE_SHA256 = "e" * 64


class ObligationCloseoutMigrationTests(unittest.TestCase):
    def test_current_im05_assembles_complete_bundle_without_llm_or_legacy_replay(
        self,
    ) -> None:
        require_im05_fixture()
        build_provider = mock.Mock()
        build_provider.finalize_unchanged.return_value = True

        def fake_store(_root, _paper, paper_index, graph, _issuances, **_kwargs):
            self.assertTrue(paper_index.complete_paper_surface)
            self.assertEqual(paper_index.graph_sha256, graph.graph_sha256)
            return IM05_AUDIT_DIR / "obligation_evidence" / "current_bundle.json"

        def fake_verify(_root, _paper, paper_index, graph, **_kwargs):
            self.assertEqual(paper_index.graph_sha256, graph.graph_sha256)
            return types.SimpleNamespace(
                paper_index_sha256=paper_index.index_sha256
            )

        engine = types.SimpleNamespace(engine_tree_sha256=ENGINE_SHA256)
        with (
            mock.patch(
                "scripts.obligation_closeout_migration.validate_runtime_engine_registration",
                return_value=engine,
            ),
            mock.patch(
                "scripts.obligation_closeout_materialization.validate_runtime_engine_registration",
                return_value=engine,
            ),
            mock.patch(
                "scripts.obligation_closeout_materialization.validated_runtime_engine_revision_ledger",
                return_value={
                    "schema": 1,
                    "revisions": [
                        {"engine_tree_sha256": ENGINE_SHA256}
                    ],
                },
            ),
            mock.patch(
                "scripts.obligation_closeout_migration.validate_final_closure_receipt",
                return_value=types.SimpleNamespace(payload={"schema": 4}),
            ),
            mock.patch(
                "scripts.obligation_closeout_materialization.RepositoryBuildInputSnapshotProvider",
                return_value=build_provider,
            ) as provider_constructor,
            mock.patch(
                "scripts.obligation_closeout_materialization.store_paper_obligation_bundle",
                side_effect=fake_store,
            ),
            mock.patch(
                "scripts.obligation_closeout_materialization.verify_current_stored_paper_obligations",
                side_effect=fake_verify,
            ),
            mock.patch("subprocess.run", side_effect=AssertionError("subprocess invoked")),
        ):
            result = migrate_accepted_closeout_to_obligation_bundle(
                IM05_REPOSITORY_ROOT, PAPER
            )

        self.assertEqual(result.source_route_count, 25)
        self.assertEqual(result.operation, "authenticated_legacy_closeout_migration")
        self.assertEqual(result.direct_claim_count, 12)
        self.assertEqual(result.semantic_prerequisite_count, 45)
        self.assertEqual(result.reused_prerequisite_leaf_count, 45)
        self.assertEqual(result.materialized_prerequisite_leaf_count, 0)
        self.assertGreater(result.leaf_count, 100)
        saved_closure = load_im05_audit_json("LEAN_IMPORT_CLOSURE_RECEIPT.json")
        self.assertEqual(
            provider_constructor.call_args.kwargs["lean_import_closure_payload"],
            saved_closure["lean_import_closure"],
        )

if __name__ == "__main__":
    unittest.main()
