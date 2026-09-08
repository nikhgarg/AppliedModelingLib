#!/usr/bin/env python3
"""Tests for per-paper strict dashboard-row reuse in the repository audit."""

from __future__ import annotations

import json
import sys
import tempfile
import types
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import (
    audit_evidence_integrity,
    audit_repository,
    review_surface_structure,
)


def finding_identity(
    findings: list[audit_repository.Finding],
) -> list[tuple[str, str, str]]:
    return [
        (finding.severity, str(finding.path), finding.message) for finding in findings
    ]


def legacy_source_record_state(
    audit_payload: dict[str, object],
    *,
    audit_path: Path | None = None,
    match_path: Path | None = None,
    source_record_identity_error: str = "",
    current_source_record_judgments: dict[str, dict[str, object]] | None = None,
    corrected_scope_current: bool = False,
    semantic_reuse_authority: object | None = None,
) -> SimpleNamespace:
    """Build the explicit raw-evidence lane used by closeout test fixtures."""

    return SimpleNamespace(
        inputs=SimpleNamespace(
            audit_snapshot=SimpleNamespace(
                path=audit_path or Path("audit/source_record_audit.json"),
                payload=audit_payload,
            ),
            match_snapshot=SimpleNamespace(
                path=match_path or Path("audit/source_record_match_llm.json"),
                payload={},
            ),
            audit_path_error="",
            match_path_error="",
        ),
        source_record_identity_error=source_record_identity_error,
        semantic_reuse_authority=semantic_reuse_authority,
        current_source_record_judgments=(current_source_record_judgments or {}),
        corrected_scope_current=corrected_scope_current,
        semantic_contract_revalidation=None,
        semantic_contract_revalidation_error="",
        administrative_projection_rebind=None,
        administrative_projection_rebind_path=None,
        administrative_projection_rebind_error="",
        configured_assumption_regularity_context=None,
        configured_assumption_regularity_context_error="",
    )


class StrictReviewItemReuseTests(unittest.TestCase):
    def test_assumption_declarations_accept_exact_qualified_status_names(self) -> None:
        source = "namespace Fixture\n\naxiom source_condition : Prop\n"

        declarations = review_surface_structure.assumption_declarations_from_text(
            source, {"Fixture.source_condition"}
        )

        self.assertEqual(set(declarations), {"Fixture.source_condition"})

    def test_assumption_declarations_disambiguate_dotted_names(self) -> None:
        source = (
            "theorem First.shared : True := by trivial\n"
            "theorem Second.shared : True := by trivial\n"
        )

        declarations = review_surface_structure.assumption_declarations_from_text(
            source, {"First.shared", "Second.shared"}
        )

        self.assertEqual(set(declarations), {"First.shared", "Second.shared"})

    def test_lazy_provider_memoizes_success_and_failure(self) -> None:
        folder = Path("papers/opaque-paper-id")
        rows = (object(), object())
        with mock.patch.object(
            audit_repository,
            "strict_review_items_for_paper",
            return_value=rows,
        ) as extract:
            provider = audit_repository.LazyStrictReviewItems(folder)
            first = provider()
            second = provider()

        self.assertIs(first, rows)
        self.assertIs(second, rows)
        extract.assert_called_once_with(
            folder, build_input_provider=None, audit_inputs=None
        )

        failure = RuntimeError("manifest extraction failed")
        with mock.patch.object(
            audit_repository,
            "strict_review_items_for_paper",
            side_effect=failure,
        ) as extract:
            provider = audit_repository.LazyStrictReviewItems(folder)
            with self.assertRaisesRegex(RuntimeError, "manifest extraction failed"):
                provider()
            with self.assertRaisesRegex(RuntimeError, "manifest extraction failed"):
                provider()

        extract.assert_called_once_with(
            folder, build_input_provider=None, audit_inputs=None
        )

    def test_lazy_provider_forwards_closeout_manifest_authority(self) -> None:
        folder = Path("papers/opaque-paper-id")
        configured_rows = (
            {
                "qualified_declaration": "Opaque.PaperInterface.reviewed",
                "elaborated_signature_sha256": "a" * 64,
            },
        )
        with mock.patch.object(
            audit_repository,
            "strict_review_items_for_paper",
            return_value=(),
        ) as extract:
            provider = audit_repository.LazyStrictReviewItems(
                folder,
                validated_configured_review_rows=configured_rows,
            )
            provider()

        extract.assert_called_once_with(
            folder,
            build_input_provider=None,
            audit_inputs=None,
            validated_configured_review_rows=configured_rows,
        )

    def test_strict_closeout_dashboard_extraction_is_read_only(self) -> None:
        folder = Path("papers/opaque-paper-id")
        provider = mock.Mock()
        with mock.patch(
            "scripts.review_dashboard.review_items_for_paper",
            return_value=[],
        ) as review:
            rows = audit_repository.strict_review_items_for_paper(
                folder, build_input_provider=provider
            )

        self.assertEqual(rows, ())
        review.assert_called_once_with(
            folder,
            use_cache=True,
            render_images=False,
            require_current_signatures=True,
            persist_cache_rebind=False,
            build_input_provider=provider,
            audit_inputs=None,
        )

    def test_strict_closeout_passes_validated_rows_to_dashboard(self) -> None:
        folder = Path("papers/opaque-paper-id")
        configured_rows = (
            {
                "qualified_declaration": "Opaque.PaperInterface.reviewed",
                "elaborated_signature_sha256": "a" * 64,
            },
        )
        with mock.patch(
            "scripts.review_dashboard.review_items_for_paper",
            return_value=[],
        ) as review:
            rows = audit_repository.strict_review_items_for_paper(
                folder,
                validated_configured_review_rows=configured_rows,
            )

        self.assertEqual(rows, ())
        review.assert_called_once_with(
            folder,
            use_cache=True,
            render_images=False,
            require_current_signatures=True,
            persist_cache_rebind=False,
            build_input_provider=None,
            audit_inputs=None,
            validated_configured_review_rows=configured_rows,
        )


class PaperCloseoutRunContextTests(unittest.TestCase):
    def test_current_v11_declaration_index_uses_lean_inventory_and_exact_bytes(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper_id = "OpaquePaper_lean_inventory"
            folder = papers / paper_id
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            proof = folder / "ProofInterface.lean"
            interface_text = (
                f"namespace {paper_id}\n"
                "def claimSpec : Prop :=\n  True\n"
                f"end {paper_id}\n"
            )
            proof_text = (
                f"namespace {paper_id}\n"
                "theorem claim : claimSpec := by trivial\n"
                f"end {paper_id}\n"
            )
            interface.write_text(interface_text, encoding="utf-8")
            proof.write_text(proof_text, encoding="utf-8")
            entry_module = f"{paper_id}.ProofInterface"
            closure = {
                "entrypoint": proof.relative_to(root).as_posix(),
                "entry_module": entry_module,
                "sources": [
                    {
                        "module": f"{paper_id}.PaperInterface",
                        "path": interface.relative_to(root).as_posix(),
                    },
                    {
                        "module": entry_module,
                        "path": proof.relative_to(root).as_posix(),
                    },
                ],
            }
            specification = f"{paper_id}.claimSpec"
            theorem = f"{paper_id}.claim"
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                audit_payload={"lean_import_closure": closure},
                statement_map={
                    "items": {
                        "claim": {
                            "semantic_contract": {
                                "spec_declaration": specification,
                                "evidence_declaration": theorem,
                                "evidence_mode": "proves",
                            }
                        }
                    }
                },
            )
            provider = mock.Mock()
            provider.repository_source_snapshot.return_value = (
                (
                    f"{paper_id}.PaperInterface",
                    interface.resolve(),
                    interface_text.encode("utf-8"),
                    "a" * 64,
                ),
                (
                    entry_module,
                    proof.resolve(),
                    proof_text.encode("utf-8"),
                    "b" * 64,
                ),
            )
            inventory = {
                "source_declarations": [],
                "declarations": [
                    {
                        "declaration": specification,
                        "review_owner_declaration": specification,
                        "generated_from_owner": False,
                        "paper_owned": True,
                        "module": f"{paper_id}.PaperInterface",
                        "declaration_kind": "definition",
                        "source_presented": True,
                        "source_range": {
                            "line_start": 2,
                            "column_start": 0,
                            "line_end": 3,
                            "column_end": 6,
                        },
                    },
                    {
                        "declaration": theorem,
                        "review_owner_declaration": theorem,
                        "generated_from_owner": False,
                        "paper_owned": True,
                        "module": entry_module,
                        "declaration_kind": "theorem",
                        "source_presented": True,
                        "source_range": {
                            "line_start": 2,
                            "column_start": 0,
                            "line_end": 2,
                            "column_end": len(
                                "theorem claim : claimSpec := by trivial"
                            ),
                        },
                    },
                ],
            }
            surface = SimpleNamespace(
                declaration_inventory=inventory,
                module_sources={
                    f"{paper_id}.PaperInterface": (
                        interface.resolve(),
                        interface_text.encode("utf-8"),
                    ),
                    entry_module: (proof.resolve(), proof_text.encode("utf-8")),
                },
                library_source_declarations={},
                build_input_provider=provider,
            )
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_direct_semantic_review_state",
                    return_value=(True, ""),
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_lean_review_surface",
                    return_value=surface,
                ),
                mock.patch.object(
                    audit_repository,
                    "lean_declaration_index_from_source_bytes",
                    side_effect=AssertionError(
                        "current v11 declaration indexing must use Lean's typed inventory"
                    ),
                ) as native,
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    paper_id, folder, evidence_context=evidence_context
                )
                exact_sources = context.lean_owned_source_snapshots()
                declaration_index = context.paper_declaration_index()

            resolved_spec = audit_repository.resolve_declaration_name(
                declaration_index, "claimSpec"
            )
            resolved_proof = audit_repository.resolve_declaration_name(
                declaration_index, "claim"
            )
            self.assertEqual(len(resolved_spec), 1)
            self.assertEqual(len(resolved_proof), 1)
            self.assertEqual(
                exact_sources,
                {
                    interface.resolve(): interface_text.encode("utf-8"),
                    proof.resolve(): proof_text.encode("utf-8"),
                },
            )
            self.assertEqual(resolved_spec[0].source, "def claimSpec : Prop :=\n  True")
            self.assertEqual(resolved_proof[0].kind, "theorem")
            self.assertEqual(
                audit_repository.qualified_declaration_identity(resolved_proof[0]),
                theorem,
            )
            native.assert_not_called()
            provider.repository_source_snapshot.assert_not_called()

    def test_current_v11_context_uses_live_lean_instead_of_stale_raw_closure(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OpaquePaper_v11"
            folder.mkdir()
            legacy_closure = {"entry_module": "OpaquePaper_v11.PaperInterface"}
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                status="formalized",
                audit_payload={"lean_import_closure": legacy_closure},
                source_record_identity_error="legacy import bytes changed",
                semantic_reuse_authority=None,
            )
            shared_provider = mock.Mock()
            surface = SimpleNamespace(build_input_provider=shared_provider)
            with (
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_direct_semantic_review_state",
                    return_value=(True, ""),
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_lean_review_surface",
                    return_value=surface,
                ),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=mock.Mock(),
                ) as provider_factory,
            ):
                context = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
                    folder.name, folder, evidence_context=evidence_context
                )

        self.assertTrue(context.v11_direct_semantic_review_current)
        self.assertIs(context.build_input_provider, shared_provider)
        provider_factory.assert_not_called()

    def test_selected_v11_context_retains_graph_when_semantic_judgment_fails(self) -> None:
        """A real v11 finding must not be masked by retired source transport."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "OpaquePaper_v11_finding"
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            paper_id = folder.name
            interface_bytes = (
                f"namespace {paper_id}\n"
                "def reviewedSpec : Prop := True\n"
                f"end {paper_id}\n"
            ).encode("utf-8")
            interface.write_bytes(interface_bytes)
            library = root / "AppliedModelingLib" / "Fixture.lean"
            library.parent.mkdir()
            library.write_text(
                "namespace AppliedModelingLib\ndef fixture : Prop := True\nend AppliedModelingLib\n",
                encoding="utf-8",
            )
            legacy_closure = {"entry_module": "Retired.Legacy"}
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                status="formalized",
                audit_payload={"lean_import_closure": legacy_closure},
                source_record_identity_error="",
                semantic_reuse_authority=None,
                v11_lean_claim_graph_selected=True,
                source_semantic_lane=(
                    audit_evidence_integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
                ),
            )
            shared_provider = mock.Mock()
            reviewed_spec = f"{paper_id}.reviewedSpec"
            surface = SimpleNamespace(
                build_input_provider=shared_provider,
                module_sources={
                    f"{paper_id}.PaperInterface": (
                        interface.resolve(),
                        interface_bytes,
                    )
                },
                declaration_inventory={
                    "declarations": [
                        {
                            "declaration": reviewed_spec,
                            "review_owner_declaration": reviewed_spec,
                            "generated_from_owner": False,
                            "paper_owned": True,
                            "module": f"{paper_id}.PaperInterface",
                            "declaration_kind": "definition",
                            "source_presented": True,
                            "source_range": {
                                "line_start": 2,
                                "column_start": 0,
                                "line_end": 2,
                                "column_end": len(
                                    "def reviewedSpec : Prop := True"
                                ),
                            },
                        }
                    ]
                },
                library_source_declarations={
                    "AppliedModelingLib.fixture": {
                        "source_path": library.resolve(),
                        "source": "def fixture : Prop := True",
                        "source_range": {
                            "line_start": 2,
                            "column_start": 0,
                            "line_end": 2,
                            "column_end": len("def fixture : Prop := True"),
                        },
                        "declaration_kind": "definition",
                    }
                },
            )
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_direct_semantic_review_state",
                    return_value=(False, "library judgment is stale"),
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_lean_review_surface",
                    return_value=surface,
                ) as retained_graph,
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=mock.Mock(),
                ) as provider_factory,
                mock.patch.object(
                    audit_repository,
                    "lean_declaration_index_from_source_bytes",
                    side_effect=AssertionError(
                        "selected v11 graph fell back to Python source parsing"
                    ),
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
                    folder.name, folder, evidence_context=evidence_context
                )
                snapshots = context.lean_owned_source_snapshots()
                paper_declarations = context.paper_declaration_index()
                library_declarations = context.library_declaration_index()
                selected_v11_closeout = context.selected_v11_closeout
                current_v11_closeout = context.current_v11_closeout

        self.assertFalse(context.v11_direct_semantic_review_current)
        self.assertTrue(context.v11_lean_claim_graph_selected)
        self.assertTrue(selected_v11_closeout)
        self.assertFalse(current_v11_closeout)
        self.assertEqual(context.v11_direct_semantic_review_error, "library judgment is stale")
        self.assertEqual(snapshots, {interface.resolve(): interface_bytes})
        self.assertEqual(
            len(
                audit_repository.resolve_declaration_name(
                    paper_declarations, "reviewedSpec"
                )
            ),
            1,
        )
        self.assertEqual(
            len(
                audit_repository.resolve_declaration_name(
                    library_declarations, "AppliedModelingLib.fixture"
                )
            ),
            1,
        )
        self.assertIs(context.build_input_provider, shared_provider)
        retained_graph.assert_called_once_with(folder, evidence_context)
        provider_factory.assert_not_called()

    def test_exact_transaction_skew_stops_before_v11_graph_construction(self) -> None:
        """A predetermined raw/map mismatch must not launch derived Lean work."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OpaquePaper_skew"
            folder.mkdir()
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                audit_payload={},
                semantic_reuse_authority=None,
            )
            skew = audit_repository.Finding(
                "ERROR",
                folder / "audit" / "source_record_audit.json",
                "exact source-map transaction skew",
            )
            with (
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_source_record_transaction_skew_findings",
                    return_value=[skew],
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_direct_semantic_review_state",
                ) as semantic_state,
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    folder.name, folder, evidence_context=evidence_context
                )

        self.assertFalse(context.v11_direct_semantic_review_current)
        self.assertEqual(
            context.v11_direct_semantic_review_error,
            "exact source-map transaction skew",
        )
        semantic_state.assert_not_called()

    def test_selected_v11_missing_graph_never_instantiates_legacy_provider(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OpaquePaper_missing_graph"
            folder.mkdir()
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                status="formalized",
                audit_payload={"lean_import_closure": {"entry_module": "Retired"}},
                semantic_reuse_authority=None,
                v11_lean_claim_graph_selected=True,
            )
            with (
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_direct_semantic_review_state",
                    return_value=(False, "the selected Lean graph is unavailable"),
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_closeout_v11_lean_review_surface",
                    return_value=None,
                ),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                ) as provider_factory,
            ):
                context = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
                    folder.name, folder, evidence_context=evidence_context
                )
                selected_v11_closeout = context.selected_v11_closeout

        self.assertTrue(selected_v11_closeout)
        self.assertIsNone(context.build_input_provider)
        provider_factory.assert_not_called()

    def test_selected_v11_statement_check_defers_to_current_evidence_owner(
        self,
    ) -> None:
        folder = Path("/tmp/OpaquePaper_selected_statement")
        run_context = SimpleNamespace(selected_v11_closeout=True)
        with (
            mock.patch.object(
                audit_repository,
                "paper_statement_map_declaration_findings",
                side_effect=AssertionError(
                    "selected v11 replayed the legacy declaration checker"
                ),
            ),
            mock.patch.object(
                audit_repository,
                "evaluate_author_approved_corrected_scope",
                return_value=False,
            ),
            mock.patch.object(
                audit_repository,
                "semantic_contract_closeout_bridge_is_current",
                side_effect=AssertionError("selected v11 entered a legacy dashboard lane"),
            ),
        ):
            findings = audit_repository.paper_statement_sidecar_findings(
                folder.name,
                folder,
                "formalized",
                status_payload_override={"status": "formalized"},
                run_context=run_context,  # type: ignore[arg-type]
            )

        self.assertEqual(findings, [])

    def test_selected_invalid_v11_source_record_check_never_runs_legacy_audit(
        self,
    ) -> None:
        folder = Path("/tmp/OpaquePaper_selected_source_record")
        run_context = SimpleNamespace(
            selected_v11_closeout=True,
            current_v11_closeout=False,
            v11_direct_semantic_review_error="library review is stale",
        )
        with mock.patch.object(
            audit_repository,
            "run_source_record_audit_helper",
            side_effect=AssertionError("selected v11 ran the raw source-record audit"),
        ):
            findings = audit_repository.check_source_record_audit(
                folder.name,
                folder,
                {},
                "formalized",
                True,
                paper_closeout=True,
                run_context=run_context,  # type: ignore[arg-type]
            )

        self.assertEqual(len(findings), 1)
        self.assertIn("selected v11 semantic lane is not current", findings[0].message)
        self.assertIn("library review is stale", findings[0].message)

    def test_selected_v11_never_calls_legacy_explicit_model_gate(self) -> None:
        folder = Path("/tmp/OpaquePaper_selected_explicit_model")
        run_context = SimpleNamespace(selected_v11_closeout=True)
        with mock.patch.object(
            audit_evidence_integrity,
            "explicit_source_route_semantic_model_findings",
            side_effect=AssertionError(
                "selected v11 called the legacy explicit-model gate"
            ),
        ):
            findings = (
                audit_repository.check_explicit_source_route_semantic_model_evidence(
                    folder,
                    "formalized",
                    {},
                    run_context=run_context,  # type: ignore[arg-type]
                )
            )

        self.assertEqual(findings, [])

    def test_manifest_reuse_rows_require_exact_current_evidence_context(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OpaquePaper_623"
            folder.mkdir()
            row = {
                "qualified_declaration": "OpaquePaper_623.reviewed",
                "elaborated_signature_sha256": "a" * 64,
            }
            payload = {
                "paper": folder.name,
                "configured_review_rows": [row],
                "configured_review_rows_count": 1,
                "missing_configured_review_rows": [],
            }
            current_evidence = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                legacy_source_record_state=legacy_source_record_state(payload),
            )
            stale_evidence = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                legacy_source_record_state=legacy_source_record_state(
                    payload,
                    source_record_identity_error="stale source fingerprint",
                ),
            )
            with (
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=mock.Mock(),
                ),
            ):
                current = audit_repository.PaperCloseoutRunContext(
                    folder.name, folder, evidence_context=current_evidence
                )
                stale = audit_repository.PaperCloseoutRunContext(
                    folder.name, folder, evidence_context=stale_evidence
                )

        self.assertEqual(
            current.current_configured_review_rows_for_manifest_reuse(),
            (row,),
        )
        self.assertIsNone(
            stale.current_configured_review_rows_for_manifest_reuse()
        )

    def test_declaration_index_uses_only_authenticated_loaded_sources(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper_id = "OpaquePaper_624"
            folder = papers / paper_id
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            imported = folder / "Imported.lean"
            scratch = folder / "UnimportedScratch.lean"
            interface.write_text(f"import {paper_id}.Imported\n", encoding="utf-8")
            imported.write_text(
                "namespace OpaquePaper_624\n"
                "theorem semantic_coordinate : True := by trivial\n"
                "end OpaquePaper_624\n",
                encoding="utf-8",
            )
            # This same-short-name declaration is deliberately absent from the
            # Lean-owned closure and must not make the canonical route ambiguous.
            scratch.write_text(
                "namespace Scratch\n"
                "theorem semantic_coordinate : False := by contradiction\n"
                "end Scratch\n",
                encoding="utf-8",
            )

            interface_content = interface.read_bytes()
            imported_content = imported.read_bytes()
            entry_module = f"{paper_id}.PaperInterface"
            audit_payload = {
                "lean_import_closure": {
                    "entrypoint": interface.relative_to(root).as_posix(),
                    "entry_module": entry_module,
                }
            }
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                legacy_source_record_state=legacy_source_record_state(audit_payload),
            )
            build_input_provider = mock.Mock()
            build_input_provider.repository_source_snapshot.return_value = (
                (
                    entry_module,
                    interface.resolve(),
                    interface_content,
                    "a" * 64,
                ),
                (
                    f"{paper_id}.Imported",
                    imported.resolve(),
                    imported_content,
                    "b" * 64,
                ),
            )
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=build_input_provider,
                ) as provider_factory,
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    paper_id,
                    folder,
                    evidence_context=evidence_context,
                )
                first = context.paper_declaration_index()
                second = context.paper_declaration_index()

            provider_factory.assert_called_once_with(
                root,
                lean_import_closure_payload=audit_payload["lean_import_closure"],
            )
            build_input_provider.repository_source_snapshot.assert_called_once_with(
                entry_module
            )
            resolved = audit_repository.resolve_declaration_name(
                first, "semantic_coordinate"
            )
            self.assertIs(first, second)
            self.assertEqual(len(resolved), 1)
            self.assertEqual(resolved[0].path, imported)
            self.assertNotIn("Scratch.semantic_coordinate", first)

    def test_exact_lean_parsers_ignore_an_aba_live_replacement(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper_id = "OpaquePaper_625"
            folder = papers / paper_id
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            assumptions = folder / "Assumptions.lean"
            interface_text = (
                f"import {paper_id}.Assumptions\n"
                "theorem reviewed_result : True := by trivial\n"
            )
            assumption_text = (
                "-- audit-premise: h : SourceCondition theta\n"
                "axiom source_condition : SourceCondition theta\n"
            )
            interface.write_text(interface_text, encoding="utf-8")
            assumptions.write_text(assumption_text, encoding="utf-8")
            entry_module = f"{paper_id}.PaperInterface"
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                legacy_source_record_state=legacy_source_record_state(
                    {
                        "lean_import_closure": {
                            "entrypoint": interface.relative_to(root).as_posix(),
                            "entry_module": entry_module,
                        }
                    }
                ),
            )
            provider = mock.Mock()
            provider.repository_source_snapshot.return_value = (
                (
                    entry_module,
                    interface.resolve(),
                    interface_text.encode("utf-8"),
                    "a" * 64,
                ),
                (
                    f"{paper_id}.Assumptions",
                    assumptions.resolve(),
                    assumption_text.encode("utf-8"),
                    "b" * 64,
                ),
            )
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    paper_id,
                    folder,
                    evidence_context=evidence_context,
                )
                # Simulate a replacement that is restored before the final
                # transaction hash. Primary parsers must still see snapshot A.
                interface.write_text(
                    "theorem replacement_result : False := by contradiction\n",
                    encoding="utf-8",
                )
                assumptions.write_text(
                    "axiom replacement_condition : False\n", encoding="utf-8"
                )
                exact_interface = context.exact_lean_source_text(interface)
                exact_assumptions = context.exact_lean_source_text(assumptions)

            self.assertEqual(exact_interface, interface_text)
            self.assertEqual(exact_assumptions, assumption_text)
            self.assertEqual(
                review_surface_structure.review_rows_from_interface_text(
                    exact_interface or ""
                ),
                [(2, "reviewed_result")],
            )
            self.assertIn(
                "source_condition",
                review_surface_structure.assumption_declarations_from_text(
                    exact_assumptions or "", {"source_condition"}
                ),
            )
            self.assertEqual(
                audit_repository.assumption_premises_from_text(
                    exact_assumptions or "", {"source_condition"}
                ),
                {"source_condition": {"h : SourceCondition theta"}},
            )
            provider.repository_source_snapshot.assert_called_once_with(entry_module)

    def test_declaration_findings_use_exact_fidelity_path_and_payload(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper_id = "OpaquePaper_626"
            folder = papers / paper_id
            audit_dir = folder / "audit"
            audit_dir.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface_text = "-- exact paper-facing surface\n"
            interface.write_text(interface_text, encoding="utf-8")
            status_path = folder / "status.json"
            map_path = audit_dir / "paper_statement_map.json"
            fidelity_path = audit_dir / "configured_fidelity.json"
            status_payload = {
                "id": paper_id,
                "status": "partially formalized",
                "review_surface": {
                    "source_file": interface.relative_to(root).as_posix(),
                    "include_names": [],
                    "assumption_names": [],
                    "source_proof_fidelity_review": {
                        "ledger_file": "audit/configured_fidelity.json"
                    },
                },
            }
            map_payload = {"items": {}}
            fidelity_payload = {"defects": [{"id": "snapshot-defect"}]}
            for path, payload in (
                (status_path, status_payload),
                (map_path, map_payload),
                (fidelity_path, fidelity_payload),
            ):
                path.write_text(json.dumps(payload), encoding="utf-8")
            snapshots = (
                SimpleNamespace(path=status_path, payload=status_payload),
                SimpleNamespace(path=map_path, payload=map_payload),
                SimpleNamespace(path=fidelity_path, payload=fidelity_payload),
            )
            entry_module = f"{paper_id}.PaperInterface"
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                legacy_source_record_state=legacy_source_record_state(
                    {
                        "lean_import_closure": {
                            "entrypoint": interface.relative_to(root).as_posix(),
                            "entry_module": entry_module,
                        }
                    }
                ),
                input_snapshots=snapshots,
                source_proof_fidelity_snapshot=snapshots[-1],
            )
            provider = mock.Mock()
            provider.repository_source_snapshot.return_value = (
                (
                    entry_module,
                    interface.resolve(),
                    interface_text.encode("utf-8"),
                    "a" * 64,
                ),
            )
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    paper_id,
                    folder,
                    evidence_context=evidence_context,
                )
                fidelity_path.write_text(
                    json.dumps({"defects": [{"id": "replacement-defect"}]}),
                    encoding="utf-8",
                )
                with (
                    mock.patch.object(context, "paper_declaration_index", return_value={}),
                    mock.patch.object(context, "library_declaration_index", return_value={}),
                    mock.patch.object(
                        context,
                        "exact_source_proof_fidelity_input",
                        wraps=context.exact_source_proof_fidelity_input,
                    ) as exact_fidelity,
                    mock.patch.object(
                        audit_repository,
                        "configured_source_proof_fidelity_path",
                        side_effect=AssertionError("must not resolve a live ledger"),
                    ),
                    mock.patch.object(
                        audit_repository,
                        "source_index_byte_pinned_anchor_item_ids",
                        return_value=set(),
                    ),
                    mock.patch.object(
                        audit_repository,
                        "paper_statement_map_semantic_surface_findings",
                        return_value=[],
                    ),
                    mock.patch.object(
                        audit_repository,
                        "paper_statement_map_semantic_contract_findings",
                        return_value=[],
                    ),
                    mock.patch.object(
                        Path,
                        "read_text",
                        side_effect=AssertionError("must not reread primary inputs"),
                    ),
                ):
                    audit_repository.paper_statement_map_declaration_findings(
                        paper_id,
                        folder,
                        "partially formalized",
                        run_context=context,
                    )

            exact_fidelity.assert_called_once_with()
            self.assertEqual(
                context.exact_source_proof_fidelity_input(),
                (fidelity_path, fidelity_payload),
            )

    def test_dashboard_bundle_combines_exact_json_and_lean_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper_id = "OpaquePaper_627"
            folder = papers / paper_id
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            status_path = folder / "status.json"
            interface_text = "theorem exact_row : True := by trivial\n"
            status_bytes = json.dumps(
                {"id": paper_id, "status": "partially formalized"}
            ).encode("utf-8")
            interface.write_text(interface_text, encoding="utf-8")
            status_path.write_bytes(status_bytes)
            entry_module = f"{paper_id}.PaperInterface"
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                legacy_source_record_state=legacy_source_record_state(
                    {
                        "lean_import_closure": {
                            "entrypoint": interface.relative_to(root).as_posix(),
                            "entry_module": entry_module,
                        }
                    }
                ),
                input_snapshots=(
                    SimpleNamespace(
                        path=status_path,
                        raw_bytes=status_bytes,
                        sha256="a" * 64,
                    ),
                    SimpleNamespace(
                        path=interface,
                        raw_bytes=interface_text.encode("utf-8"),
                        sha256="b" * 64,
                    ),
                    SimpleNamespace(
                        path=folder / "audit" / "statement_match_llm.json",
                        raw_bytes=None,
                        sha256=None,
                    ),
                ),
            )
            provider = mock.Mock()
            provider.repository_source_snapshot.return_value = (
                (
                    entry_module,
                    interface.resolve(),
                    interface_text.encode("utf-8"),
                    "b" * 64,
                ),
            )
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    paper_id,
                    folder,
                    evidence_context=evidence_context,
                )
                status_path.write_text(
                    json.dumps({"id": paper_id, "status": "replacement"}),
                    encoding="utf-8",
                )
                interface.write_text(
                    "theorem replacement_row : False := by contradiction\n",
                    encoding="utf-8",
                )
                first = context.dashboard_audit_inputs()
                second = context.dashboard_audit_inputs()

            self.assertIs(first, second)
            self.assertIsNotNone(first)
            assert first is not None
            self.assertEqual(first.read_bytes(status_path), status_bytes)  # type: ignore[attr-defined]
            self.assertEqual(first.read_text(interface), interface_text)  # type: ignore[attr-defined]
            self.assertFalse(  # type: ignore[attr-defined]
                first.is_file(folder / "audit" / "statement_match_llm.json")
            )
            with mock.patch.object(
                audit_repository.PaperCloseoutRunContext,
                "selected_v11_closeout",
                new_callable=mock.PropertyMock,
                return_value=True,
            ):
                self.assertIsNone(context.dashboard_audit_inputs())

    def test_statement_and_assumption_judgments_use_exact_json_snapshots(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper_id = "OpaquePaper_628"
            folder = papers / paper_id
            audit_dir = folder / "audit"
            audit_dir.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface_text = "theorem exact_row : True := by trivial\n"
            interface.write_text(interface_text, encoding="utf-8")
            statement_path = audit_dir / "statement_match_llm.json"
            assumption_path = audit_dir / "assumption_match_llm.json"
            statement_payload = {
                "schema": 1,
                "paper": paper_id,
                "items": {"exact_row": {"judgment": "mismatch"}},
            }
            assumption_payload = {
                "schema": 1,
                "paper": paper_id,
                "items": {
                    "source_condition": {"judgment": "paper_condition"}
                },
            }
            statement_bytes = json.dumps(statement_payload).encode("utf-8")
            assumption_bytes = json.dumps(assumption_payload).encode("utf-8")
            statement_path.write_bytes(statement_bytes)
            assumption_path.write_bytes(assumption_bytes)
            snapshots = (
                SimpleNamespace(
                    path=statement_path,
                    payload=statement_payload,
                    raw_bytes=statement_bytes,
                    sha256="a" * 64,
                ),
                SimpleNamespace(
                    path=assumption_path,
                    payload=assumption_payload,
                    raw_bytes=assumption_bytes,
                    sha256="b" * 64,
                ),
            )
            entry_module = f"{paper_id}.PaperInterface"
            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                legacy_source_record_state=legacy_source_record_state(
                    {
                        "lean_import_closure": {
                            "entrypoint": interface.relative_to(root).as_posix(),
                            "entry_module": entry_module,
                        }
                    }
                ),
                input_snapshots=snapshots,
            )
            provider = mock.Mock()
            provider.repository_source_snapshot.return_value = (
                (
                    entry_module,
                    interface.resolve(),
                    interface_text.encode("utf-8"),
                    "c" * 64,
                ),
            )
            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    audit_repository,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    paper_id,
                    folder,
                    evidence_context=evidence_context,
                )
                bundle = context.dashboard_audit_inputs()
                statement_path.write_text(
                    json.dumps({"schema": 1, "items": {}}), encoding="utf-8"
                )
                assumption_path.write_text(
                    json.dumps({"schema": 1, "items": {}}), encoding="utf-8"
                )

                dashboard = types.ModuleType("review_dashboard")

                def load_statement_judgments(
                    _folder: Path,
                    _manifests: object,
                    *,
                    audit_inputs: object,
                ) -> dict[str, dict[str, object]]:
                    self.assertIs(audit_inputs, bundle)
                    self.assertEqual(  # type: ignore[attr-defined]
                        audit_inputs.json_payload(statement_path), statement_payload
                    )
                    return {"exact_row": {"conditional": True}}

                dashboard.load_llm_statement_judgments = load_statement_judgments  # type: ignore[attr-defined]
                dashboard._is_conditional_boundary_judgment = (  # type: ignore[attr-defined]
                    lambda judgment: judgment.get("conditional") is True
                )
                rows = (SimpleNamespace(name="exact_row", lean_signature_manifest={}),)
                with mock.patch.dict(
                    sys.modules, {"scripts.review_dashboard": dashboard}
                ):
                    conditional_rows = (
                        audit_repository.current_statement_conditional_boundary_rows(
                            folder,
                            review_items_provider=lambda: rows,
                            run_context=context,
                        )
                    )
                exact_assumption_payload = context.exact_json_payload(assumption_path)

            self.assertEqual(conditional_rows, {"exact_row"})
            self.assertIs(exact_assumption_payload, assumption_payload)
            self.assertEqual(
                audit_repository.assumption_judgments_from_payload(
                    exact_assumption_payload, paper_id
                )["source_condition"]["judgment"],
                "paper_condition",
            )

    def test_exact_json_payload_never_rereads_a_live_replacement(self) -> None:
        folder = Path("papers/OpaquePaper_842")
        path = folder / "status.json"
        exact = {"status": "formalized", "opaque": "snapshot-a"}
        evidence_context = SimpleNamespace(
            folder=folder.resolve(),
            issued_by_builder=True,
            input_snapshots=(SimpleNamespace(path=path, payload=exact),),
        )
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            context = audit_repository.PaperCloseoutRunContext(
                folder.name,
                folder,
                evidence_context=evidence_context,
            )

        with mock.patch.object(
            audit_repository,
            "load_json_object",
            side_effect=AssertionError("exact input must not be reread"),
        ):
            self.assertIs(context.exact_json_payload(path), exact)

    def test_blank_lane_uses_configured_snapshot_not_canonical_live_file(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "OpaquePaper_519"
            configured_dir = folder / "audit" / "configured"
            configured_dir.mkdir(parents=True)
            fields = {
                "review_surface_audit_file": "surface.json",
                "lean_to_tex_file": "drafts.json",
                "match_judgment_file": "statements.json",
                "paper_coverage_audit_file": "coverage.json",
            }
            status = {
                "status": "formalized",
                "review_surface": {
                    "llm_statement_review": {
                        field: str(
                            Path("papers")
                            / folder.name
                            / "audit"
                            / "configured"
                            / basename
                        )
                        for field, basename in fields.items()
                    }
                },
            }
            from scripts import review_dashboard

            blank = {
                "non_evidence_scaffold": {
                    "schema": review_dashboard.NON_EVIDENCE_SCAFFOLD_SCHEMA,
                    "status": review_dashboard.NON_EVIDENCE_SCAFFOLD_STATUS,
                }
            }
            snapshots = [
                SimpleNamespace(path=folder / "status.json", payload=status, sha256="a")
            ]
            for basename in fields.values():
                snapshots.append(
                    SimpleNamespace(
                        path=configured_dir / basename,
                        payload=blank,
                        sha256="b",
                    )
                )

            by_path = {snapshot.path.resolve(): snapshot for snapshot in snapshots}

            def json_snapshot(path: Path) -> object | None:
                return by_path.get(path.resolve())

            evidence_context = SimpleNamespace(
                folder=folder.resolve(),
                issued_by_builder=True,
                input_snapshots=tuple(snapshots),
                json_snapshot=json_snapshot,
                canonical_sidecar_path=lambda basename: folder / "audit" / basename,
            )
            with mock.patch.object(
                audit_repository, "exact_evidence_run_context", return_value=True
            ):
                context = audit_repository.PaperCloseoutRunContext(
                    folder.name,
                    folder,
                    evidence_context=evidence_context,
                )

            with (
                mock.patch.object(audit_repository, "ROOT", root),
                mock.patch.object(
                    audit_repository,
                    "load_json_object",
                    side_effect=AssertionError("blank lane must use frozen bytes"),
                ),
            ):
                lanes = audit_repository.semantic_contract_closeout_blank_sidecar_lanes(
                    folder,
                    run_context=context,
                )

        self.assertEqual(
            lanes,
            {"review_surface": True, "statement": True, "coverage": True},
        )

    def test_exact_snapshot_reuses_payload_judgments_and_corrected_scope(self) -> None:
        paper_id = "OpaquePaper_948"
        folder = Path("papers") / paper_id
        audit_path = folder / "audit" / "source_record_audit.json"
        judgment_path = folder / "audit" / "source_record_match_llm.json"
        payload = {
            "source_record_audit_sha256": "a" * 64,
            "source_record_audit_integrity_sha256": "b" * 64,
        }
        judgments = {"opaque-key": {"classification": "reviewed"}}
        status = {"id": paper_id, "status": "formalized"}
        evidence_context = SimpleNamespace(
            folder=folder.resolve(),
            issued_by_builder=True,
            status_payload=status,
            corrected_scope_current=True,
            legacy_source_record_state=legacy_source_record_state(
                payload,
                audit_path=audit_path,
                match_path=judgment_path,
                current_source_record_judgments=judgments,
                corrected_scope_current=True,
            ),
        )
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            context = audit_repository.PaperCloseoutRunContext(
                paper_id,
                folder,
                evidence_context=evidence_context,
            )

        with (
            mock.patch.object(
                audit_repository,
                "load_json_object",
                return_value=payload,
            ) as load_json,
            mock.patch.object(
                audit_repository,
                "current_saved_source_record_audit",
                return_value=payload,
            ) as validate_payload,
            mock.patch.object(
                audit_repository,
                "source_record_judgment_items",
                return_value=judgments,
            ) as parse_judgments,
            mock.patch.object(
                audit_repository,
                "evaluate_author_approved_corrected_scope",
                return_value=True,
            ) as corrected_scope,
        ):
            first_payload = context.current_source_record_audit()
            second_payload = context.current_source_record_audit()
            first_saved = context.saved_source_record_audit(audit_path)
            second_saved = context.saved_source_record_audit(audit_path)
            first_judgments = context.source_record_judgments(
                judgment_path, payload
            )
            second_judgments = context.source_record_judgments(
                judgment_path, payload
            )
            wrong_saved = context.saved_source_record_audit(
                folder / "audit" / "replacement-audit.json"
            )
            wrong_judgments = context.source_record_judgments(
                folder / "audit" / "replacement-judgments.json",
                payload,
            )
            first_scope = context.corrected_scope_current(status)
            second_scope = context.corrected_scope_current(dict(status))

        self.assertEqual(first_payload, (payload, ""))
        self.assertEqual(second_payload, first_payload)
        self.assertIs(first_saved, payload)
        self.assertIs(second_saved, first_saved)
        self.assertIs(first_judgments, judgments)
        self.assertIs(second_judgments, first_judgments)
        self.assertIsNone(wrong_saved)
        self.assertEqual(wrong_judgments, {})
        self.assertTrue(first_scope)
        self.assertTrue(second_scope)
        # The exact evidence transaction already performed all four operations;
        # no primary-closeout consumer may repeat them.
        load_json.assert_not_called()
        validate_payload.assert_not_called()
        parse_judgments.assert_not_called()
        corrected_scope.assert_not_called()

    def test_mismatched_corrected_scope_status_fails_without_live_evaluation(
        self,
    ) -> None:
        paper_id = "OpaquePaper_557"
        folder = Path("papers") / paper_id
        status = {"id": paper_id, "status": "formalized"}
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            context = audit_repository.PaperCloseoutRunContext(
                paper_id,
                folder,
                evidence_context=SimpleNamespace(
                    folder=folder.resolve(),
                    issued_by_builder=True,
                    status_payload={"id": paper_id, "status": "partially formalized"},
                ),
            )

        with mock.patch.object(
            audit_repository,
            "evaluate_author_approved_corrected_scope",
            side_effect=AssertionError("exact closeout must not evaluate live status"),
        ) as evaluate:
            first = context.corrected_scope_evaluation(status)
            second = context.corrected_scope_evaluation(dict(status))
            self.assertFalse(context.corrected_scope_current(status))
            with self.assertRaisesRegex(ValueError, "does not match"):
                context.corrected_scope_current(status, raise_on_error=True)

        self.assertFalse(first[0])
        self.assertIsInstance(first[1], ValueError)
        self.assertFalse(second[0])
        self.assertIsInstance(second[1], ValueError)
        evaluate.assert_not_called()

    def test_complete_model_binding_derivation_is_cached_once_per_surface(self) -> None:
        paper_id = "OpaquePaper_271"
        folder = Path("papers") / paper_id
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            context = audit_repository.PaperCloseoutRunContext(
                paper_id,
                folder,
                evidence_context=SimpleNamespace(
                    folder=folder.resolve(), issued_by_builder=True
                ),
            )
        review_surface = {"source_record_audit_file": "audit/opaque.json"}
        expected = {
            "Opaque.row": ((frozenset({"model"}), "Opaque.Model", frozenset()),)
        }

        with mock.patch.object(
            audit_repository,
            "_source_record_complete_model_record_bindings_uncached",
            return_value=expected,
        ) as derive:
            first = audit_repository.source_record_complete_model_record_bindings(
                paper_id,
                folder,
                review_surface,
                "formalized",
                run_context=context,
            )
            second = audit_repository.source_record_complete_model_record_bindings(
                paper_id,
                folder,
                dict(review_surface),
                "formalized",
                run_context=context,
            )

        self.assertIs(first, expected)
        self.assertIs(second, first)
        derive.assert_called_once_with(
            paper_id,
            folder,
            review_surface,
            "formalized",
            run_context=context,
        )

    def test_duck_typed_evidence_context_cannot_authorize_reuse(self) -> None:
        folder = Path("papers/OpaquePaper_119")
        with self.assertRaisesRegex(ValueError, "does not match"):
            audit_repository.PaperCloseoutRunContext(
                folder.name,
                folder,
                evidence_context=SimpleNamespace(
                    folder=folder.resolve(),
                    issued_by_builder=True,
                ),
            )

    def test_normal_repository_run_calls_paper_ledger_once(self) -> None:
        other_checks = (
            "check_sorries",
            "check_axiom_like_declarations",
            "check_hidden_variable_premises",
            "check_guarded_checks",
            "check_library_source_assumption_standards",
            "check_library_reusable_provenance_language",
            "check_library_standard_definition_audits",
            "check_library_source_hygiene",
            "check_generic_source_reference_hygiene",
            "check_paper_contract",
            "check_graph_native_paper_closure",
            "check_final_report_status_alignment",
            "check_final_report_human_facing_front_matter",
            "check_dag_and_validation_report_closeout",
            "check_review_launcher_readiness",
            "check_dag_status_styles",
            "check_post_paper_audit_interfaces",
            "check_machine_paper_status",
            "check_status_label_vocabulary",
            "check_generated_human_status_labels",
            "check_readme_status_tables",
            "check_tracked_artifacts",
            "check_stale_architecture_terms",
            "check_root_readme_policy",
            "check_human_facing_readme",
        )
        with ExitStack() as stack:
            for name in other_checks:
                stack.enter_context(
                    mock.patch.object(audit_repository, name, return_value=[])
                )
            ledger = stack.enter_context(
                mock.patch.object(
                    audit_repository,
                    "check_paper_facing_ledgers",
                    return_value=[],
                )
            )
            findings = audit_repository.run(
                include_active=False,
                strict_style=False,
            )

        self.assertEqual(findings, [])
        ledger.assert_called_once_with(False)

    def test_check_machine_threads_one_provider_through_all_consumers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            paper_id = "OpaquePaper_731"
            paper = papers / paper_id
            paper.mkdir(parents=True)
            interface_text = (
                "namespace OpaqueNamespace\n"
                "theorem semantic_coordinate_99 : True := by trivial\n"
                "end OpaqueNamespace\n"
            )
            (paper / "PaperInterface.lean").write_text(interface_text, encoding="utf-8")
            status = {
                "id": paper_id,
                "title": "Opaque title",
                "source_version": "pinned source",
                "build_target": f"lake build {paper_id}",
                "status": "partially formalized",
                "review_entrypoint": f"papers/{paper_id}/FINAL_VALIDATION_REPORT.md",
                "human_review": {
                    "reviewed_rows": 1,
                    "total_rows": 1,
                    "stale_rows": 0,
                    "mismatch_rows": 0,
                },
                "paper_interface": {
                    "path": f"papers/{paper_id}/PaperInterface.lean",
                    "line_count": len(interface_text.splitlines()),
                    "declaration_rows": 1,
                    "review_rows": 1,
                },
                "review_surface": {
                    "source_file": f"papers/{paper_id}/PaperInterface.lean",
                    "include_names": ["semantic_coordinate_99"],
                    "assumption_names": [],
                    "auxiliary_names": [],
                    "proof_boundary_names": [],
                    "source_definition_names": [],
                    "proposition_spec_proofs": {},
                },
            }
            (paper / "status.json").write_text(json.dumps(status), encoding="utf-8")

            extracted_rows = (object(),)
            providers: list[object] = []
            observed_rows: list[tuple[object, ...]] = []
            observed_corrected_scope: list[object] = []
            source_run_contexts: list[object] = []

            def consume_provider(provider: object) -> None:
                self.assertTrue(callable(provider))
                providers.append(provider)
                observed_rows.append(provider())  # type: ignore[operator]

            def sidecar_consumer(
                *_args: object,
                review_items_provider: object = None,
                corrected_scope_evaluation: object = None,
                **_kwargs: object,
            ) -> list[audit_repository.Finding]:
                consume_provider(review_items_provider)
                observed_corrected_scope.append(corrected_scope_evaluation)
                return []

            def source_audit_consumer(
                *_args: object,
                run_context: object = None,
                **_kwargs: object,
            ) -> list[audit_repository.Finding]:
                source_run_contexts.append(run_context)
                return []

            def premise_consumer(
                *_args: object,
                run_context: object = None,
                **_kwargs: object,
            ) -> set[str]:
                source_run_contexts.append(run_context)
                return set()

            def binding_consumer(
                *_args: object,
                run_context: object = None,
                **_kwargs: object,
            ) -> dict[str, object]:
                source_run_contexts.append(run_context)
                return {}

            def conditional_consumer(
                *_args: object,
                review_items_provider: object = None,
                **_kwargs: object,
            ) -> set[str]:
                consume_provider(review_items_provider)
                return set()

            def proposition_consumer(
                *_args: object,
                review_items_provider: object = None,
                **_kwargs: object,
            ) -> list[audit_repository.Finding]:
                consume_provider(review_items_provider)
                return []

            with ExitStack() as stack:
                stack.enter_context(mock.patch.object(audit_repository, "ROOT", root))
                stack.enter_context(
                    mock.patch.object(audit_repository, "PAPERS", papers)
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "PAPER_STATUS_FILE",
                        papers / "missing-aggregate-status.json",
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository, "paper_dirs", return_value=[paper]
                    )
                )
                extract = stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "strict_review_items_for_paper",
                        return_value=extracted_rows,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "paper_statement_sidecar_findings",
                        side_effect=sidecar_consumer,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "current_statement_conditional_boundary_rows",
                        side_effect=conditional_consumer,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "check_proposition_spec_routes",
                        side_effect=proposition_consumer,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "paper_lean_declaration_index",
                        return_value={},
                    )
                )
                corrected_scope = stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "evaluate_author_approved_corrected_scope",
                        return_value=False,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "current_corrected_model_premise_bridge",
                        return_value=None,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "check_paper_interface_axiom_closure",
                        return_value=[],
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "check_source_proof_fidelity",
                        return_value=[],
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "check_explicit_source_route_semantic_model_evidence",
                        return_value=[],
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "check_source_record_audit",
                        side_effect=source_audit_consumer,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "source_record_validated_boundary_premises",
                        side_effect=premise_consumer,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "source_record_complete_model_record_bindings",
                        side_effect=binding_consumer,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "current_named_theory_semantic_review_surface",
                        return_value=(None, ""),
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        audit_repository,
                        "load_expanded_review_statements",
                        return_value={},
                    )
                )
                audit_repository.check_machine_paper_status(
                    paper_filter=paper_id,
                    paper_closeout=True,
                )

            extract.assert_called_once_with(
                paper, build_input_provider=mock.ANY, audit_inputs=None
            )
            self.assertEqual(len(providers), 3)
            self.assertIs(providers[0], providers[1])
            self.assertIs(providers[1], providers[2])
            self.assertIs(observed_rows[0], extracted_rows)
            self.assertIs(observed_rows[1], extracted_rows)
            self.assertIs(observed_rows[2], extracted_rows)
            self.assertEqual(observed_corrected_scope, [(False, None)])
            corrected_scope.assert_called_once_with(paper, status)
            self.assertEqual(len(source_run_contexts), 3)
            self.assertIsInstance(
                source_run_contexts[0],
                audit_repository.PaperCloseoutRunContext,
            )
            self.assertIs(source_run_contexts[0], source_run_contexts[1])
            self.assertIs(source_run_contexts[1], source_run_contexts[2])
            self.assertIs(
                extract.call_args.kwargs["build_input_provider"],
                source_run_contexts[0].build_input_provider,
            )

    def _run_consumers(
        self,
        spec_name: str,
        proof_name: str,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            interface = folder / "PaperInterface.lean"
            interface.write_text("-- mocked review surface\n", encoding="utf-8")
            # The v11 surface keeps semantic Specs in PaperInterface and their
            # proof endpoints in a distinct module.  This fixture exercises
            # arbitrary declaration names, not the missing-module gate.
            (folder / "ProofInterface.lean").write_text(
                "-- mocked proof endpoints\n", encoding="utf-8"
            )

            rows = (
                SimpleNamespace(
                    name=spec_name,
                    kind="def",
                    lean_signature_manifest={"semantic_role": "specification"},
                ),
                SimpleNamespace(
                    name=proof_name,
                    kind="theorem",
                    lean_signature_manifest={"semantic_role": "proof"},
                ),
            )
            review_surface: dict[str, object] = {
                "include_names": [spec_name, proof_name],
                "assumption_names": [],
                "source_definition_names": [],
                "proposition_spec_proofs": {spec_name: proof_name},
            }

            dashboard = types.ModuleType("review_dashboard")
            dashboard_rows = mock.Mock(return_value=list(rows))
            dashboard.review_items_for_paper = dashboard_rows  # type: ignore[attr-defined]
            dashboard.review_surface_audit_summary = mock.Mock(  # type: ignore[attr-defined]
                return_value={"has_completed_audit": True, "needs_attention": False}
            )
            dashboard.statement_translation_audit_summary = mock.Mock(  # type: ignore[attr-defined]
                return_value={"needs_attention": False}
            )
            dashboard.paper_coverage_audit_summary = mock.Mock(  # type: ignore[attr-defined]
                return_value={"needs_attention": False}
            )
            dashboard.assumption_provenance_audit_summary = mock.Mock(  # type: ignore[attr-defined]
                return_value={"needs_attention": False}
            )
            dashboard.load_llm_statement_judgments = mock.Mock(  # type: ignore[attr-defined]
                return_value={spec_name: {"semantic_class": "conditional"}}
            )
            dashboard._is_conditional_boundary_judgment = (  # type: ignore[attr-defined]
                lambda judgment: judgment.get("semantic_class") == "conditional"
            )
            dashboard.is_proposition_specification_manifest = (  # type: ignore[attr-defined]
                lambda manifest: manifest.get("semantic_role") == "specification"
            )
            dashboard.parse_review_source_declarations = mock.Mock(  # type: ignore[attr-defined]
                return_value=[
                    ("def", spec_name, f"OpaqueNamespace.{spec_name}"),
                    ("theorem", proof_name, f"OpaqueNamespace.{proof_name}"),
                ]
            )
            dashboard.review_source_file = mock.Mock(return_value=interface)  # type: ignore[attr-defined]
            dashboard.review_source_module = mock.Mock(  # type: ignore[attr-defined]
                return_value="OpaqueNamespace.PaperInterface"
            )
            dashboard.review_proof_module = mock.Mock(  # type: ignore[attr-defined]
                return_value="OpaqueNamespace.ProofInterface"
            )

            evidence = types.ModuleType("audit_evidence_integrity")
            evidence.author_approved_corrected_scope_contract_is_current = (  # type: ignore[attr-defined]
                lambda _folder, _status: False
            )
            lean_manifest = types.ModuleType("lean_signature_manifest")
            lean_manifest.run_lean_proposition_spec_proof_matches = (  # type: ignore[attr-defined]
                lambda _root, _module, routes, **_kwargs: {
                    tuple(route): True for route in routes
                }
            )

            def run_all(
                provider: audit_repository.LazyStrictReviewItems | None,
            ) -> tuple[
                list[audit_repository.Finding],
                set[str],
                list[audit_repository.Finding],
            ]:
                provider_arg = provider if provider is not None else None
                sidecar = audit_repository.paper_statement_sidecar_findings(
                    "OpaquePaper",
                    folder,
                    "partially formalized",
                    review_items_provider=provider_arg,
                )
                conditional = (
                    audit_repository.current_statement_conditional_boundary_rows(
                        folder,
                        review_items_provider=provider_arg,
                    )
                )
                proposition = audit_repository.check_proposition_spec_routes(
                    "OpaquePaper",
                    folder,
                    review_surface,
                    [spec_name, proof_name],
                    set(),
                    "partially formalized",
                    paper_closeout=False,
                    review_items_provider=provider_arg,
                )
                return sidecar, conditional, proposition

            with (
                mock.patch.dict(
                    sys.modules,
                    {
                        "scripts.audit_evidence_integrity": evidence,
                        "scripts.lean_signature_manifest": lean_manifest,
                        "scripts.review_dashboard": dashboard,
                    },
                ),
                mock.patch.object(
                    audit_repository,
                    "paper_statement_map_declaration_findings",
                    return_value=[],
                ),
                mock.patch.object(
                    audit_repository,
                    "load_json_object",
                    return_value={},
                ),
                mock.patch.object(
                    audit_repository,
                    "semantic_contract_closeout_bridge_is_current",
                    return_value=False,
                ),
            ):
                baseline = run_all(None)
                # Two diagnostic consumers extract rows without a shared
                # provider; canonical closeout no longer uses this parser lane.
                self.assertEqual(dashboard_rows.call_count, 2)

                dashboard_rows.reset_mock()
                provider = audit_repository.LazyStrictReviewItems(folder)
                shared = run_all(provider)
                self.assertEqual(dashboard_rows.call_count, 1)
                dashboard_rows.assert_called_once_with(
                    folder,
                    use_cache=True,
                    render_images=False,
                    require_current_signatures=True,
                    persist_cache_rebind=False,
                    build_input_provider=None,
                    audit_inputs=None,
                )
                cached_rows = provider()

            self.assertEqual(finding_identity(shared[0]), finding_identity(baseline[0]))
            self.assertEqual(shared[1], baseline[1])
            self.assertEqual(finding_identity(shared[2]), finding_identity(baseline[2]))
            self.assertEqual(shared[1], {spec_name})
            self.assertEqual(shared[2], [])
            self.assertIsInstance(cached_rows, tuple)
            self.assertEqual([row.name for row in cached_rows], [spec_name, proof_name])

    def test_shared_rows_preserve_semantics_under_arbitrary_renaming(self) -> None:
        for spec_name, proof_name in (
            ("alpha_coordinate", "beta_certificate"),
            ("renamed_row_17", "renamed_row_42"),
        ):
            with self.subTest(spec_name=spec_name, proof_name=proof_name):
                self._run_consumers(spec_name, proof_name)


if __name__ == "__main__":
    unittest.main()
