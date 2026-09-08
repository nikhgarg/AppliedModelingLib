from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import terminal_lean_semantic_revalidation as terminal
from scripts.accepted_obligation_graph import AcceptedObligationGraphCredential
from scripts.lean_review_surface import (
    lean_owned_semantic_review_display_surface_from_inventory,
)
from scripts.obligation_evidence_graph import (
    legacy_artifact_bound_source_atom_leaf,
    source_atom_leaf,
)


class TerminalLeanSemanticRevalidationTests(unittest.TestCase):
    def test_public_projection_authority_requires_canonical_main_and_exact_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paper = root / "papers/Fixture"
            envelope = paper / terminal.PUBLIC_SOURCE_ROLE_PROJECTION_FILE
            envelope.parent.mkdir(parents=True)
            envelope.write_bytes(b"trusted envelope\n")

            def git(*args):
                subprocess.run(["git", "-C", directory, *args], check=True,
                               capture_output=True)

            git("init", "-b", "main")
            git("config", "user.name", "Fixture")
            git("config", "user.email", "fixture@example.invalid")
            git("add", "papers")
            git("commit", "-m", "Fixture envelope")
            git("remote", "add", "origin", "https://github.com/untrusted/AppliedModelingLib.git")
            git("update-ref", "refs/remotes/origin/main", "HEAD")
            with self.assertRaisesRegex(ValueError, "not authenticated"):
                terminal._trusted_public_source_role_envelope(paper)
            for url in ("https://github.com/nikhgarg/AppliedModelingLib.git",
                        "git@github.com:nikhgarg/EconCSLib.git"):
                git("remote", "set-url", "origin", url)
                self.assertEqual(terminal._trusted_public_source_role_envelope(paper),
                                 b"trusted envelope\n")
            envelope.write_bytes(b"branch-only replacement\n")
            git("add", "papers")
            git("commit", "-m", "Unreleased replacement")
            with self.assertRaisesRegex(ValueError, "not authenticated"):
                terminal._trusted_public_source_role_envelope(paper)
            git("update-ref", "-d", "refs/remotes/origin/main")
            with self.assertRaisesRegex(ValueError, "not authenticated"):
                terminal._trusted_public_source_role_envelope(paper)

    def test_projected_roles_require_authenticated_bridge_before_atom_comparison(self) -> None:
        original = source_atom_leaf(
            contract_sha256="1" * 64, source_artifact_sha256="2" * 64,
            source_quote_sha256="3" * 64, source_component_sha256="4" * 64,
            source_role_contract_sha256="5" * 64,
        )
        changed_role = source_atom_leaf(
            contract_sha256="1" * 64, source_artifact_sha256="2" * 64,
            source_quote_sha256="3" * 64, source_component_sha256="4" * 64,
            source_role_contract_sha256="6" * 64,
        )
        loaded = AcceptedObligationGraphCredential(
            accepted_graph=SimpleNamespace(graph_sha256="9" * 64),
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "claim": {"source_atom": (original.leaf_sha256,)}},
                prerequisite_leaf_sha256s_by_declaration={}),
            semantic_graph=SimpleNamespace(graph_sha256="8" * 64,
                                           leaves={original.leaf_sha256: original}),
            closure_leaf=None)
        for role_field in ("corrected_target", "user_approved_scope_exclusion"):
            source = {"items": {"claim": {role_field: {}}},
                      "publication_corrected_target_projection": {
                          "schema": 1, "approval_material_included": False}}
            with self.subTest(role_field=role_field), \
                 mock.patch.object(terminal, "project_source_route_leaf_material_from_validated_inputs",
                                   return_value=({changed_role.leaf_sha256: changed_role},
                                                 {"claim": (changed_role.leaf_sha256,)})), \
                 mock.patch.object(terminal, "_json_bytes",
                                   side_effect=lambda path, label: (source, b"map")
                                   if label == "public source map" else ({}, b"display")), \
                 mock.patch.object(terminal, "_trusted_public_source_role_envelope",
                                   return_value=b"trusted") as trusted, \
                 mock.patch.object(terminal, "validate_runtime_public_source_role_projection") as validate:
                call = lambda: terminal._validate_current_source_routes(
                    loaded, source, SimpleNamespace(),
                    paper_dir=Path("/repo/papers/Fixture"), allow_withheld_source_material=True)
                self.assertEqual(call(), {"claim": "claim"})
                self.assertEqual(validate.call_args.kwargs["accepted_role_sha256s_by_source_item"],
                                 {"claim": ("5" * 64,)})
                self.assertEqual(validate.call_args.kwargs["accepted_graph_sha256"], "9" * 64)
                validate.side_effect = ValueError("retained public role changed")
                with self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError,
                                            "retained public role changed"):
                    call()
                validate.side_effect = None
                trusted.side_effect = ValueError("unreleased envelope")
                with self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError,
                                            "unreleased envelope"):
                    call()

    def test_public_source_recovery_requires_exact_routes_and_atoms(self) -> None:
        def atom(quote):
            return source_atom_leaf(
                contract_sha256="1" * 64, source_artifact_sha256="2" * 64,
                source_quote_sha256=quote * 64, source_component_sha256="4" * 64,
                source_role_contract_sha256="5" * 64,
            )
        original, changed = atom("3"), atom("6")
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "claim": {"source_atom": (original.leaf_sha256,)}},
                prerequisite_leaf_sha256s_by_declaration={}),
            graph=SimpleNamespace(leaves={original.leaf_sha256: original}))
        with mock.patch.object(terminal, "current_source_semantic_material",
                               side_effect=ValueError("private material withheld")), \
             mock.patch.object(terminal, "project_source_route_leaf_material_from_validated_inputs") as project:
            project.return_value = ({original.leaf_sha256: original}, {"claim": (original.leaf_sha256,)})
            call = lambda source, public: terminal._validate_current_source_routes(
                loaded, source, SimpleNamespace(), paper_dir=Path("/fixture"),
                allow_withheld_source_material=public)
            self.assertEqual(call({}, True), {"claim": "claim"})
            with self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError, "private material withheld"):
                call({}, False)
            with self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError, "withheld source locator"):
                call({"source_text_file": "source.tex"}, True)
            project.return_value = ({changed.leaf_sha256: changed}, {"claim": (changed.leaf_sha256,)})
            with self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError, "semantic atoms changed"):
                call({}, True)
            project.return_value = ({original.leaf_sha256: original}, {"renamed": (original.leaf_sha256,)})
            with self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError, "source routes"):
                call({}, True)

    def test_module_discovery_failure_preserves_bounded_causal_diagnostic(self) -> None:
        root = Path("/tmp/diagnostic-fixture")
        provider = terminal.RepositoryBuildInputSnapshotProvider(root)
        reason = "Lake could not build +Fixture.PaperInterface:olean: timed out after 600 seconds"
        worktree = mock.Mock()
        worktree.record_for_entrypoint.return_value = (None, SimpleNamespace(reason=reason))
        provider._live_closure_provider = worktree
        with mock.patch(
            "scripts.lean_signature_manifest._repository_module_source_path",
            return_value=root / "papers/Fixture/PaperInterface.lean",
        ), self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError,
                                  "timed out after 600 seconds") as raised:
            terminal._current_paper_modules(root, "Fixture", "Fixture.PaperInterface",
                                            provider, timeout_seconds=600)
        self.assertIn("+Fixture.PaperInterface:olean", str(raised.exception))
        worktree.record_for_entrypoint.assert_called_once()

    def test_import_does_not_load_presentation_or_evidence_monoliths(self) -> None:
        root = Path(__file__).resolve().parents[2]
        process = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import json, sys; "
                    "import scripts.terminal_lean_semantic_revalidation; "
                    "print(json.dumps([name for name in ("
                    "'scripts.review_dashboard', "
                    "'scripts.review_dashboard_packet', "
                    "'scripts.audit_evidence_integrity', "
                    "'scripts.direct_semantic_review_binding') "
                    "if name in sys.modules]))"
                ),
            ],
            cwd=root,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout), [])

    def test_terminal_routes_cache_through_shared_graph_acquisition(self) -> None:
        route_set = terminal.EvidenceRouteSet.from_source_map(
            {
                "items": {
                    "model": {
                        "claim_bearing": True,
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                        "lean_declarations": ["Fixture.Model"],
                    },
                    "algorithm": {
                        "claim_bearing": True,
                        "source_kind": "algorithm",
                        "inventory_role": "named_result",
                        "semantic_contract": {
                            "spec_declaration": "Fixture.AlgorithmSpec",
                            "evidence_declaration": "Fixture.algorithmRealizes",
                            "evidence_mode": "definitionally_realizes",
                            "semantic_shape": "plain",
                        },
                        "semantic_review_target": {
                            "schema": 1,
                            "kind": "definition_declaration",
                            "declaration": "Fixture.Algorithm",
                        },
                    },
                }
            }
        )
        inventory = {"inventory": "lean-owned"}
        projection = SimpleNamespace(semantic_targets={})
        provider = SimpleNamespace()
        module_sources = {
            "Fixture.PaperInterface": (
                Path("/repo/papers/Fixture/PaperInterface.lean"),
                b"def placeholder := True\n",
            ),
            "AppliedModelingLib.Foundation": (
                Path("/repo/AppliedModelingLib/Foundation.lean"),
                b"def foundation := True\n",
            ),
        }
        with (
            mock.patch.object(
                terminal,
                "current_terminal_lean_graph_inventory",
                return_value=None,
            ),
            mock.patch.object(
                terminal,
                "acquire_validated_graph_projection",
                return_value=SimpleNamespace(
                    inventory=inventory,
                    projection=projection,
                    acquired_fresh=True,
                ),
            ) as acquire,
            mock.patch.object(
                terminal,
                "checkpoint_terminal_lean_graph",
            ) as checkpoint,
        ):
            request, acquired, projected = (
                terminal._acquire_terminal_graph_projection(
                    Path("/repo"),
                    Path("/repo/papers/Fixture"),
                    route_set=route_set,
                    expected_specifications={"Fixture.AlgorithmSpec"},
                    import_module="Fixture.PaperInterface",
                    paper_modules=("Fixture.PaperInterface",),
                    module_sources=module_sources,
                    accepted_import_closure={
                        "schema": 1,
                        "entry_module": "Fixture.PaperInterface",
                    },
                    assumption_names={"Fixture.Assumption"},
                    provider=provider,
                    build_timeout_seconds=600,
                )
            )
        self.assertIs(acquired, inventory)
        self.assertIs(projected, projection)
        self.assertEqual(request.specifications, ("Fixture.AlgorithmSpec",))
        self.assertEqual(
            request.semantic_review_claim_declarations,
            frozenset({"Fixture.Algorithm"}),
        )
        acquire.assert_called_once_with(
            Path("/repo"),
            Path("/repo/papers/Fixture"),
            request,
            module_sources=module_sources,
            inventory=None,
            build_input_provider=provider,
            additional_axiom_root_names={"Fixture.Assumption"},
            root_semantic_manifest_declaration_names={"Fixture.Assumption"},
            build_timeout_seconds=600,
        )
        checkpoint.assert_called_once()

        with (
            mock.patch.object(
                terminal,
                "current_terminal_lean_graph_inventory",
                return_value=inventory,
            ),
            mock.patch.object(
                terminal,
                "acquire_validated_graph_projection",
                return_value=SimpleNamespace(
                    inventory=inventory,
                    projection=projection,
                    acquired_fresh=False,
                ),
            ) as reuse,
            mock.patch.object(
                terminal,
                "checkpoint_terminal_lean_graph",
            ) as recheckpoint,
        ):
            terminal._acquire_terminal_graph_projection(
                Path("/repo"),
                Path("/repo/papers/Fixture"),
                route_set=route_set,
                expected_specifications={"Fixture.AlgorithmSpec"},
                import_module="Fixture.PaperInterface",
                paper_modules=("Fixture.PaperInterface",),
                module_sources=module_sources,
                accepted_import_closure={
                    "schema": 1,
                    "entry_module": "Fixture.PaperInterface",
                },
                assumption_names={"Fixture.Assumption"},
                provider=provider,
                build_timeout_seconds=600,
            )
        self.assertIs(reuse.call_args.kwargs["inventory"], inventory)
        recheckpoint.assert_not_called()

    def test_historical_code_reuse_uses_lean_owned_module_identity(self) -> None:
        paper_name = "Paper.Input"
        library_name = "AppliedModelingLib.Model"
        paper_path = Path("/repo/Paper/Main.lean")
        library_path = Path("/repo/AppliedModelingLib/Model.lean")
        paper_source = b"namespace Paper\nstructure Input where\n  value : Nat\nend Paper\n"
        library_source = b"def Model : Nat := 0\n"
        inventory = {
            "source_declarations": [],
            "declarations": [
                {
                    "declaration": paper_name,
                    "review_owner_declaration": paper_name,
                    "generated_from_owner": False,
                    "module": "Paper.Main",
                    "paper_owned": True,
                    "source_presented": True,
                    "source_range": {
                        "line_start": 2,
                        "column_start": 0,
                        "line_end": 3,
                        "column_end": len("  value : Nat"),
                    },
                    "declaration_kind": "structure",
                    "is_transparent_definition": False,
                    "type_display": "Type",
                }
            ],
            "library_prerequisite_displays": {
                "schema": "3",
                "items": [
                    {
                        "declaration": library_name,
                        "review_owner_declaration": library_name,
                        "source_module": "AppliedModelingLib.Model",
                        "source_line_start": 1,
                        "source_column_start": 0,
                        "source_line_end": 1,
                        "source_column_end": len("def Model : Nat := 0"),
                        "declaration_kind": "definition",
                        "root_expanded": True,
                    },
                    {
                        "declaration": "AppliedModelingLib.NewlyDiscovered",
                        "review_owner_declaration": "AppliedModelingLib.NewlyDiscovered",
                        "source_module": "AppliedModelingLib.Unavailable",
                        "source_line_start": 1,
                        "source_column_start": 0,
                        "source_line_end": 1,
                        "source_column_end": 1,
                        "declaration_kind": "definition",
                        "root_expanded": True,
                    },
                ],
            },
        }
        provider = SimpleNamespace(
            repository_source_snapshot=lambda _module: (
                (
                    "Paper.Main",
                    paper_path,
                    paper_source,
                    hashlib.sha256(paper_source).hexdigest(),
                ),
                (
                    "AppliedModelingLib.Model",
                    library_path,
                    library_source,
                    hashlib.sha256(library_source).hexdigest(),
                ),
            )
        )
        accepted_closure = {
            "sources": [
                {
                    "module": "Paper.Main",
                    "sha256": hashlib.sha256(paper_source).hexdigest(),
                },
                {
                    "module": "AppliedModelingLib.Model",
                    "sha256": hashlib.sha256(library_source).hexdigest(),
                },
            ]
        }
        result = terminal._unchanged_prerequisite_declarations_from_inventory(
            inventory,
            provider,
            "Paper.ProofInterface",
            accepted_closure,
            paper_declarations={paper_name},
            library_declarations={library_name},
        )
        self.assertEqual(result, {paper_name, library_name})

        accepted_closure["sources"][1]["sha256"] = "f" * 64
        self.assertEqual(
            terminal._unchanged_prerequisite_declarations_from_inventory(
                inventory,
                provider,
                "Paper.ProofInterface",
                accepted_closure,
                paper_declarations={paper_name},
                library_declarations={library_name},
            ),
            {paper_name},
        )

    def test_current_review_import_module_retains_authenticated_entry_module(self) -> None:
        for entry_module in (
            "Fixture", "Fixture.PaperInterface", "Fixture.AcceptedSurface",
        ):
            with self.subTest(entry_module=entry_module):
                self.assertEqual(
                    terminal._current_review_import_module(
                        {"review_surface": {
                            "source_file": "papers/Fixture/PaperInterface.lean",
                        }},
                        "Fixture",
                        accepted_import_closure={"entry_module": entry_module},
                    ),
                    entry_module,
                )

    def test_current_review_import_module_selects_separate_proof_surface(self) -> None:
        self.assertEqual(
            terminal._current_review_import_module(
                {"review_surface": {"proof_module": "Fixture.ProofInterface"}},
                "Fixture",
                accepted_import_closure={"entry_module": "Fixture.OldSurface"},
            ),
            "Fixture.ProofInterface",
        )

    def test_current_review_import_module_rejects_external_module(self) -> None:
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "not owned by the paper",
        ):
            terminal._current_review_import_module(
                {"review_surface": {"proof_module": "Other.ProofInterface"}},
                "Fixture",
                accepted_import_closure={"entry_module": "Fixture"},
            )

    def test_current_review_import_module_rejects_invalid_accepted_root(self) -> None:
        for entry_module in (None, "", "Fixture;other", "Other.ProofInterface"):
            with self.subTest(entry_module=entry_module), self.assertRaises(
                terminal.TerminalLeanSemanticRevalidationError,
            ):
                terminal._current_review_import_module(
                    {"review_surface": {}}, "Fixture",
                    accepted_import_closure={"entry_module": entry_module},
                )

    def test_missing_accepted_root_does_not_fall_back_to_spec_interface(self) -> None:
        provider = mock.Mock()
        provider.lean_loaded_module_names.return_value = ()
        provider.lean_loaded_module_error.return_value = "entry-module source is unavailable"
        module = terminal._current_review_import_module(
            {"review_surface": {}}, "Fixture",
            accepted_import_closure={"entry_module": "Fixture.AcceptedSurface"},
        )
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "entry-module source is unavailable",
        ):
            terminal._current_paper_modules(
                Path("/repo"), "Fixture", module, provider, timeout_seconds=17,
            )
        provider.lean_loaded_module_names.assert_called_once_with(
            "Fixture.AcceptedSurface", timeout_seconds=17,
        )
        provider.repository_source_snapshot.assert_not_called()

    def test_complete_review_surface_retains_lean_discovered_prerequisites(
        self,
    ) -> None:
        inventory = self._inventory_target("Paper.Input", "paper input")
        inventory["library_prerequisite_displays"] = {
            "schema": "3",
            "items": [
                {
                    "declaration": "AppliedModelingLib.Discovered",
                    "review_owner_declaration": "AppliedModelingLib.Discovered",
                    "source_module": "AppliedModelingLib.Discovered",
                    "source_line_start": 1,
                    "source_column_start": 0,
                    "source_line_end": 1,
                    "source_column_end": 10,
                    "declaration_kind": "definition",
                    "root_expanded": True,
                    "direct_library_declarations": [],
                    "erased_proof_declarations": [],
                    "display": "True",
                }
            ],
        }
        surface = lean_owned_semantic_review_display_surface_from_inventory(
            inventory,
            expected_specifications=set(),
        )
        self.assertEqual(set(surface.paper_declarations), {"Paper.Input"})
        self.assertEqual(
            set(surface.library_declarations),
            {"AppliedModelingLib.Discovered"},
        )

        display_sha256 = hashlib.sha256(b"paper input").hexdigest()
        loaded = self._loaded_prerequisite(
            "Paper.Input",
            {"reviewed_semantic_target_sha256": display_sha256},
        )
        terminal._validate_prerequisites(
            loaded,
            review_surface=surface,
            semantic_signatures={},
        )

    def test_terminal_recovery_rejects_missing_accepted_prerequisite(self) -> None:
        name = "Paper.Input"
        display_sha256 = hashlib.sha256(b"accepted input").hexdigest()
        loaded = self._loaded_prerequisite(
            name,
            {"reviewed_semantic_target_sha256": display_sha256},
        )
        inventory = self._inventory_target(name, "accepted input")
        inventory["paper_prerequisite_displays"]["items"] = []
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted prerequisite semantic identity",
        ):
            terminal._validate_prerequisites(
                loaded,
                review_surface=self._review_surface(inventory),
                semantic_signatures={},
            )

    @staticmethod
    def _accepted_direct_fixture(target_sha256: str) -> tuple[object, object]:
        spec_sha256 = "1" * 64
        endpoint_sha256 = "2" * 64
        review_leaf = SimpleNamespace(
            leaf_sha256=spec_sha256,
            semantic_payload={
                "semantic_target_kind": "spec_proposition",
                "reviewed_semantic_target_sha256": target_sha256,
                # Historical accepted leaves may retain syntax provenance.
                "declaration_content_sha256": "3" * 64,
            },
        )
        endpoint_leaf = SimpleNamespace(
            leaf_sha256=endpoint_sha256,
            semantic_payload={
                "spec_declaration_sha256": spec_sha256,
                "relation": "proves",
            },
        )
        realization_leaf = SimpleNamespace(
            leaf_sha256="4" * 64,
            semantic_payload={
                "spec_declaration_sha256": spec_sha256,
                "proof_endpoint_sha256": endpoint_sha256,
                "relation": "proves",
            },
        )
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "claim": {
                        "semantic_review": ("spec",),
                        "spec": ("spec",),
                        "proof_endpoint": ("endpoint",),
                        "proof_realization": ("realization",),
                    }
                }
            ),
            graph=SimpleNamespace(
                leaves={
                    "spec": review_leaf,
                    "endpoint": endpoint_leaf,
                    "realization": realization_leaf,
                }
            ),
        )
        route = SimpleNamespace(
            source_item_id="claim",
            semantic_review_declaration="Fixture.claimSpec",
            semantic_review_target_kind=SimpleNamespace(value="spec_proposition"),
            evidence_mode="proves",
        )
        return loaded, route

    def _loaded_prerequisite(self, name: str, payload: dict[str, str]) -> object:
        return SimpleNamespace(
            paper_index=SimpleNamespace(
                prerequisite_leaf_sha256s_by_declaration={
                    name: {"lean_declaration": ("leaf",)}
                }
            ),
            graph=SimpleNamespace(
                leaves={
                    "leaf": SimpleNamespace(
                        semantic_payload={
                            "semantic_target_kind": "semantic_prerequisite",
                            **payload,
                        }
                    )
                }
            ),
        )

    @staticmethod
    def _inventory_target(name: str, display: str) -> dict[str, object]:
        return {
            "transparent_spec_displays": {"schema": "2", "items": []},
            "paper_prerequisite_displays": {
                "schema": "2",
                "items": [
                    {
                        "declaration": name,
                        "display": display,
                        "declaration_kind": "definition",
                        "root_expanded": True,
                        "direct_paper_declarations": [],
                        "direct_library_declarations": [],
                        "erased_proof_declarations": [],
                    }
                ],
            },
            "library_prerequisite_displays": {"schema": "3", "items": []},
            "semantic_manifests": {"schema": "1", "items": [], "errors": []},
        }

    @staticmethod
    def _review_surface(inventory: dict[str, object]):
        section = inventory.get("transparent_spec_displays")
        rows = section.get("items") if isinstance(section, dict) else None
        expected_specifications = tuple(
            str(row.get("specification") or "").strip()
            for row in rows or []
            if isinstance(row, dict)
            and str(row.get("specification") or "").strip()
        )
        return lean_owned_semantic_review_display_surface_from_inventory(
            inventory,
            expected_specifications=expected_specifications,
        )

    def test_content_bound_prerequisite_requires_unchanged_module_and_target(
        self,
    ) -> None:
        name = "Paper.Input"
        reviewed_display = "accepted target"
        display_sha256 = hashlib.sha256(reviewed_display.encode("utf-8")).hexdigest()
        loaded = self._loaded_prerequisite(
            name,
            {
                "declaration_content_sha256": "a" * 64,
                "reviewed_semantic_target_sha256": display_sha256,
            },
        )
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(
                self._inventory_target(name, reviewed_display)
            ),
            semantic_signatures={},
            unchanged_declaration_names={name},
        )
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted prerequisite semantic identity",
        ):
            terminal._validate_prerequisites(
                loaded,
                review_surface=self._review_surface(
                    self._inventory_target(name, reviewed_display)
                ),
                semantic_signatures={},
                unchanged_declaration_names=set(),
            )

    def test_target_only_prerequisite_uses_same_terminal_check(self) -> None:
        name = "Paper.Input"
        display = "current target"
        display_sha256 = hashlib.sha256(display.encode("utf-8")).hexdigest()
        loaded = self._loaded_prerequisite(
            name,
            {"reviewed_semantic_target_sha256": display_sha256},
        )
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(
                self._inventory_target(name, display)
            ),
            semantic_signatures={},
        )

    def test_current_direct_target_must_equal_accepted_graph_leaf(self) -> None:
        accepted_target = "a" * 64
        loaded, route = self._accepted_direct_fixture(accepted_target)
        terminal._validate_accepted_direct_routes(
            loaded,
            (route,),
            {route.semantic_review_declaration: {"display_sha256": accepted_target}},
            {},
        )

        changed_target = "b" * 64
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted direct semantic target changed",
        ):
            terminal._validate_accepted_direct_routes(
                loaded,
                (route,),
                {route.semantic_review_declaration: {"display_sha256": changed_target}},
                {},
            )

    def test_all_changed_direct_routes_are_reported_from_one_acquisition(
        self,
    ) -> None:
        accepted_target = "a" * 64
        current_target = "b" * 64
        loaded, first = self._accepted_direct_fixture(accepted_target)

        second = SimpleNamespace(
            source_item_id="second_claim",
            semantic_review_declaration="Fixture.secondClaimSpec",
            semantic_review_target_kind=SimpleNamespace(value="spec_proposition"),
            evidence_mode="proves",
        )
        loaded.paper_index.route_leaf_sha256s_by_source_item[second.source_item_id] = {
            "semantic_review": ("second_spec",),
            "spec": ("second_spec",),
            "proof_endpoint": ("second_endpoint",),
            "proof_realization": ("second_realization",),
        }
        loaded.graph.leaves["second_spec"] = SimpleNamespace(
            leaf_sha256="5" * 64,
            semantic_payload={
                "semantic_target_kind": "spec_proposition",
                "reviewed_semantic_target_sha256": accepted_target,
            },
        )
        loaded.graph.leaves["second_endpoint"] = SimpleNamespace(
            leaf_sha256="6" * 64,
            semantic_payload={
                "spec_declaration_sha256": "5" * 64,
                "relation": "proves",
            },
        )
        loaded.graph.leaves["second_realization"] = SimpleNamespace(
            leaf_sha256="7" * 64,
            semantic_payload={
                "spec_declaration_sha256": "5" * 64,
                "proof_endpoint_sha256": "6" * 64,
                "relation": "proves",
            },
        )

        with self.assertRaises(
            terminal.TerminalLeanSemanticRevalidationError
        ) as raised:
            terminal._validate_accepted_direct_routes(
                loaded,
                (first, second),
                {
                    first.semantic_review_declaration: {"display_sha256": current_target},
                    second.semantic_review_declaration: {"display_sha256": current_target},
                },
                {},
            )
        message = str(raised.exception)
        self.assertIn("2 failure(s)", message)
        self.assertIn(first.semantic_review_declaration, message)
        self.assertIn(second.semantic_review_declaration, message)

    def test_current_source_routes_bind_exact_atoms_and_verbatim_bundle(self) -> None:
        bundle = "a" * 64
        atom = source_atom_leaf(
            contract_sha256="1" * 64,
            source_artifact_sha256="2" * 64,
            source_quote_sha256="3" * 64,
            source_component_sha256="4" * 64,
            source_role_contract_sha256="5" * 64,
        )
        judgment = SimpleNamespace(
            semantic_payload={
                "source_atom_sha256s": [atom.leaf_sha256],
                "verbatim_source_bundle_sha256": bundle,
            }
        )
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "claim": {
                        "source_atom": (atom.leaf_sha256,),
                        "source_lean_judgment": ("judgment",),
                    }
                },
                prerequisite_leaf_sha256s_by_declaration={},
            ),
            graph=SimpleNamespace(
                leaves={atom.leaf_sha256: atom, "judgment": judgment}
            ),
        )
        preflight = SimpleNamespace(
            require_current=lambda: None, prerequisite_source_item_by_declaration={}
        )
        with (
            mock.patch.object(
                terminal,
                "project_source_route_leaf_material_from_validated_inputs",
                return_value=(
                    {atom.leaf_sha256: atom},
                    {"claim": (atom.leaf_sha256,)},
                ),
            ),
            mock.patch.object(
                terminal,
                "current_source_semantic_material",
                return_value={
                    "claim": SimpleNamespace(source_input_bundle_sha256=bundle)
                },
            ),
        ):
            terminal._validate_current_source_routes(
                loaded,
                {"items": {}},
                preflight,
                paper_dir=SimpleNamespace(),
            )
            judgment.semantic_payload["verbatim_source_bundle_sha256"] = "b" * 64
            with self.assertRaisesRegex(
                terminal.TerminalLeanSemanticRevalidationError,
                "verbatim source bundle changed",
            ):
                terminal._validate_current_source_routes(
                    loaded,
                    {"items": {}},
                    preflight,
                    paper_dir=SimpleNamespace(),
                )

    def test_source_route_recovery_compares_historical_atom_by_semantics(self) -> None:
        fields = {
            "contract_sha256": "1" * 64,
            "source_artifact_sha256": "2" * 64,
            "source_quote_sha256": "3" * 64,
            "source_component_sha256": "4" * 64,
            "source_role_contract_sha256": "5" * 64,
        }
        accepted = legacy_artifact_bound_source_atom_leaf(**fields)
        current = source_atom_leaf(**fields)
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "claim": {"source_atom": (accepted.leaf_sha256,)}
                },
                prerequisite_leaf_sha256s_by_declaration={},
            ),
            graph=SimpleNamespace(leaves={accepted.leaf_sha256: accepted}),
        )
        with (
            mock.patch.object(
                terminal,
                "project_source_route_leaf_material_from_validated_inputs",
                return_value=(
                    {current.leaf_sha256: current},
                    {"claim": (current.leaf_sha256,)},
                ),
            ),
            mock.patch.object(
                terminal,
                "current_source_semantic_material",
                return_value={
                    "claim": SimpleNamespace(source_input_bundle_sha256="6" * 64)
                },
            ),
        ):
            terminal._validate_current_source_routes(
                loaded,
                {"items": {}},
                SimpleNamespace(
                    require_current=lambda: None,
                    prerequisite_source_item_by_declaration={},
                ),
                paper_dir=SimpleNamespace(),
            )

    def test_source_route_key_rename_rebinds_by_exact_semantics(self) -> None:
        bundle = "a" * 64
        atom = source_atom_leaf(
            contract_sha256="1" * 64,
            source_artifact_sha256="2" * 64,
            source_quote_sha256="3" * 64,
            source_component_sha256="4" * 64,
            source_role_contract_sha256="5" * 64,
        )
        judgment = SimpleNamespace(
            semantic_payload={
                "source_atom_sha256s": [atom.leaf_sha256],
                "verbatim_source_bundle_sha256": bundle,
            }
        )
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "old_claim": {
                        "source_atom": (atom.leaf_sha256,),
                        "source_lean_judgment": ("judgment",),
                    }
                },
                prerequisite_leaf_sha256s_by_declaration={},
            ),
            graph=SimpleNamespace(
                leaves={atom.leaf_sha256: atom, "judgment": judgment}
            ),
        )
        preflight = SimpleNamespace(
            require_current=lambda: None,
            prerequisite_source_item_by_declaration={},
            route_set=SimpleNamespace(
                result_routes=lambda: (
                    SimpleNamespace(source_item_id="renamed_claim"),
                )
            ),
        )
        with (
            mock.patch.object(
                terminal,
                "project_source_route_leaf_material_from_validated_inputs",
                return_value=(
                    {atom.leaf_sha256: atom},
                    {"renamed_claim": (atom.leaf_sha256,)},
                ),
            ),
            mock.patch.object(
                terminal,
                "current_source_semantic_material",
                return_value={
                    "renamed_claim": SimpleNamespace(
                        source_input_bundle_sha256=bundle
                    )
                },
            ),
        ):
            self.assertEqual(
                terminal._validate_current_source_routes(
                    loaded,
                    {"items": {}},
                    preflight,
                    paper_dir=SimpleNamespace(),
                ),
                {"renamed_claim": "old_claim"},
            )

    def test_shared_atom_does_not_cross_source_item_bundle_routes(self) -> None:
        atom = source_atom_leaf(
            contract_sha256="1" * 64,
            source_artifact_sha256="2" * 64,
            source_quote_sha256="3" * 64,
            source_component_sha256="4" * 64,
            source_role_contract_sha256="5" * 64,
        )
        bundles = {"first": "a" * 64, "second": "b" * 64}
        leaves = {atom.leaf_sha256: atom}
        prerequisites = {}
        for source_item, declaration in (
            ("first", "Paper.FirstInput"),
            ("second", "Paper.SecondInput"),
        ):
            judgment_id = "judgment-" + source_item
            leaves[judgment_id] = SimpleNamespace(
                semantic_payload={
                    "source_atom_sha256s": [atom.leaf_sha256],
                    "verbatim_source_bundle_sha256": bundles[source_item],
                }
            )
            prerequisites[declaration] = {
                "source_atom": (atom.leaf_sha256,),
                "source_lean_judgment": (judgment_id,),
            }
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    source_item: {"source_atom": (atom.leaf_sha256,)}
                    for source_item in bundles
                },
                prerequisite_leaf_sha256s_by_declaration=prerequisites,
            ),
            graph=SimpleNamespace(leaves=leaves),
        )
        with (
            mock.patch.object(
                terminal,
                "project_source_route_leaf_material_from_validated_inputs",
                return_value=(
                    {atom.leaf_sha256: atom},
                    {source_item: (atom.leaf_sha256,) for source_item in bundles},
                ),
            ),
            mock.patch.object(
                terminal,
                "current_source_semantic_material",
                return_value={
                    source_item: SimpleNamespace(source_input_bundle_sha256=bundle)
                    for source_item, bundle in bundles.items()
                },
            ),
        ):
            terminal._validate_current_source_routes(
                loaded,
                {"items": {}},
                SimpleNamespace(
                    require_current=lambda: None,
                    prerequisite_source_item_by_declaration={
                        "Paper.FirstInput": "first",
                        "Paper.SecondInput": "second",
                    },
                ),
                paper_dir=SimpleNamespace(),
            )

    def test_authenticated_owners_bind_distinct_bundles_with_shared_atoms(
        self,
    ) -> None:
        atom = source_atom_leaf(
            contract_sha256="1" * 64,
            source_artifact_sha256="2" * 64,
            source_quote_sha256="3" * 64,
            source_component_sha256="4" * 64,
            source_role_contract_sha256="5" * 64,
        )
        bundles = {"dimension": "a" * 64, "recovery": "b" * 64}
        leaves = {atom.leaf_sha256: atom}
        prerequisites = {}
        authenticated_owners = {}
        for source_item, declaration in (
            ("dimension", "Paper.DimensionValue"),
            ("recovery", "Paper.RecoveryCondition"),
        ):
            judgment_id = "judgment-" + source_item
            leaves[judgment_id] = SimpleNamespace(
                semantic_payload={
                    "source_atom_sha256s": [atom.leaf_sha256],
                    "verbatim_source_bundle_sha256": bundles[source_item],
                }
            )
            prerequisites[declaration] = {
                "source_atom": (atom.leaf_sha256,),
                "source_lean_judgment": (judgment_id,),
            }
            authenticated_owners[declaration] = source_item
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    source_item: {"source_atom": (atom.leaf_sha256,)}
                    for source_item in bundles
                },
                prerequisite_leaf_sha256s_by_declaration=prerequisites,
            ),
            graph=SimpleNamespace(leaves=leaves),
        )
        preflight = SimpleNamespace(
            require_current=lambda: None,
            prerequisite_source_item_by_declaration={},
        )
        with (
            mock.patch.object(
                terminal,
                "project_source_route_leaf_material_from_validated_inputs",
                return_value=(
                    {atom.leaf_sha256: atom},
                    {source_item: (atom.leaf_sha256,) for source_item in bundles},
                ),
            ),
            mock.patch.object(
                terminal,
                "current_source_semantic_material",
                return_value={
                    source_item: SimpleNamespace(source_input_bundle_sha256=bundle)
                    for source_item, bundle in bundles.items()
                },
            ),
        ):
            terminal._validate_current_source_routes(
                loaded,
                {"items": {}},
                preflight,
                paper_dir=SimpleNamespace(),
                authenticated_prerequisite_source_items_by_declaration=(
                    authenticated_owners
                ),
            )

    def test_prerequisite_judgment_keeps_proof_support_bundle_current(self) -> None:
        """Historical prerequisite evidence survives fresh route reclassification.

        A completed graph can bind a source item to a semantic-prerequisite
        judgment even when the current role-typed route classifies that source
        presentation as proof support.  Recovery must authenticate that same
        full bundle, rather than omit it because the presentation is no longer
        a fresh ``source_semantic_declaration`` route.
        """

        bundle = "a" * 64
        atom = source_atom_leaf(
            contract_sha256="1" * 64,
            source_artifact_sha256="2" * 64,
            source_quote_sha256="3" * 64,
            source_component_sha256="4" * 64,
            source_role_contract_sha256="5" * 64,
        )
        judgment = SimpleNamespace(
            semantic_payload={
                "source_atom_sha256s": [atom.leaf_sha256],
                "verbatim_source_bundle_sha256": bundle,
            }
        )
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "historical_prerequisite": {
                        "source_atom": (atom.leaf_sha256,)
                    }
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.HistoricalPrerequisite": {
                        "source_atom": (atom.leaf_sha256,),
                        "source_lean_judgment": ("judgment",),
                    }
                },
            ),
            graph=SimpleNamespace(
                leaves={atom.leaf_sha256: atom, "judgment": judgment}
            ),
        )
        current_material = SimpleNamespace(source_input_bundle_sha256=bundle)
        preflight = SimpleNamespace(
            require_current=lambda: None,
            prerequisite_source_item_by_declaration={
                "Fixture.HistoricalPrerequisite": "historical_prerequisite"
            },
            route_set=SimpleNamespace(
                result_routes=lambda: (),
                routes=(
                    SimpleNamespace(
                        source_item_id="historical_prerequisite",
                        route_kind=terminal.RouteKind.PROOF_SUPPORT,
                    ),
                ),
            ),
        )
        with (
            mock.patch.object(
                terminal,
                "project_source_route_leaf_material_from_validated_inputs",
                return_value=(
                    {atom.leaf_sha256: atom},
                    {"historical_prerequisite": (atom.leaf_sha256,)},
                ),
            ),
            mock.patch.object(
                terminal,
                "current_source_semantic_material",
                return_value={"historical_prerequisite": current_material},
            ),
        ):
            terminal._validate_current_source_routes(
                loaded,
                {"items": {}},
                preflight,
                paper_dir=SimpleNamespace(),
            )
            # The normal full bundle includes approved-review contexts.  A
            # changed quote or changed bound context must remain fail-closed.
            current_material.source_input_bundle_sha256 = "b" * 64
            with self.assertRaisesRegex(
                terminal.TerminalLeanSemanticRevalidationError,
                "verbatim source bundle changed",
            ):
                terminal._validate_current_source_routes(
                    loaded,
                    {"items": {}},
                    preflight,
                    paper_dir=SimpleNamespace(),
                )

    def test_accepted_direct_routes_are_bidirectionally_complete(self) -> None:
        target = "a" * 64
        loaded, route = self._accepted_direct_fixture(target)
        loaded.paper_index.route_leaf_sha256s_by_source_item["removed_claim"] = {
            "semantic_review": ("spec",),
            "spec": ("spec",),
            "proof_endpoint": ("endpoint",),
            "proof_realization": ("realization",),
        }
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "direct routes differ from the current paper surface",
        ):
            terminal._validate_accepted_direct_routes(
                loaded,
                (route,),
                {route.semantic_review_declaration: {"display_sha256": target}},
                {},
            )

    def test_accepted_direct_route_uses_semantic_source_key_binding(self) -> None:
        target = "a" * 64
        loaded, route = self._accepted_direct_fixture(target)
        route.source_item_id = "renamed_claim"
        terminal._validate_accepted_direct_routes(
            loaded,
            (route,),
            {route.semantic_review_declaration: {"display_sha256": target}},
            {},
            {"renamed_claim": "claim"},
        )

    def test_current_direct_relation_must_equal_accepted_graph_leaf(self) -> None:
        target = "a" * 64
        loaded, route = self._accepted_direct_fixture(target)
        route.evidence_mode = "refutes"
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted direct typed relation changed",
        ):
            terminal._validate_accepted_direct_routes(
                loaded,
                (route,),
                {route.semantic_review_declaration: {"display_sha256": target}},
                {},
            )

    def test_legacy_direct_manifest_ignores_renderer_bytes(self) -> None:
        target = "a" * 64
        loaded, route = self._accepted_direct_fixture(target)
        legacy_spec = {
            "semantic_target_kind": "spec_proposition",
            "elaborated_signature_sha256": "5" * 64,
            "elaborated_proposition_graph_sha256": "6" * 64,
            "semantic_dependency_sha256": "7" * 64,
        }
        legacy_endpoint = {
            "semantic_target_kind": "proof_endpoint",
            "elaborated_signature_sha256": "8" * 64,
            "elaborated_proposition_graph_sha256": "9" * 64,
            "semantic_dependency_sha256": "b" * 64,
        }
        loaded.graph.leaves["spec"].semantic_payload = legacy_spec
        loaded.graph.leaves["endpoint"].semantic_payload = legacy_endpoint
        terminal._validate_accepted_direct_routes(
            loaded,
            (route,),
            {route.semantic_review_declaration: {"display_sha256": "c" * 64}},
            {
                route.semantic_review_declaration: legacy_spec[
                    "elaborated_signature_sha256"
                ]
            },
        )

        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted direct semantic target changed",
        ):
            terminal._validate_accepted_direct_routes(
                loaded,
                (route,),
                {route.semantic_review_declaration: {"display_sha256": target}},
                {route.semantic_review_declaration: "f" * 64},
            )

    def test_identity_bound_direct_review_requires_display_and_signature(
        self,
    ) -> None:
        reviewed_display = "a" * 64
        accepted_signature = "5" * 64
        loaded, route = self._accepted_direct_fixture(reviewed_display)
        loaded.graph.leaves["spec"].semantic_payload = {
            "semantic_target_kind": "spec_proposition",
            "reviewed_semantic_target_sha256": reviewed_display,
            "elaborated_signature_sha256": accepted_signature,
        }
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted direct semantic target changed",
        ):
            terminal._validate_accepted_direct_routes(
                loaded,
                (route,),
                {route.semantic_review_declaration: {"display_sha256": "c" * 64}},
                {route.semantic_review_declaration: accepted_signature},
            )
        terminal._validate_accepted_direct_routes(
            loaded,
            (route,),
            {
                route.semantic_review_declaration: {
                    "display_sha256": reviewed_display
                }
            },
            {route.semantic_review_declaration: accepted_signature},
        )
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted direct semantic target changed",
        ):
            terminal._validate_accepted_direct_routes(
                loaded,
                (route,),
                {
                    route.semantic_review_declaration: {
                        "display_sha256": reviewed_display
                    }
                },
                {route.semantic_review_declaration: "f" * 64},
            )

    def test_changed_container_rejects_legacy_direct_even_with_equal_signature(
        self,
    ) -> None:
        loaded, route = self._accepted_direct_fixture("a" * 64)
        payload = {
            "semantic_target_kind": "spec_proposition",
            "elaborated_signature_sha256": "5" * 64,
            "elaborated_proposition_graph_sha256": "6" * 64,
            "semantic_dependency_sha256": "7" * 64,
        }
        loaded.graph.leaves["spec"].semantic_payload = payload
        for reviewed_target in (None, "", " "):
            if reviewed_target is not None:
                payload["reviewed_semantic_target_sha256"] = reviewed_target
            with self.subTest(reviewed_target=reviewed_target), self.assertRaisesRegex(
                terminal.TerminalLeanSemanticRevalidationError,
                "changed-container recovery.*require deliberate new acceptance",
            ):
                terminal._validate_accepted_direct_routes(
                    loaded,
                    (route,),
                    {route.semantic_review_declaration: {"display_sha256": "c" * 64}},
                    {route.semantic_review_declaration: "5" * 64},
                    require_reviewed_display=True,
                )

    def test_legacy_prerequisite_manifest_ignores_renderer_bytes(self) -> None:
        name = "Paper.LegacyInput"
        legacy_payload = {
            "semantic_target_kind": "semantic_prerequisite",
            "elaborated_signature_sha256": "c" * 64,
            "elaborated_proposition_graph_sha256": "d" * 64,
            "semantic_dependency_sha256": "e" * 64,
        }
        loaded = self._loaded_prerequisite(name, legacy_payload)
        inventory = self._inventory_target(name, "current target")
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(inventory),
            semantic_signatures={
                name: legacy_payload["elaborated_signature_sha256"]
            },
        )

        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted prerequisite semantic identity",
        ):
            terminal._validate_prerequisites(
                loaded,
                review_surface=self._review_surface(inventory),
                semantic_signatures={name: "f" * 64},
            )

    def test_identity_bound_prerequisite_requires_display_and_signature(
        self,
    ) -> None:
        name = "Paper.Input"
        accepted_display = "accepted expanded display"
        reviewed_display = hashlib.sha256(
            accepted_display.encode("utf-8")
        ).hexdigest()
        accepted_signature = "c" * 64
        loaded = self._loaded_prerequisite(
            name,
            {
                "semantic_target_kind": "semantic_prerequisite",
                "reviewed_semantic_target_sha256": reviewed_display,
                "elaborated_signature_sha256": accepted_signature,
            },
        )
        inventory = self._inventory_target(name, accepted_display)
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(inventory),
            semantic_signatures={name: accepted_signature},
        )
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted prerequisite semantic identity",
        ):
            terminal._validate_prerequisites(
                loaded,
                review_surface=self._review_surface(
                    self._inventory_target(name, "changed expanded display")
                ),
                semantic_signatures={name: accepted_signature},
            )
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted prerequisite semantic identity",
        ):
            terminal._validate_prerequisites(
                loaded,
                review_surface=self._review_surface(inventory),
                semantic_signatures={name: "f" * 64},
            )

    def test_changed_container_rejects_legacy_prerequisite_with_equal_signature(
        self,
    ) -> None:
        name = "Paper.LegacyInput"
        payload = {
            "elaborated_signature_sha256": "c" * 64,
            "elaborated_proposition_graph_sha256": "d" * 64,
            "semantic_dependency_sha256": "e" * 64,
        }
        for reviewed_target in (None, "", " "):
            if reviewed_target is not None:
                payload["reviewed_semantic_target_sha256"] = reviewed_target
            with self.subTest(reviewed_target=reviewed_target), self.assertRaisesRegex(
                terminal.TerminalLeanSemanticRevalidationError,
                "changed-container recovery.*require deliberate new acceptance",
            ):
                terminal._validate_prerequisites(
                    self._loaded_prerequisite(name, payload),
                    review_surface=self._review_surface(
                        self._inventory_target(name, "current target")
                    ),
                    semantic_signatures={name: "c" * 64},
                    require_reviewed_display=True,
                )

    def test_all_changed_prerequisites_are_reported_from_one_acquisition(
        self,
    ) -> None:
        names = ("Paper.FirstInput", "Paper.SecondInput")
        reviewed_display = "b" * 64
        accepted_signature = "c" * 64
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                prerequisite_leaf_sha256s_by_declaration={
                    name: {"lean_declaration": (f"leaf-{index}",)}
                    for index, name in enumerate(names)
                }
            ),
            graph=SimpleNamespace(
                leaves={
                    f"leaf-{index}": SimpleNamespace(
                        semantic_payload={
                            "semantic_target_kind": "semantic_prerequisite",
                            "reviewed_semantic_target_sha256": reviewed_display,
                            "elaborated_signature_sha256": accepted_signature,
                        }
                    )
                    for index, _name in enumerate(names)
                }
            ),
        )
        inventory = {
            "transparent_spec_displays": {"schema": "2", "items": []},
            "paper_prerequisite_displays": {
                "schema": "2",
                "items": [
                    {
                        "declaration": name,
                        "display": "renderer output",
                        "declaration_kind": "definition",
                        "root_expanded": True,
                        "direct_paper_declarations": [],
                        "direct_library_declarations": [],
                        "erased_proof_declarations": [],
                    }
                    for name in names
                ],
            },
            "library_prerequisite_displays": {"schema": "3", "items": []},
        }
        with self.assertRaises(
            terminal.TerminalLeanSemanticRevalidationError
        ) as raised:
            terminal._validate_prerequisites(
                loaded,
                review_surface=self._review_surface(inventory),
                semantic_signatures={name: "f" * 64 for name in names},
            )
        message = str(raised.exception)
        self.assertIn("2 accepted prerequisite", message)
        for name in names:
            self.assertIn(name, message)

    def test_terminal_recovery_does_not_add_new_direct_prerequisite(self) -> None:
        name = "Paper.Input"
        display = "current target"
        display_sha256 = hashlib.sha256(display.encode("utf-8")).hexdigest()
        loaded = self._loaded_prerequisite(
            name,
            {"reviewed_semantic_target_sha256": display_sha256},
        )
        inventory = self._inventory_target(name, display)
        inventory["transparent_spec_displays"]["items"] = [
            {
                "specification": "Paper.ClaimSpec",
                "complete": True,
                "expansion_count": "0",
                "expanded_declarations": [],
                "prerequisite_declarations": [],
                "library_declarations": ["AppliedModelingLib.Hidden"],
                "erased_proof_declarations": [],
                "blocked_declarations": [],
                "display": "True",
            }
        ]
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(inventory),
            semantic_signatures={},
        )

    def test_terminal_recovery_does_not_add_new_transitive_prerequisite(self) -> None:
        name = "Paper.Input"
        display = "current target"
        display_sha256 = hashlib.sha256(display.encode("utf-8")).hexdigest()
        loaded = self._loaded_prerequisite(
            name,
            {"reviewed_semantic_target_sha256": display_sha256},
        )
        inventory = self._inventory_target(name, display)
        inventory["paper_prerequisite_displays"]["items"][0][
            "direct_library_declarations"
        ] = ["AppliedModelingLib.Hidden"]
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(inventory),
            semantic_signatures={},
        )

    def test_prerequisite_semantic_identity_survives_unique_rename(self) -> None:
        signature = "5" * 64
        loaded = self._loaded_prerequisite(
            "Paper.OldInput",
            {"elaborated_signature_sha256": signature},
        )
        inventory = self._inventory_target("Paper.NewInput", "renderer changed")
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(inventory),
            semantic_signatures={"Paper.NewInput": signature},
        )

    def test_prerequisite_semantic_rename_must_be_unambiguous(self) -> None:
        signature = "5" * 64
        loaded = self._loaded_prerequisite(
            "Paper.OldInput",
            {"elaborated_signature_sha256": signature},
        )
        inventory = self._inventory_target("Paper.FirstInput", "first")
        inventory["paper_prerequisite_displays"]["items"].append(
            {
                "declaration": "Paper.SecondInput",
                "display": "second",
                "declaration_kind": "definition",
                "root_expanded": True,
                "direct_paper_declarations": [],
                "direct_library_declarations": [],
                "erased_proof_declarations": [],
            }
        )
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "accepted prerequisite semantic identity",
        ):
            terminal._validate_prerequisites(
                loaded,
                review_surface=self._review_surface(inventory),
                semantic_signatures={
                    "Paper.FirstInput": signature,
                    "Paper.SecondInput": signature,
                },
            )

    def test_current_lean_prerequisite_surface_may_be_a_superset(self) -> None:
        accepted_signature = "1" * 64
        loaded = self._loaded_prerequisite(
            "Paper.Accepted",
            {"elaborated_signature_sha256": accepted_signature},
        )
        inventory = self._inventory_target("Paper.Accepted", "accepted")
        inventory["paper_prerequisite_displays"]["items"].append(
            {
                "declaration": "Paper.CurrentOnly",
                "display": "current only",
                "declaration_kind": "definition",
                "root_expanded": True,
                "direct_paper_declarations": [],
                "direct_library_declarations": [],
                "erased_proof_declarations": [],
            }
        )
        terminal._validate_prerequisites(
            loaded,
            review_surface=self._review_surface(inventory),
            semantic_signatures={
                "Paper.Accepted": accepted_signature,
                "Paper.CurrentOnly": "2" * 64,
            },
        )

    def test_assumption_discovery_names_use_shared_qualification_not_order(self) -> None:
        self.assertEqual(
            terminal._configured_assumption_names(
                {"review_surface": {"assumption_names": ["z", "Paper.a"]}},
                entry_module="Paper.ProofInterface",
            ),
            ("Paper.a", "Paper.z"),
        )
        for names in (["a", "a"], ["a", " a "], [""], [None], "a"):
            with self.subTest(names=names), self.assertRaisesRegex(
                terminal.TerminalLeanSemanticRevalidationError, "malformed"
            ):
                terminal._configured_assumption_names(
                    {"review_surface": {"assumption_names": names}},
                    entry_module="Paper.ProofInterface",
                )

    def test_recovery_reads_historical_rows_only_after_native_axiom_discovery(self) -> None:
        self._run_mock_assumption_recovery(self._axiom_inventory({
            "Paper.result": {"propext"},
            "Paper.z": {"propext"},
            "Paper.a": {"Classical.choice"},
        }))

    def test_differing_current_carrier_drives_graph_and_disables_source_shortcut(
        self,
    ) -> None:
        self._run_mock_assumption_recovery(
            self._axiom_inventory(
                {
                    "Paper.result": {"propext"},
                    "Paper.z": {"propext"},
                    "Paper.a": {"Classical.choice"},
                }
            ),
            current_import_closure={"entry_module": "Paper.Current"},
        )

    def _run_mock_assumption_recovery(
        self, inventory: dict, raw_audit: dict | None = None,
        *, assumption_names: list[str] | None = None,
        current_import_closure: dict | None = None,
    ) -> tuple[Path, ...]:
        """Exercise real recovery orchestration around one mocked native graph."""

        root = Path("/repo")
        folder = root / "papers" / "Paper"
        route = SimpleNamespace(
            spec_declaration="Paper.Spec",
            evidence_declaration="Paper.result",
            semantic_review_declaration="Paper.Spec",
        )
        preflight = SimpleNamespace(
            require_current=lambda: None,
            route_set=SimpleNamespace(result_routes=lambda: (route,)),
        )
        plan = SimpleNamespace(specifications=("Paper.Spec",), selected_routes=(route,))
        projection = SimpleNamespace(
            semantic_targets={"Paper.Spec": {}},
            paper_semantic_targets={}, library_semantic_targets={},
        )
        provider = SimpleNamespace(
            root=root,
            owns_exact_lean_import_closure_payload=(
                lambda value: value is current_import_closure
            ),
        )
        loaded = SimpleNamespace(paper_index=SimpleNamespace(
            prerequisite_leaf_sha256s_by_declaration={}
        ))
        status = {"review_surface": {"assumption_names": (
            ["z", "a"] if assumption_names is None else assumption_names
        )}}
        snapshots = {folder / "status.json": b"status",
                     folder / "audit/paper_statement_map.json": b"map"}
        if raw_audit is not None:
            snapshots[folder / "audit/source_record_audit.json"] = b"historical axiom pin"

        def read_json(path: Path, label: str) -> tuple[dict, bytes]:
            if path not in snapshots:
                raise AssertionError("condition-only recovery opened a legacy carrier")
            if path.name == "source_record_audit.json":
                assert raw_audit is not None
                return raw_audit, snapshots[path]
            return (status if path.name == "status.json" else {}), snapshots[path]

        with ExitStack() as stack:
            validators = {}
            for name in ("_validate_current_source_routes", "_validate_accepted_direct_routes",
                         "_validate_prerequisites"):
                validators[name] = stack.enter_context(
                    mock.patch.object(terminal, name, return_value={})
                )
            unchanged = stack.enter_context(mock.patch.object(
                terminal,
                "_unchanged_prerequisite_declarations_from_inventory",
                return_value={},
            ))
            reader = stack.enter_context(mock.patch.object(
                terminal, "_json_bytes", side_effect=read_json
            ))
            discover = stack.enter_context(mock.patch.object(
                terminal, "_current_paper_modules",
                return_value=(("Paper", "Paper.PaperInterface"), {}),
            ))
            acquire = stack.enter_context(mock.patch.object(
                terminal, "_acquire_terminal_graph_projection",
                return_value=(plan, inventory, projection),
            ))
            stack.enter_context(mock.patch.object(
                Path, "read_bytes", autospec=True, side_effect=lambda path: snapshots[path]
            ))
            try:
                actual_provider, inputs = terminal.revalidate_terminal_lean_semantics(
                    root, "Paper", loaded, preflight=preflight,
                    accepted_import_closure={"entry_module": "Paper"},
                    current_import_closure=current_import_closure,
                    build_input_provider=provider,
                )
            finally:
                self.assertNotIn(
                    folder / "audit/source_record_audit.json",
                    [call.args[0] for call in reader.call_args_list],
                )
        self.assertIs(actual_provider, provider)
        for name in ("_validate_accepted_direct_routes", "_validate_prerequisites"):
            self.assertEqual(
                validators[name].call_args.kwargs["require_reviewed_display"],
                current_import_closure is not None,
            )
        self.assertEqual(set(inputs), set(snapshots))
        expected_module = (
            "Paper.Current" if current_import_closure is not None else "Paper"
        )
        self.assertEqual(discover.call_args.args[2], expected_module)
        self.assertEqual(acquire.call_args.kwargs["import_module"], expected_module)
        if current_import_closure is not None:
            self.assertIs(
                acquire.call_args.kwargs["accepted_import_closure"],
                current_import_closure,
            )
            unchanged.assert_not_called()
        else:
            unchanged.assert_called_once()
        self.assertEqual(acquire.call_args.kwargs["assumption_names"], (
            {"Paper.a", "Paper.z"} if assumption_names is None else set(assumption_names)
        ))
        return inputs

    def test_current_self_pinned_axiom_cannot_authorize_historical_recovery(self) -> None:
        from scripts.authenticated_manifest_store import elaborated_proposition_graph_sha256
        from scripts.lean_signature_manifest import MANIFEST_SCHEMA, signature_manifest_digest
        from scripts.source_record_semantic_reuse import manifest_root_matches_configured_row

        manifest = {
            "schema": MANIFEST_SCHEMA,
            "declaration_kind": "axiom",
            "conclusion_mode": "type_only",
            "atoms": [{"ref": "result", "role": "conclusion",
                       "canonical": {"tag": "fixture_proposition", "value": "accepted"}}],
            "elaborated_proposition_graph": {"root": "accepted proposition"},
        }
        manifest["sha256"] = signature_manifest_digest(manifest)
        self.assertEqual(len(manifest["sha256"]), 64)
        row = {
            "row": "external_boundary", "qualified_declaration": "Paper.a",
            "elaborated_signature_sha256": manifest["sha256"],
            "elaborated_proposition_graph_sha256": elaborated_proposition_graph_sha256(
                manifest["elaborated_proposition_graph"]
            ),
        }
        raw_audit = {"configured_review_rows": [row],
                     "semantic_model_configured_assumption_rows": ["external_boundary"]}
        closures = {"Paper.result": {"Paper.a"}, "Paper.a": {"Paper.a"},
                    "Paper.z": {"propext"}}

        # The new current row really matches the native proposition, but it
        # supplies consistency, not historical acceptance authority.
        self.assertTrue(manifest_root_matches_configured_row(manifest, row))
        for carrier in ({}, raw_audit):
            with self.subTest(self_pinned=bool(carrier)), self.assertRaisesRegex(
                terminal.TerminalLeanSemanticRevalidationError,
                "historical accepted graph lacks authenticated axiom-boundary evidence",
            ):
                self._run_mock_assumption_recovery(
                    self._axiom_inventory(closures, {"Paper.a": manifest}), carrier,
                )

    @staticmethod
    def _axiom_inventory(
        closures: dict[str, set[str]], manifests: dict[str, object] | None = None
    ) -> dict[str, object]:
        return {
            "declarations": [
                {
                    "declaration": name,
                    "axiom_closure_checked": True,
                    "axiom_closure": sorted(values),
                }
                for name, values in sorted(closures.items())
            ],
            "root_semantic_manifests": {
                "schema": "1",
                "items": [
                    {"declaration": name, "manifest": value}
                    for name, value in sorted((manifests or {}).items())
                ],
                "errors": [],
            },
        }

    def test_native_material_selection_excludes_condition_definitions(self) -> None:
        self.assertEqual(terminal._material_axiom_boundary_names(
            proof_endpoints={"Paper.result"},
            configured_names={"Paper.usedBoundary", "Paper.condition"},
            inventory=self._axiom_inventory({
                "Paper.result": {"propext", "Paper.usedBoundary"},
                "Paper.usedBoundary": {"Paper.usedBoundary"},
                "Paper.condition": {"propext"},
            }),
        ), {"Paper.usedBoundary"})

    def test_standalone_configured_axiom_boundary_remains_material(self) -> None:
        self.assertEqual(terminal._material_axiom_boundary_names(
            proof_endpoints={"Paper.result"},
            configured_names={"Paper.externalBoundary"},
            inventory=self._axiom_inventory({
                "Paper.result": {"propext"},
                "Paper.externalBoundary": {"Paper.externalBoundary"},
            }),
        ), {"Paper.externalBoundary"})

    def test_unconfigured_transitive_axiom_fails_closed(self) -> None:
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "lacks authenticated axiom-boundary evidence for: Paper.hiddenBoundary",
        ):
            self._run_mock_assumption_recovery(
                self._axiom_inventory({"Paper.result": {"Paper.hiddenBoundary"}}),
                assumption_names=[],
            )

    def test_standalone_wrapper_cannot_hide_material_axiom(self) -> None:
        with self.assertRaisesRegex(
            terminal.TerminalLeanSemanticRevalidationError,
            "lacks authenticated axiom-boundary evidence for: Paper.hiddenBoundary",
        ):
            self._run_mock_assumption_recovery(self._axiom_inventory({
                "Paper.result": {"propext"},
                "Paper.a": {"Paper.hiddenBoundary"},
                "Paper.z": {"Classical.choice"},
            }))

    def test_configured_foundation_is_not_a_material_axiom(self) -> None:
        for used in (False, True):
            with self.subTest(used=used):
                self._run_mock_assumption_recovery(self._axiom_inventory({
                    "Paper.result": {"Classical.choice"} if used else {"propext"},
                    "Classical.choice": {"Classical.choice"},
                }), assumption_names=["Classical.choice"])

    def test_missing_checked_discovery_root_fails_closed(self) -> None:
        with self.assertRaisesRegex(terminal.TerminalLeanSemanticRevalidationError,
                                    "omits a required axiom-closure root"):
            self._run_mock_assumption_recovery(self._axiom_inventory({
                "Paper.result": {"propext"}, "Paper.z": {"propext"},
            }))


if __name__ == "__main__":
    unittest.main()
