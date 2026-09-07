"""Unit coverage for the non-evidence source/interface preflight."""

from __future__ import annotations

import hashlib
import io
import json
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest.mock import patch

from scripts import draft_semantic_preflight as preflight_cli
from scripts.current_closeout import draft_semantic_preflight as preflight
from scripts.obligation_routes import RouteKind, SemanticReviewTargetKind


class _FakeProvider:
    last_entry: str | None = None

    def __init__(self, *_args: object, **_kwargs: object) -> None:
        pass

    def repository_source_snapshot(self, entry: str):
        type(self).last_entry = entry
        return [("papers.Test", Path("/repo/papers/Test.lean"), b"import Test", "0" * 64)]

    def finalize_unchanged(self) -> bool:
        return True


class _FakeRoutes:
    routes = (
        SimpleNamespace(
            route_kind=RouteKind.SOURCE_SEMANTIC_DECLARATION,
            source_item_id="model",
            semantic_declarations=("Test.Model",),
        ),
    )

    def result_specifications(self) -> tuple[str, ...]:
        return ("Test.PaperInterface.resultSpec",)

    def result_route_by_specification(self):
        return {"Test.PaperInterface.resultSpec": SimpleNamespace(source_item_id="result")}


class DraftSemanticPreflightTests(unittest.TestCase):
    def test_cli_persists_exact_stdout_only_under_ignored_trace_directory(self) -> None:
        payload = {
            "acceptance_credential": False,
            "non_evidence": True,
            "persisted": False,
            "source_result_rows": [],
        }
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Test"
            folder.mkdir(parents=True)
            destination = "papers/Test/.review_traces/draft-preflight.json"
            stdout = io.StringIO()
            with (
                patch.object(preflight_cli, "ROOT", root),
                patch.object(preflight_cli, "build_draft_semantic_preflight", return_value=payload),
                patch("sys.argv", ["draft_semantic_preflight.py", "--paper", "Test", "--output", destination]),
                redirect_stdout(stdout),
            ):
                self.assertEqual(preflight_cli.main(), 0)

            expected = '{\n  "acceptance_credential": false,\n  "non_evidence": true,\n  "persisted": false,\n  "source_result_rows": []\n}\n'
            self.assertEqual(stdout.getvalue(), expected)
            self.assertEqual((root / destination).read_text(encoding="utf-8"), expected)

    def test_cli_rejects_output_outside_ignored_trace_directory(self) -> None:
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Test"
            folder.mkdir(parents=True)
            stderr = io.StringIO()
            with (
                patch.object(preflight_cli, "ROOT", root),
                patch.object(preflight_cli, "build_draft_semantic_preflight", return_value={}),
                patch("sys.argv", ["draft_semantic_preflight.py", "--paper", "Test", "--output", "draft-preflight.json"]),
                redirect_stderr(stderr),
            ):
                self.assertEqual(preflight_cli.main(), 3)
            self.assertFalse((root / "draft-preflight.json").exists())
            self.assertIn(".review_traces", stderr.getvalue())

    def test_cli_persists_exact_refusal_stderr_to_the_ignored_trace(self) -> None:
        with TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Test"
            folder.mkdir(parents=True)
            destination = "papers/Test/.review_traces/draft-preflight.txt"
            stderr = io.StringIO()
            with (
                patch.object(preflight_cli, "ROOT", root),
                patch.object(
                    preflight_cli,
                    "build_draft_semantic_preflight",
                    side_effect=preflight_cli.DraftSemanticPreflightError("fixture refusal"),
                ),
                patch("sys.argv", ["draft_semantic_preflight.py", "--paper", "Test", "--output", destination]),
                redirect_stderr(stderr),
            ):
                self.assertEqual(preflight_cli.main(), 2)

            expected = "draft semantic preflight refused: fixture refusal\n"
            self.assertEqual(stderr.getvalue(), expected)
            self.assertEqual((root / destination).read_text(encoding="utf-8"), expected)

    def test_cli_emits_only_the_non_evidence_bundle(self) -> None:
        payload = {
            "paper": "Fixture",
            "non_evidence": True,
            "acceptance_credential": False,
        }
        output = io.StringIO()
        with (
            patch.object(preflight, "build_draft_semantic_preflight", return_value=payload)
            as build,
            patch("sys.stdout", output),
        ):
            self.assertEqual(preflight.main(["--paper", "Fixture"]), 0)

        self.assertEqual(json.loads(output.getvalue()), payload)
        self.assertEqual(build.call_args.args[1].name, "Fixture")

    def test_exposes_approved_corrected_target_to_preflight_reviewer(self) -> None:
        excerpt = "The printed denominator requires a stronger product lower bound."
        source_item = {
            "statement": "Printed source proposition.",
            "coverage_status": "corrected_source_statement",
            "source_note": "The approved correction changes only the denominator.",
            "corrected_target": {
                "statement": "Corrected proposition with the squared denominator.",
                "archival_equivalence_claimed": False,
                "archival_source_locator": "source/main.tex:12-18",
                "governing_defect_ids": ["FIXTURE-DENOMINATOR-01"],
                "approval": {
                    "kind": "documented_source_correction",
                    "recorded_at": "2026-09-02",
                    "reference": "Fixture correction memo.",
                    "artifact_protocol": "unique_normalized_artifact_excerpt_v1",
                    "artifact_excerpt": excerpt,
                    "artifact_excerpt_sha256": hashlib.sha256(
                        excerpt.encode("utf-8")
                    ).hexdigest(),
                },
            },
        }
        with (
            patch.object(preflight, "source_anchor_file_error", return_value=""),
            patch.object(
                preflight,
                "source_semantic_input_bundle",
                return_value=("verbatim source", "c" * 64, ""),
            ),
        ):
            row = preflight._review_row(
                review_id="source-result:Fixture.resultSpec",
                review_kind="source_result_spec",
                declaration="Fixture.resultSpec",
                source_item_id="result",
                source_item=source_item,
                lean_target={"display": "expanded target", "display_sha256": "a" * 64},
                folder=Path("/repo/papers/Fixture"),
                repository_root=Path("/repo"),
            )

        correction = row["approved_corrected_target"]
        self.assertEqual(
            correction["statement"],
            "Corrected proposition with the squared denominator.",
        )
        self.assertFalse(correction["archival_equivalence_claimed"])
        self.assertEqual(
            correction["approval_record"]["artifact_excerpt"], excerpt
        )

    def test_rejects_source_review_target_with_pretty_printer_elision(self) -> None:
        """A source-to-Lean comparison may not hide any displayed premise."""

        source_item = {"statement": "Printed source proposition."}
        with (
            patch.object(preflight, "source_anchor_file_error", return_value=""),
            patch.object(
                preflight,
                "source_semantic_input_bundle",
                return_value=("verbatim source", "c" * 64, ""),
            ),
            self.assertRaisesRegex(
                preflight.DraftSemanticPreflightError, "pretty-printer elision"
            ),
        ):
            preflight._review_row(
                review_id="source-result:Fixture.resultSpec",
                review_kind="source_result_spec",
                declaration="Fixture.resultSpec",
                source_item_id="result",
                source_item=source_item,
                lean_target={"display": "∀ x : Nat, ⋯ → x = x", "display_sha256": "a" * 64},
                folder=Path("/repo/papers/Fixture"),
                repository_root=Path("/repo"),
            )

    def test_retains_lean_authenticated_declaration_source_for_review(self) -> None:
        """A recursive definition is reviewable even if its type is opaque."""

        source_item = {"statement": "Printed procedure."}
        declaration_source = "def sourceProcedure := State.step"
        with (
            patch.object(preflight, "source_anchor_file_error", return_value=""),
            patch.object(
                preflight,
                "source_semantic_input_bundle",
                return_value=("verbatim source", "c" * 64, ""),
            ),
        ):
            row = preflight._review_row(
                review_id="source-declaration:Fixture.sourceProcedure:model",
                review_kind="source_model_or_definition",
                declaration="Fixture.sourceProcedure",
                source_item_id="model",
                source_item=source_item,
                lean_target={"display": "State → State", "display_sha256": "a" * 64},
                lean_declaration_source={
                    "source": declaration_source,
                    "source_sha256": hashlib.sha256(
                        declaration_source.encode("utf-8")
                    ).hexdigest(),
                    "source_module": "Fixture.PaperInterface",
                    "source_path": "papers/Fixture/PaperInterface.lean",
                    "source_range": {"line_start": 5, "line_end": 5},
                },
                folder=Path("/repo/papers/Fixture"),
                repository_root=Path("/repo"),
            )

        self.assertEqual(row["lean_exact_declaration_source"], declaration_source)
        self.assertEqual(
            row["lean_exact_declaration_source_module"], "Fixture.PaperInterface"
        )

    def test_builds_stdout_only_bundle_from_lean_owned_displays(self) -> None:
        _FakeProvider.last_entry = None
        source_map: dict[str, object] = {
            "paper_interface_namespace": "AppliedModelingLib.Example.TestPaper",
            "semantic_preflight_import_module": "Test.PaperInterface",
            "items": {
                "result": {"statement": "Result."},
                "model": {"statement": "Model."},
                "support": {"statement": "Support."},
            },
            "paper_semantic_prerequisite_sources": {
                "Test.Model": "model",
                "Test.Support": "support",
            },
        }
        surface = {
            "specification_targets": {
                "Test.PaperInterface.resultSpec": {
                    "display": "expanded result",
                    "display_sha256": "a" * 64,
                }
            },
            "paper_declaration_targets": {
                "Test.Model": {
                    "display": "expanded model",
                    "display_sha256": "b" * 64,
                },
                "Test.Support": {
                    "display": "expanded support",
                    "display_sha256": "d" * 64,
                }
            },
            "library_declaration_targets": {},
        }
        with (
            patch.object(
                preflight,
                "_draft_statement_map",
                return_value=source_map,
            ),
            patch.object(
                preflight.EvidenceRouteSet,
                "from_source_map",
                return_value=_FakeRoutes(),
            ),
            patch.object(preflight, "RepositoryBuildInputSnapshotProvider", _FakeProvider),
            patch.object(preflight, "paper_module_names_from_sources", return_value=("papers.Test",)),
            patch.object(
                preflight,
                "run_lean_paper_semantic_review_graph",
                return_value=surface,
            ) as graph,
            patch.object(preflight, "source_anchor_file_error", return_value=""),
            patch.object(
                preflight,
                "source_semantic_input_bundle",
                return_value=("verbatim source", "c" * 64, ""),
            ),
        ):
            result = preflight.build_draft_semantic_preflight(
                Path("/repo"), Path("/repo/papers/Test")
            )

        self.assertFalse(result["acceptance_credential"])
        self.assertTrue(result["non_evidence"])
        self.assertFalse(result["persisted"])
        self.assertIn(
            "needs_maintainer_clarification", result["reviewer_instruction"]
        )
        self.assertEqual(
            result["source_result_rows"][0]["lean_expanded_target"],
            "expanded result",
        )
        self.assertEqual(
            result["source_model_and_definition_rows"][0]["lean_expanded_target"],
            "expanded model",
        )
        self.assertEqual(
            result["source_model_and_definition_rows"][1]["lean_expanded_target"],
            "expanded support",
        )
        self.assertEqual(
            graph.call_args.kwargs["semantic_review_claim_declaration_names"], ()
        )
        self.assertEqual(
            set(graph.call_args.kwargs["semantic_declaration_names"]),
            {"Test.Model", "Test.Support"},
        )
        self.assertEqual(_FakeProvider.last_entry, "Test.PaperInterface")
        self.assertEqual(graph.call_args.args[1], "Test.PaperInterface")
        self.assertEqual(result["semantic_preflight_import_module"], "Test.PaperInterface")

    def test_allows_a_result_only_source_surface(self) -> None:
        routes = SimpleNamespace(routes=())
        self.assertEqual(
            preflight._source_items_by_declaration({"items": {}}, routes), ()
        )

    def test_batches_non_evidence_display_requests_without_dropping_roots(self) -> None:
        """A large preflight may bound Lean display work without changing scope."""

        specifications = tuple(
            f"Test.PaperInterface.result{index}Spec" for index in range(5)
        )
        source_map: dict[str, object] = {
            "paper_interface_namespace": "Test",
            "items": {
                f"result{index}": {"statement": f"Result {index}."}
                for index in range(5)
            },
        }
        routes = SimpleNamespace(
            routes=(),
            result_specifications=lambda: specifications,
            result_route_by_specification=lambda: {
                specification: SimpleNamespace(source_item_id=f"result{index}")
                for index, specification in enumerate(specifications)
            },
        )

        def bounded_surface(*_args: object, **kwargs: object) -> dict[str, object]:
            batch = tuple(kwargs["specification_names"])
            return {
                "specification_targets": {
                    specification: {
                        "display": f"expanded {specification}",
                        "display_sha256": "a" * 64,
                    }
                    for specification in batch
                },
                "paper_declaration_targets": {
                    "Test.schedule": {
                        "display": "type: Nat → Nat\nvalue: fun n => n + 1",
                        "display_sha256": "d" * 64,
                        "direct_paper_declarations": list(batch),
                    },
                },
                "library_declaration_targets": {
                    "Fixture.samplingLaw": {
                        "display": "type: Nat → Prop\nvalue: fun n => n > 0",
                        "display_sha256": "e" * 64,
                        "elaborated_signature_sha256": "f" * 64,
                        "review_owner_declaration": "Fixture.samplingLaw",
                        "source_module": "Fixture.Model",
                        "source_line_start": 10,
                        "source_column_start": 0,
                        "source_line_end": 12,
                        "source_column_end": 5,
                        "direct_library_declarations": list(batch),
                        "erased_proof_declarations": list(batch),
                    },
                },
            }

        with (
            patch.object(preflight, "_draft_statement_map", return_value=source_map),
            patch.object(preflight.EvidenceRouteSet, "from_source_map", return_value=routes),
            patch.object(preflight, "RepositoryBuildInputSnapshotProvider", _FakeProvider),
            patch.object(preflight, "paper_module_names_from_sources", return_value=("papers.Test",)),
            patch.object(
                preflight,
                "run_lean_paper_semantic_review_graph",
                side_effect=bounded_surface,
            ) as graph,
            patch.object(preflight, "source_anchor_file_error", return_value=""),
            patch.object(
                preflight,
                "source_semantic_input_bundle",
                return_value=("verbatim source", "c" * 64, ""),
            ),
        ):
            result = preflight.build_draft_semantic_preflight(
                Path("/repo"), Path("/repo/papers/Test")
            )

        self.assertEqual(len(graph.call_args_list), 2)
        self.assertEqual(
            tuple(graph.call_args_list[0].kwargs["specification_names"]),
            specifications[:4],
        )
        self.assertEqual(
            tuple(graph.call_args_list[1].kwargs["specification_names"]),
            specifications[4:],
        )
        self.assertTrue(graph.call_args_list[0].kwargs["require_build"])
        self.assertFalse(graph.call_args_list[1].kwargs["require_build"])
        self.assertEqual(
            [row["declaration"] for row in result["source_result_rows"]],
            list(specifications),
        )
        self.assertEqual(result["source_model_and_definition_rows"], [])
        support = result["lean_dependency_support"]
        self.assertEqual(set(support["paper_declarations"]), {"Test.schedule"})
        self.assertEqual(set(support["library_declarations"]), {"Fixture.samplingLaw"})
        self.assertEqual(
            support["paper_declarations"]["Test.schedule"]["display"],
            "type: Nat → Nat\nvalue: fun n => n + 1",
        )
        self.assertNotIn(
            "direct_paper_declarations", support["paper_declarations"]["Test.schedule"]
        )
        self.assertNotIn(
            "erased_proof_declarations", support["library_declarations"]["Fixture.samplingLaw"]
        )
        library_support = support["library_declarations"]["Fixture.samplingLaw"]
        self.assertNotIn("direct_library_declarations", library_support)
        self.assertEqual(library_support["elaborated_signature_sha256"], "f" * 64)
        self.assertEqual(library_support["review_owner_declaration"], "Fixture.samplingLaw")
        self.assertEqual(library_support["source_module"], "Fixture.Model")
        self.assertEqual(
            [library_support[key] for key in (
                "source_line_start", "source_column_start", "source_line_end", "source_column_end"
            )],
            [10, 0, 12, 5],
        )
        self.assertTrue(result["non_evidence"])
        self.assertFalse(result["acceptance_credential"])

    def test_dependency_seen_before_its_explicit_batch_remains_one_source_root(self) -> None:
        specifications = tuple(f"Test.result{i}Spec" for i in range(5))
        target = {"display": "complete model", "display_sha256": "b" * 64}

        def surface(*_args: object, **kwargs: object) -> dict[str, object]:
            return {
                "specification_targets": {
                    name: {"display": name, "display_sha256": "a" * 64}
                    for name in kwargs["specification_names"]
                },
                "paper_declaration_targets": {"Test.Model": target},
                "library_declaration_targets": {},
            }

        with patch.object(preflight, "run_lean_paper_semantic_review_graph", side_effect=surface):
            result = preflight._run_bounded_draft_display_surface(
                root=Path("/repo"), entry_module="Test", specifications=specifications,
                declarations=("Test.Model",), paper_modules=("Test",), provider=_FakeProvider(),
            )
        self.assertEqual(result["paper_declaration_targets"], {"Test.Model": target})
        self.assertEqual(result["paper_dependency_support"], {})

    def test_rejects_dependency_semantic_or_owner_conflicts_across_batches(self) -> None:
        specifications = tuple(f"Test.result{i}Spec" for i in range(5))
        for changed_field, changed_value in (
            ("display", "different model"),
            ("display_sha256", "c" * 64),
            ("source_line_start", 99),
            ("elaborated_signature_sha256", "c" * 64),
            ("elaborated_signature_sha256", None),
            ("owner", "paper"),
        ):
            with self.subTest(changed_field=changed_field):
                calls = 0

                def surface(*_args: object, **kwargs: object) -> dict[str, object]:
                    nonlocal calls
                    calls += 1
                    target = {
                        "display": "complete model", "display_sha256": "b" * 64,
                        "elaborated_signature_sha256": "d" * 64,
                        "source_line_start": 1,
                    }
                    if calls > 1 and changed_field != "owner":
                        if changed_value is None:
                            target.pop(changed_field)
                        else:
                            target[changed_field] = changed_value
                    library_owner = not (calls > 1 and changed_field == "owner")
                    return {
                        "specification_targets": {
                            name: {"display": name, "display_sha256": "a" * 64}
                            for name in kwargs["specification_names"]
                        },
                        "paper_declaration_targets": {} if library_owner else {"Test.Model": target},
                        "library_declaration_targets": {"Test.Model": target} if library_owner else {},
                    }

                with patch.object(preflight, "run_lean_paper_semantic_review_graph", side_effect=surface):
                    with self.assertRaises(preflight.DraftSemanticPreflightError):
                        preflight._run_bounded_draft_display_surface(
                            root=Path("/repo"), entry_module="Test", specifications=specifications,
                            declarations=(), paper_modules=("Test",), provider=_FakeProvider(),
                        )

    def test_uses_definition_target_for_a_source_definition(self) -> None:
        source_map: dict[str, object] = {
            "paper_interface_namespace": "Test",
            "items": {"definition": {"statement": "Definition."}},
        }
        definition = "Test.PaperInterface.sourceDefinitionSpec"
        route = SimpleNamespace(
            source_item_id="definition",
            semantic_review_target_kind=(
                SemanticReviewTargetKind.DEFINITION_DECLARATION
            ),
            semantic_review_declaration=definition,
        )
        routes = SimpleNamespace(
            routes=(),
            result_specifications=lambda: (definition,),
            result_route_by_specification=lambda: {definition: route},
        )
        surface = {
            "specification_targets": {
                definition: {"display": "wrapper", "display_sha256": "a" * 64}
            },
            "paper_declaration_targets": {
                definition: {
                    "display": "expanded definition",
                    "display_sha256": "b" * 64,
                }
            },
            "library_declaration_targets": {},
        }
        with (
            patch.object(preflight, "_draft_statement_map", return_value=source_map),
            patch.object(preflight.EvidenceRouteSet, "from_source_map", return_value=routes),
            patch.object(preflight, "RepositoryBuildInputSnapshotProvider", _FakeProvider),
            patch.object(preflight, "paper_module_names_from_sources", return_value=("papers.Test",)),
            patch.object(preflight, "run_lean_paper_semantic_review_graph", return_value=surface) as graph,
            patch.object(preflight, "source_anchor_file_error", return_value=""),
            patch.object(
                preflight,
                "source_semantic_input_bundle",
                return_value=("verbatim source", "c" * 64, ""),
            ),
        ):
            result = preflight.build_draft_semantic_preflight(
                Path("/repo"), Path("/repo/papers/Test")
            )

        self.assertEqual(
            result["source_result_rows"][0]["lean_expanded_target"],
            "expanded definition",
        )
        self.assertEqual(
            graph.call_args.kwargs["semantic_declaration_names"], (definition,)
        )

    def test_preserves_multiple_source_conditions_for_one_declaration(self) -> None:
        source_map: dict[str, object] = {
            "items": {
                "condition_a": {"statement": "Condition A."},
                "condition_b": {"statement": "Condition B."},
            }
        }
        routes = SimpleNamespace(
            routes=(
                SimpleNamespace(
                    route_kind=RouteKind.SOURCE_SEMANTIC_DECLARATION,
                    source_item_id="condition_a",
                    semantic_declarations=("Test.Model",),
                ),
                SimpleNamespace(
                    route_kind=RouteKind.SOURCE_SEMANTIC_DECLARATION,
                    source_item_id="condition_b",
                    semantic_declarations=("Test.Model",),
                ),
            )
        )
        self.assertEqual(
            preflight._source_items_by_declaration(source_map, routes),
            (
                ("Test.Model", "condition_a", source_map["items"]["condition_a"]),
                ("Test.Model", "condition_b", source_map["items"]["condition_b"]),
            ),
        )

    def test_reads_library_target_for_a_routed_source_condition(self) -> None:
        source_map: dict[str, object] = {
            "paper_interface_namespace": "Test",
            "items": {
                "result": {"statement": "Result."},
                "library_model": {"statement": "Library model."},
            },
        }
        routes = _FakeRoutes()
        routes.routes = (
            SimpleNamespace(
                route_kind=RouteKind.SOURCE_SEMANTIC_DECLARATION,
                source_item_id="library_model",
                semantic_declarations=("Fixture.LibraryModel",),
            ),
        )
        surface = {
            "specification_targets": {
                "Test.PaperInterface.resultSpec": {
                    "display": "expanded result",
                    "display_sha256": "a" * 64,
                }
            },
            "paper_declaration_targets": {},
            "library_declaration_targets": {
                "Fixture.LibraryModel": {
                    "display": "library signature and code",
                    "display_sha256": "b" * 64,
                }
            },
        }
        with (
            patch.object(preflight, "_draft_statement_map", return_value=source_map),
            patch.object(preflight.EvidenceRouteSet, "from_source_map", return_value=routes),
            patch.object(preflight, "RepositoryBuildInputSnapshotProvider", _FakeProvider),
            patch.object(preflight, "paper_module_names_from_sources", return_value=("papers.Test",)),
            patch.object(preflight, "run_lean_paper_semantic_review_graph", return_value=surface),
            patch.object(preflight, "source_anchor_file_error", return_value=""),
            patch.object(
                preflight,
                "source_semantic_input_bundle",
                return_value=("verbatim source", "c" * 64, ""),
            ),
        ):
            result = preflight.build_draft_semantic_preflight(
                Path("/repo"), Path("/repo/papers/Test")
            )

        row = result["source_model_and_definition_rows"][0]
        self.assertEqual(row["declaration"], "Fixture.LibraryModel")
        self.assertEqual(row["lean_expanded_target"], "library signature and code")


if __name__ == "__main__":
    unittest.main()
