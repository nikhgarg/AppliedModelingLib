from __future__ import annotations

import hashlib
import json
import re
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import closeout_document_gates as document_gates
from scripts import human_review_packet_renderer as renderer
from scripts import review_dashboard
from scripts import review_dashboard_packet as packet
from scripts.current_closeout import review_surface as review_surface_owner
from scripts.report_context_presentation import (
    ReportContextPresentation,
    row_context_presentation,
)


class ReviewDashboardPacketTests(unittest.TestCase):
    def _source_card_fixture(self, *, source_changed: bool = True) -> SimpleNamespace:
        """Keep source bundling, authority selection and verdict binding real."""

        stack = ExitStack()
        self.addCleanup(stack.close)
        root = Path(stack.enter_context(tempfile.TemporaryDirectory()))
        folder = root / "papers" / "Fixture"
        (folder / "audit").mkdir(parents=True)
        spec = "Fixture.claimSpec"

        def anchor(text: str) -> dict:
            return {"path": "source.tex", "line_start": 1, "line_end": 1,
                    "quoted_text": text,
                    "quoted_text_sha256": hashlib.sha256(text.encode()).hexdigest()}

        record = {
            "source_kind": "theorem", "source_location": "source.tex:1",
            "source_anchor_evidence": [anchor("The source claim.")],
            "semantic_contract": {"spec_declaration": spec,
                                  "evidence_declaration": "Fixture.claim",
                                  "evidence_mode": "proves", "semantic_shape": "plain"},
        }
        _old_text, old_digest, error = review_dashboard.source_semantic_input_bundle(
            record, require_context_roles=True
        )
        self.assertFalse(error)
        if source_changed:
            record["semantic_context_requirements"] = [{
                "semantic_role": "definition",
                "source_anchor_evidence": [anchor("The source model definition.")],
            }]
        source_text, source_digest, error = review_dashboard.source_semantic_input_bundle(
            record, require_context_roles=True
        )
        self.assertFalse(error)
        source_map = {"paper": "Fixture", "semantic_route_schema": 2,
                      "semantic_contract_schema": 1, "items": {"claim": record}}
        atoms = [{"ref": "result", "role": "conclusion",
                  "canonical": {"tag": "const", "name": "True"}, "display": "True"}]
        atom_digest = hashlib.sha256(json.dumps(
            {"schema": 1, "atoms": [{key: value for key, value in atoms[0].items()
                                      if key != "display"}]},
            ensure_ascii=True, sort_keys=True, separators=(",", ":"),
        ).encode()).hexdigest()
        target = {"display": "True", "display_sha256": hashlib.sha256(b"True").hexdigest(),
                  "review_claim_manifest_sha256": "b" * 64,
                  "review_claim_atoms_sha256": atom_digest, "review_claim_atoms": atoms}
        cache = {
            "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA, "paper": "Fixture",
            "specifications": [spec], "display_protocols": review_surface_owner._current_packet_display_protocols(),
            "semantic_targets": {spec: target}, "paper_prerequisite_targets": {},
            "paper_prerequisite_supporting_declarations_sha256": {},
            "library_semantic_targets": {}, "library_declaration_sources": {},
            "library_semantic_target_errors": {},
        }
        projection = SimpleNamespace(
            graph_sha256="f" * 64, reviewed_display_surface_complete=True,
            claim_semantic_target_sha256s_by_specification={spec: target["display_sha256"]},
            prerequisite_semantic_target_sha256s_by_declaration={},
            review_declarations_by_source_item={"claim": (spec,)},
            card_review_declarations_by_source_item={"claim": (spec,)},
            source_lean_verdicts_by_source_item={"claim": "matches"},
            source_input_bundle_sha256s_by_source_item={"claim": old_digest},
        )
        screening = {
            "schema": review_surface_owner.V11_SCREENING_SCHEMA, "paper": "Fixture",
            "prompt_version": review_surface_owner.V11_SCREENING_PROMPT_VERSION,
            "validator": "independent reviewer", "validated_at": "2026-09-05T00:00:00Z",
            "items": {spec: {
                "judgment": "matches", "reason": "The displayed source and target agree.",
                "source_input_bundle_sha256": source_digest,
                "paper_statement_sha256": review_dashboard.statement_digest(source_text),
                "lean_expanded_statement_sha256": target["display_sha256"],
                "review_claim_manifest_sha256": target["review_claim_manifest_sha256"],
                "review_claim_atoms_sha256": atom_digest, "source_review_target_sha256": "d" * 64,
                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                "lean_target_protocol": packet.V11_LEAN_TARGET_PROTOCOL,
                "semantic_target_declaration": spec,
            }},
        }
        for name, payload in (
            (review_surface_owner.SOURCE_MAP_NAME, source_map), (review_surface_owner.PACKET_LEAN_CACHE_NAME, cache),
            (review_surface_owner.V11_SCREENING_NAME, screening),
            ("status.json", {"review_surface": {"require_source_spec_correspondence": True}}),
        ):
            (folder / name).write_text(json.dumps(payload), encoding="utf-8")
        stack.enter_context(mock.patch.object(packet, "ROOT", root))
        stack.enter_context(mock.patch.object(review_surface_owner, "ROOT", root))
        stack.enter_context(mock.patch.object(review_surface_owner, "_recorded_graph_packet_projection",
                                           return_value=(True, projection)))
        current_loader = stack.enter_context(mock.patch(
            "scripts.current_closeout.review_surface.load_current_v11_review_graph_projection",
            return_value=SimpleNamespace(
                context=SimpleNamespace(statement_map=source_map),
                semantic_targets=cache["semantic_targets"], paper_prerequisite_targets={},
                library_semantic_targets={}, library_declaration_sources={},
                library_semantic_target_errors={},
            ),
        ))
        return SimpleNamespace(folder=folder, source_map=source_map, projection=projection,
                               current_loader=current_loader, screening=screening,
                               spec=spec, source_digest=source_digest, old_digest=old_digest)

    def test_prepared_surface_uses_current_transaction_after_source_only_reissue(self) -> None:
        fixture = self._source_card_fixture()
        prepared = review_surface_owner.prepared_review_surface("Fixture")
        row = prepared.claim_rows[0][0]
        self.assertEqual(prepared.presentation_authority, "current_v11_graph")
        self.assertIsNone(prepared.recorded_graph_projection)
        self.assertTrue(row["llm_match_current"])
        self.assertEqual(row["llm_match_source"], Path(review_surface_owner.V11_SCREENING_NAME).name)
        self.assertEqual(row["source_input_bundle_sha256"], fixture.source_digest)
        self.assertIn("The source model definition.", row["verbatim_source_input"])
        fixture.current_loader.assert_called_once()

    def test_source_only_drift_without_exact_current_graph_fails_closed(self) -> None:
        fixture = self._source_card_fixture()
        fixture.current_loader.return_value = None
        with self.assertRaisesRegex(ValueError, "packet Lean displays are not cached"):
            review_surface_owner.prepared_review_surface("Fixture")

    def test_prepared_prerequisite_cards_reuse_selected_graph_source_coordinates(self) -> None:
        fixture = self._source_card_fixture()
        name = "Fixture.model"
        target = {"display": "Nat", "display_sha256": hashlib.sha256(b"Nat").hexdigest()}
        cache_path = fixture.folder / review_surface_owner.PACKET_LEAN_CACHE_NAME
        cache = json.loads(cache_path.read_text(encoding="utf-8"))
        cache["paper_prerequisite_targets"] = {name: target}
        cache["paper_prerequisite_supporting_declarations_sha256"] = {name: ""}
        cache_path.write_text(json.dumps(cache), encoding="utf-8")
        current = fixture.current_loader.return_value
        current.paper_prerequisite_targets = {name: target}
        current.paper_declaration_sources = {name: {"path": "Saved.lean", "line": 7}}
        with mock.patch.object(
            review_surface_owner,
            "_prepared_paper_prerequisites",
            return_value=[],
        ) as prepare:
            prepared = review_surface_owner.prepared_review_surface("Fixture")
        self.assertEqual(prepared.presentation_authority, "current_v11_graph")
        self.assertIs(prepare.call_args.kwargs["declaration_sources_override"],
                      current.paper_declaration_sources)
        fixture.current_loader.assert_called_once()

    def test_prepared_surface_projects_full_current_graph_governing_closure(self) -> None:
        fixture = self._source_card_fixture()

        def target(display: str, **extra: object) -> dict[str, object]:
            return {
                "display": display,
                "display_sha256": hashlib.sha256(display.encode()).hexdigest(),
                **extra,
            }

        paper_root = "Fixture.paperModel"
        paper_base = "Fixture.paperBase"
        library_root = "AppliedModelingLib.Shared.Root"
        library_base = "AppliedModelingLib.Shared.Base"
        paper_targets = {
            paper_root: target(
                "def paperModel := paperBase",
                declaration_kind="definition",
                direct_paper_declarations=[paper_base],
                direct_library_declarations=[library_base],
            ),
            paper_base: target(
                "def paperBase : Prop := True",
                declaration_kind="definition",
                direct_paper_declarations=[],
                direct_library_declarations=[],
            ),
        }
        library_targets = {
            library_root: target(
                "def Root := Base",
                declaration_kind="definition",
                direct_library_declarations=[library_base],
            ),
            library_base: target(
                "def Base : Prop := True",
                declaration_kind="definition",
                direct_library_declarations=[],
            ),
        }
        cache_path = fixture.folder / review_surface_owner.PACKET_LEAN_CACHE_NAME
        cache = json.loads(cache_path.read_text(encoding="utf-8"))
        cache["paper_prerequisite_targets"] = paper_targets
        cache["paper_prerequisite_supporting_declarations_sha256"] = {
            name: "" for name in paper_targets
        }
        # No declaration in this closure is a separately selected semantic
        # prerequisite row.  The full library closure is carried by the
        # authenticated current graph, outside the selected cache frontier.
        cache["paper_semantic_review_targets"] = {}
        cache["paper_semantic_review_supporting_declarations_sha256"] = {}
        cache_path.write_text(json.dumps(cache), encoding="utf-8")
        current = fixture.current_loader.return_value
        # Root edges come only from the authenticated graph.  The cache has
        # the same display digest but deliberately omits both root lists.
        current.semantic_targets = json.loads(json.dumps(cache["semantic_targets"]))
        current.semantic_targets[fixture.spec].update(
            prerequisite_declarations=[paper_root],
            library_declarations=[library_root],
        )
        current.paper_prerequisite_targets = paper_targets
        current.paper_declaration_sources = {}
        current.library_semantic_targets = library_targets
        current.library_declaration_sources = {
            name: {} for name in library_targets
        }

        prepared = review_surface_owner.prepared_review_surface("Fixture")

        self.assertEqual(prepared.paper_prerequisites, ())
        self.assertEqual(prepared.library_prerequisites, ())
        self.assertEqual(
            {entry["lean_name"] for entry in prepared.governing_declarations},
            {paper_root, paper_base, library_root, library_base},
        )
        self.assertEqual(
            prepared.governing_declarations[0]["lean_name"], library_base
        )
        self.assertEqual(
            prepared.claim_rows[0][0]["governing_declaration_links"],
            [
                {"lean_name": library_root, "anchor_kind": "governing-declaration"},
                {"lean_name": paper_root, "anchor_kind": "governing-declaration"},
            ],
        )

    def test_source_only_drift_cannot_reuse_stale_screening_verdict(self) -> None:
        fixture = self._source_card_fixture()
        fixture.screening["items"][fixture.spec]["source_input_bundle_sha256"] = fixture.old_digest
        (fixture.folder / review_surface_owner.V11_SCREENING_NAME).write_text(
            json.dumps(fixture.screening), encoding="utf-8"
        )
        prepared = review_surface_owner.prepared_review_surface("Fixture")
        self.assertEqual(prepared.presentation_authority, "current_v11_graph")
        self.assertFalse(prepared.claim_rows[0][0]["llm_match_current"])
        self.assertEqual(prepared.claim_rows[0][0]["llm_match_judgment"], "not recorded")

    def test_current_graph_supersedes_older_accepted_cards_when_available(self) -> None:
        fixture = self._source_card_fixture(source_changed=False)
        prepared = review_surface_owner.prepared_review_surface("Fixture")
        self.assertEqual(prepared.presentation_authority, "current_v11_graph")
        self.assertEqual(
            prepared.claim_rows[0][0]["llm_match_source"],
            Path(review_surface_owner.V11_SCREENING_NAME).name,
        )
        fixture.current_loader.assert_called_once()

    def test_unchanged_source_cards_keep_accepted_fallback_without_current_graph(
        self,
    ) -> None:
        fixture = self._source_card_fixture(source_changed=False)
        fixture.current_loader.return_value = None
        with mock.patch.object(
            review_surface_owner,
            "bind_current_v11_source_spec_screening",
            side_effect=AssertionError("recorded cards read screening"),
        ):
            prepared = review_surface_owner.prepared_review_surface("Fixture")
        self.assertEqual(prepared.presentation_authority, "accepted_graph")
        self.assertEqual(
            prepared.claim_rows[0][0]["llm_match_source"],
            "accepted obligation graph",
        )
        self.assertEqual(prepared.governing_declarations, ())

    def test_historical_display_reader_cannot_bypass_changed_source_cards(self) -> None:
        fixture = self._source_card_fixture()
        fixture.projection.reviewed_display_surface_complete = False
        with mock.patch.object(review_surface_owner, "current_dashboard_semantic_reuse_authority",
                               side_effect=AssertionError("stale source selected historical reader")):
            prepared = review_surface_owner.prepared_review_surface("Fixture")
        self.assertEqual(prepared.presentation_authority, "current_v11_graph")

    def test_packet_currentness_passes_source_context_to_shared_selection(self) -> None:
        fixture = self._source_card_fixture()
        with (
            mock.patch.object(review_surface_owner, "_current_packet_lean_cache_selection",
                              wraps=review_surface_owner._current_packet_lean_cache_selection) as select,
            mock.patch.object(document_gates, "packet_lean_cache_missing_stages", return_value=()),
        ):
            document_gates.current_human_review_packet_errors(fixture.folder)
        self.assertEqual(select.call_args.kwargs["source_map"], fixture.source_map)

    def test_current_graph_packet_currentness_skips_unrelated_legacy_stages(self) -> None:
        fixture = self._source_card_fixture()
        docs = fixture.folder / "docs"
        docs.mkdir()
        (docs / f"{packet.PACKET_NAME}.tex").write_text("Current packet\n", encoding="utf-8")
        (docs / f"{packet.PACKET_NAME}.pdf").write_bytes(b"%PDF-fixture\n")
        with (
            mock.patch.object(document_gates, "packet_lean_cache_missing_stages",
                              side_effect=AssertionError("current graph reentered legacy staging")),
            mock.patch.object(document_gates, "render_packet", return_value="Current packet\n") as render,
        ):
            self.assertEqual(document_gates.current_human_review_packet_errors(fixture.folder), ())
            render.assert_called_once()
            self.assertEqual(render.call_args.args[0].paper_dir, fixture.folder)
            render.side_effect = ValueError("current source or screening binding failed")
            errors = document_gates.current_human_review_packet_errors(fixture.folder)
        self.assertTrue(any("current source or screening binding failed" in error for error in errors))

    def test_packet_currentness_retains_staging_checks_without_exact_graph_authority(self) -> None:
        fixture = self._source_card_fixture()
        for authority in (None, "accepted_graph_historical_display_reader"):
            selection = None if authority is None else review_surface_owner._PacketLeanCacheSelection(
                payload={}, authority=authority, recorded_graph_projection=fixture.projection
            )
            with (
                self.subTest(authority=authority),
                mock.patch.object(
                    document_gates, "prepared_review_surface",
                    side_effect=ValueError("missing saved surface") if selection is None else None,
                    return_value=SimpleNamespace(presentation_authority=authority),
                ),
                mock.patch.object(document_gates, "packet_lean_cache_missing_stages",
                                  return_value=("specifications",)) as stages,
            ):
                errors = document_gates.current_human_review_packet_errors(fixture.folder)
            stages.assert_called_once_with(fixture.folder, fixture.source_map)
            self.assertTrue(any("missing specifications" in error for error in errors))

    def test_source_only_drift_preserves_display_only_cache_reuse(self) -> None:
        fixture = self._source_card_fixture()
        fixture.current_loader.side_effect = AssertionError("display reuse loaded current graph")
        self.assertIsNotNone(review_surface_owner._current_packet_lean_cache(fixture.folder, [fixture.spec]))
        fixture.current_loader.assert_not_called()

    def test_source_only_drift_still_requires_exact_current_lean_displays(self) -> None:
        fixture = self._source_card_fixture(source_changed=False)
        fixture.current_loader.return_value.semantic_targets = {
            fixture.spec: {"display": "False", "display_sha256": hashlib.sha256(b"False").hexdigest()}
        }
        with self.assertRaisesRegex(ValueError, "packet Lean displays are not cached"):
            review_surface_owner.prepared_review_surface("Fixture")

    def test_current_packet_preflight_compares_committed_tex_to_saved_graph_surface(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            docs = paper_dir / "docs"
            audit = paper_dir / "audit"
            docs.mkdir(parents=True)
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                '{"items": {}}\n', encoding="utf-8"
            )
            (audit / "human_review_packet_lean_cache.json").write_text(
                "{}\n", encoding="utf-8"
            )
            tex_path = docs / "HUMAN_REVIEW_PACKET.tex"
            tex_path.write_text("stale\n", encoding="utf-8")
            (docs / "HUMAN_REVIEW_PACKET.pdf").write_bytes(b"%PDF-fixture\n")
            with (
                mock.patch.object(document_gates, "prepared_review_surface",
                                  return_value=SimpleNamespace(presentation_authority="accepted_graph")),
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    document_gates, "packet_lean_cache_missing_stages", return_value=()
                ),
                mock.patch.object(document_gates, "render_packet", return_value="current\n"),
            ):
                stale = document_gates.current_human_review_packet_errors(paper_dir)
                tex_path.write_text("current\n", encoding="utf-8")
                current = document_gates.current_human_review_packet_errors(paper_dir)

        self.assertTrue(any("stale relative" in error for error in stale), stale)
        self.assertEqual(current, ())

    def test_current_packet_preflight_ignores_only_generated_date(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            docs = paper_dir / "docs"
            audit = paper_dir / "audit"
            docs.mkdir(parents=True)
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                '{"items": {}}\n', encoding="utf-8"
            )
            (audit / "human_review_packet_lean_cache.json").write_text(
                "{}\n", encoding="utf-8"
            )
            (docs / "HUMAN_REVIEW_PACKET.pdf").write_bytes(b"%PDF-fixture\n")
            (docs / "HUMAN_REVIEW_PACKET.tex").write_text(
                "header\n\\textbf{Generated:} 2026-08-31\\\\\nbody\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(document_gates, "prepared_review_surface",
                                  return_value=SimpleNamespace(presentation_authority="accepted_graph")),
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    document_gates, "packet_lean_cache_missing_stages", return_value=()
                ),
                mock.patch.object(
                    document_gates,
                    "render_packet",
                    return_value=(
                        "header\n\\textbf{Generated:} 2026-09-01\\\\\nbody\n"
                    ),
                ),
            ):
                errors = document_gates.current_human_review_packet_errors(paper_dir)

        self.assertEqual(errors, ())

    def test_current_graph_packet_can_precede_replacement_of_old_accepted_graph(
        self,
    ) -> None:
        spec = "Fixture.claimSpec"
        display_sha256 = hashlib.sha256(b"True").hexdigest()
        payload = {
            "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
            "paper": "Fixture",
            "specifications": [spec],
            "semantic_targets": {
                spec: {"display": "True", "display_sha256": display_sha256}
            },
            "paper_prerequisite_targets": {},
            "library_semantic_targets": {},
            "library_declaration_sources": {},
            "library_semantic_target_errors": {},
        }
        old_projection = SimpleNamespace(
            reviewed_display_surface_complete=True,
            claim_semantic_target_sha256s_by_specification={spec: "0" * 64},
            prerequisite_semantic_target_sha256s_by_declaration={},
        )
        current_projection = SimpleNamespace(
            semantic_targets={
                spec: {"display": "True", "display_sha256": display_sha256}
            },
            paper_prerequisite_targets={},
            library_semantic_targets={},
            library_declaration_sources={},
            library_semantic_target_errors={},
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            cache_path = paper_dir / review_surface_owner.PACKET_LEAN_CACHE_NAME
            cache_path.parent.mkdir(parents=True)
            cache_path.write_text(json.dumps(payload), encoding="utf-8")
            with (
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    review_surface_owner,
                    "_recorded_graph_packet_projection",
                    return_value=(True, old_projection),
                ),
                mock.patch.object(
                    review_surface_owner, "_packet_cache_display_integrity", return_value=True
                ),
                mock.patch(
                    "scripts.current_closeout.review_surface."
                    "load_current_v11_review_graph_projection",
                    return_value=current_projection,
                ),
            ):
                selected = review_surface_owner._current_packet_lean_cache_selection(
                    paper_dir, [spec]
                )

        self.assertIsNotNone(selected)
        assert selected is not None
        self.assertEqual(selected.authority, "current_v11_graph")
        self.assertIsNone(selected.recorded_graph_projection)

    def test_current_v11_packet_cache_uses_selected_library_frontier(self) -> None:
        spec = "Fixture.claimSpec"
        claim_display = "True"
        claim_sha256 = hashlib.sha256(claim_display.encode("utf-8")).hexdigest()
        library_display = "def sourceRoot : Prop := True"
        library_sha256 = hashlib.sha256(
            library_display.encode("utf-8")
        ).hexdigest()
        payload = {
            "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
            "paper": "Fixture",
            "specifications": [spec],
            "semantic_targets": {
                spec: {
                    "display": claim_display,
                    "display_sha256": claim_sha256,
                }
            },
            "paper_prerequisite_targets": {},
            "library_semantic_targets": {
                "AppliedModelingLib.SourceRoot": {
                    "display": library_display,
                    "display_sha256": library_sha256,
                }
            },
            "library_declaration_sources": {
                "AppliedModelingLib.SourceRoot": {
                    "library_definition": "def sourceRoot : Prop := True",
                    "library_definition_sha256": hashlib.sha256(
                        b"def sourceRoot : Prop := True"
                    ).hexdigest(),
                    "library_definition_error": "",
                    "library_source_path": "AppliedModelingLib/SourceRoot.lean",
                    "library_line_start": 1,
                    "library_line_end": 1,
                }
            },
            "library_semantic_target_errors": {},
        }
        projection = SimpleNamespace(
            context=SimpleNamespace(statement_map={"items": {}}),
            semantic_targets=payload["semantic_targets"],
            paper_prerequisite_targets={},
            library_semantic_targets={
                "AppliedModelingLib.SourceRoot": payload[
                    "library_semantic_targets"
                ]["AppliedModelingLib.SourceRoot"],
                "AppliedModelingLib.ProofOnlyHelper": {
                    "display": "def helper : Prop := True",
                    "display_sha256": hashlib.sha256(
                        b"def helper : Prop := True"
                    ).hexdigest(),
                },
            },
            library_declaration_sources={
                "AppliedModelingLib.SourceRoot": payload[
                    "library_declaration_sources"
                ]["AppliedModelingLib.SourceRoot"],
                "AppliedModelingLib.ProofOnlyHelper": {
                    "library_definition": "def helper : Prop := True",
                    "library_definition_sha256": hashlib.sha256(
                        b"def helper : Prop := True"
                    ).hexdigest(),
                    "library_definition_error": "",
                    "library_source_path": "AppliedModelingLib/Helper.lean",
                    "library_line_start": 1,
                    "library_line_end": 1,
                },
            },
            library_semantic_target_errors={},
        )
        with (
            mock.patch.object(review_surface_owner, "_packet_cache_display_integrity", return_value=True),
            mock.patch.object(
                review_surface_owner,
                "selected_library_semantic_prerequisite_targets",
                return_value=payload["library_semantic_targets"],
            ),
        ):
            self.assertTrue(
                review_surface_owner._current_v11_graph_packet_cache_current(
                    payload,
                    [spec],
                    projection,
                )
            )
            payload_without_sources = dict(payload)
            payload_without_sources.pop("library_declaration_sources")
            self.assertFalse(
                review_surface_owner._current_v11_graph_packet_cache_current(
                    payload_without_sources,
                    [spec],
                    projection,
                )
            )
            payload_with_changed_source = json.loads(json.dumps(payload))
            payload_with_changed_source["library_declaration_sources"][
                "AppliedModelingLib.SourceRoot"
            ]["library_definition"] = "def sourceRoot : Prop := False"
            self.assertFalse(
                review_surface_owner._current_v11_graph_packet_cache_current(
                    payload_with_changed_source,
                    [spec],
                    projection,
                )
            )

    def test_current_v11_graph_materializes_complete_packet_without_lean(self) -> None:
        projection = SimpleNamespace(
            context=SimpleNamespace(statement_map={"items": {}}),
            semantic_targets={"Fixture.claimSpec": {"display": "True"}},
            paper_prerequisite_targets={"Fixture.Model": {"display": "Prop"}},
            paper_prerequisite_review_support=lambda _roots: (
                {},
                {},
                {"Fixture.Model": ""},
            ),
            library_semantic_targets={"AppliedModelingLib.Shared": {"display": "Prop"}},
            library_declaration_sources={"AppliedModelingLib.Shared": {"source": "exact"}},
            library_semantic_target_errors={},
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            expected = paper_dir / review_surface_owner.PACKET_LEAN_CACHE_NAME
            with (
                mock.patch(
                    "scripts.current_closeout.review_surface."
                    "load_current_v11_review_graph_projection",
                    return_value=projection,
                ) as load_graph,
                mock.patch.object(
                    packet,
                    "raw_source_spec_screening_requested",
                    return_value=True,
                ),
                mock.patch.object(
                    packet,
                    "write_packet_lean_cache_from_elaborated_graph",
                    return_value=expected,
                ) as write_graph,
            ):
                observed = packet.write_packet_lean_cache_from_current_v11_graph(
                    paper_dir,
                    repository_root=root,
                )

        self.assertEqual(observed, expected)
        load_graph.assert_called_once_with(root, paper_dir)
        write_graph.assert_called_once_with(
            paper_dir,
            semantic_targets=projection.semantic_targets,
            paper_prerequisite_targets=projection.paper_prerequisite_targets,
            paper_prerequisite_supporting_declarations_sha256={
                "Fixture.Model": ""
            },
            library_semantic_targets=projection.library_semantic_targets,
            library_declaration_sources=projection.library_declaration_sources,
            library_semantic_target_errors={},
        )

    def test_selected_v11_packet_requires_graph_instead_of_replaying_lean(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            with (
                mock.patch.object(
                    packet,
                    "raw_source_spec_screening_requested",
                    return_value=True,
                ),
                mock.patch(
                    "scripts.current_closeout.review_surface."
                    "load_current_v11_review_graph_projection",
                    return_value=None,
                ),
            ):
                with self.assertRaisesRegex(
                    ValueError, "--prepare-v11-lean-review-graph"
                ):
                    packet.write_packet_lean_cache_from_current_v11_graph(
                        paper_dir,
                        repository_root=root,
                    )

    def test_packet_preparation_distinguishes_missing_and_stale_current_graph(
        self,
    ) -> None:
        projection = SimpleNamespace(graph_sha256="a" * 64)
        drift = ValueError(
            "Lean import-closure source validation found 1 problem(s):\n"
            "- Lean import-closure source bytes changed: "
            "AppliedModelingLib/Shared.lean"
        )
        for label, loader_kwargs in (
            ("ordinary miss", {"return_value": None}),
            ("source drift", {"side_effect": drift}),
        ):
            with self.subTest(label=label), tempfile.TemporaryDirectory() as temp_dir:
                root = Path(temp_dir)
                paper_dir = root / "papers" / "Fixture"
                audit = paper_dir / "audit"
                audit.mkdir(parents=True)
                (paper_dir / "status.json").write_text("{}\n", encoding="utf-8")
                source_map = {"paper": "Fixture", "items": {}}
                (audit / "paper_statement_map.json").write_text(
                    json.dumps(source_map), encoding="utf-8"
                )
                expected = audit / "human_review_packet_lean_cache.json"
                with (
                    mock.patch.object(
                        packet,
                        "raw_source_spec_screening_requested",
                        return_value=True,
                    ),
                    mock.patch.object(
                        review_surface_owner,
                        "load_current_v11_review_graph_projection",
                        **loader_kwargs,
                    ),
                    mock.patch.object(
                        review_surface_owner,
                        "_recorded_graph_packet_projection",
                        return_value=(True, projection),
                    ),
                    mock.patch.object(
                        packet,
                        "write_packet_lean_cache_from_accepted_graph",
                        return_value=expected,
                    ) as recover,
                    mock.patch.object(
                        packet.subprocess,
                        "run",
                        side_effect=AssertionError(
                            "packet preparation started a producer"
                        ),
                    ),
                ):
                    if label == "source drift":
                        with self.assertRaisesRegex(
                            ValueError, "--record-current-lean-import-closure"
                        ) as raised:
                            packet.write_packet_lean_cache_from_current_v11_graph(
                                paper_dir, repository_root=root
                            )
                        self.assertIn("--prepare-v11-lean-review-graph", str(raised.exception))
                        recover.assert_not_called()
                    else:
                        observed = packet.write_packet_lean_cache_from_current_v11_graph(
                            paper_dir, repository_root=root
                        )
                        self.assertEqual(observed, expected)
                        recover.assert_called_once_with(
                            paper_dir, source_map=source_map, projection=projection
                        )

    def test_current_graph_source_drift_requires_exact_bounded_diagnostic(self) -> None:
        valid = (
            "Lean import-closure source validation found 2 problem(s):\n"
            "- Lean import-closure source bytes changed: "
            "AppliedModelingLib/First.lean\n"
            "- Lean import-closure source bytes changed: papers/Fixture/Second.lean"
        )
        self.assertTrue(packet._only_lean_import_source_bytes_changed(ValueError(valid)))
        invalid = (
            valid.replace("2 problem(s)", "3 problem(s)"),
            valid.replace("source bytes changed", "source ownership changed", 1),
            valid.replace("AppliedModelingLib/First.lean", "/tmp/First.lean"),
            valid.replace("AppliedModelingLib/First.lean", "../First.lean"),
            valid.replace("AppliedModelingLib/First.lean", "First.txt"),
        )
        for message in invalid:
            with self.subTest(message=message):
                self.assertFalse(
                    packet._only_lean_import_source_bytes_changed(
                        ValueError(message)
                    )
                )

    def test_current_graph_errors_propagate_without_accepted_display_authority(
        self,
    ) -> None:
        drift = (
            "Lean import-closure source validation found 1 problem(s):\n"
            "- Lean import-closure source bytes changed: "
            "AppliedModelingLib/Shared.lean"
        )
        cases = (
            (drift, (True, None)),
            ("current graph has malformed evidence", (True, SimpleNamespace())),
        )
        for message, recorded in cases:
            with self.subTest(message=message), tempfile.TemporaryDirectory() as temp_dir:
                root = Path(temp_dir)
                paper_dir = root / "papers" / "Fixture"
                audit = paper_dir / "audit"
                audit.mkdir(parents=True)
                (paper_dir / "status.json").write_text("{}\n", encoding="utf-8")
                (audit / "paper_statement_map.json").write_text(
                    '{"paper":"Fixture","items":{}}\n', encoding="utf-8"
                )
                with (
                    mock.patch.object(
                        packet,
                        "raw_source_spec_screening_requested",
                        return_value=True,
                    ),
                    mock.patch.object(
                        review_surface_owner,
                        "load_current_v11_review_graph_projection",
                        side_effect=ValueError(message),
                    ),
                    mock.patch.object(
                        review_surface_owner,
                        "_recorded_graph_packet_projection",
                        return_value=recorded,
                    ) as accepted,
                    self.assertRaisesRegex(ValueError, re.escape(message)),
                ):
                    packet.write_packet_lean_cache_from_current_v11_graph(
                        paper_dir, repository_root=root
                    )
                accepted.assert_not_called()

    def test_accepted_display_recovery_writes_only_graph_owned_roots(self) -> None:
        claim = "Fixture.claimSpec"
        prerequisite = "Fixture.Model"
        library = "AppliedModelingLib.Shared"
        claim_display = "True"
        prerequisite_display = "type: Prop\n\nvalue:\nTrue"
        library_display = "type: Prop\n\nvalue:\nFalse"
        claim_digest = hashlib.sha256(claim_display.encode()).hexdigest()
        prerequisite_digest = hashlib.sha256(
            prerequisite_display.encode()
        ).hexdigest()
        library_digest = hashlib.sha256(library_display.encode()).hexdigest()
        projection = SimpleNamespace(
            reviewed_display_surface_complete=True,
            claim_semantic_target_sha256s_by_specification={
                claim: claim_digest
            },
            prerequisite_semantic_target_sha256s_by_declaration={
                prerequisite: prerequisite_digest,
                library: library_digest,
            },
        )
        paper_items = {
            prerequisite: {"semantic_supporting_declarations_sha256": ""}
        }
        route_set = SimpleNamespace(result_specifications=lambda: {claim})
        candidates = {
            claim_digest: {claim_display},
            prerequisite_digest: {prerequisite_display},
            library_digest: {library_display},
            hashlib.sha256(b"extra helper").hexdigest(): {"extra helper"},
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Fixture"
            (paper_dir / "audit").mkdir(parents=True)
            with (
                mock.patch.object(
                    packet.EvidenceRouteSet,
                    "from_source_map",
                    return_value=route_set,
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_recorded_graph_source_cards_current",
                    return_value=True,
                ),
                mock.patch.object(
                    packet,
                    "_retained_review_material_display_candidates",
                    return_value=(candidates, {}),
                ),
                mock.patch.object(
                    packet,
                    "_accepted_prerequisite_locations",
                    return_value=(
                        {prerequisite},
                        {library},
                        paper_items,
                        {library: {
                            "library_source_path": "AppliedModelingLib/Shared.lean"
                        }},
                    ),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_library_semantic_source_modules_sha256",
                    return_value="b" * 64,
                ),
            ):
                path = packet.write_packet_lean_cache_from_accepted_graph(
                    paper_dir,
                    source_map={"paper": "Fixture"},
                    projection=projection,
                )
            payload = json.loads(path.read_text(encoding="utf-8"))

        self.assertEqual(set(payload["semantic_targets"]), {claim})
        self.assertEqual(
            set(payload["paper_prerequisite_targets"]), {prerequisite}
        )
        self.assertEqual(set(payload["library_semantic_targets"]), {library})
        self.assertEqual(
            payload["library_semantic_targets"][library]["source_module"],
            "AppliedModelingLib.Shared",
        )
        self.assertTrue(
            review_surface_owner._recorded_graph_packet_cache_current(
                payload, [claim], projection
            )
        )

    def test_accepted_display_recovery_recomputes_every_candidate_digest(self) -> None:
        expected = hashlib.sha256(b"True").hexdigest()
        with self.assertRaisesRegex(ValueError, "missing claim display"):
            packet._recover_accepted_displays(
                {"Fixture.claimSpec": expected},
                {expected: {"False"}},
                label="claim",
            )

    def test_terminal_checkpoint_supplies_only_digest_bound_display_transport(
        self,
    ) -> None:
        from scripts.current_closeout import lean_review_graph
        from scripts.lean_review_surface import (
            TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA,
            TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA,
            TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA,
        )

        claim = "Fixture.claimSpec"
        library = "AppliedModelingLib.Shared"
        claim_display = "True"
        library_display = "type: Prop\n\nvalue:\nFalse"
        inventory = {
            "transparent_spec_displays": {
                "schema": TRANSPARENT_PAPER_SPEC_DISPLAY_SCHEMA,
                "items": [{
                    "specification": claim,
                    "display": claim_display,
                    "complete": True,
                }],
            },
            "paper_prerequisite_displays": {
                "schema": TRANSPARENT_PAPER_DECLARATION_DISPLAY_SCHEMA,
                "items": [],
            },
            "library_prerequisite_displays": {
                "schema": TRANSPARENT_LIBRARY_DECLARATION_DISPLAY_SCHEMA,
                "items": [{
                    "declaration": library,
                    "display": library_display,
                    "source_module": "AppliedModelingLib.Shared",
                }],
            },
        }
        carrier = {"graph_request": {"schema": 5}}
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            index_path = root / "terminal-index.json"
            index_path.write_text(json.dumps({
                "schema": lean_review_graph.V11_TERMINAL_GRAPH_CHECKPOINT_SCHEMA,
                "acceptance_credential": False,
                "operational_scheduling_only": True,
                "paper": "Fixture",
                "context_input_sha256": "a" * 64,
                "graph_reference": {"sha256": "b" * 64},
            }), encoding="utf-8")
            with (
                mock.patch.object(packet, "ROOT", root),
                mock.patch.object(
                    lean_review_graph,
                    "_terminal_graph_checkpoint_index_path",
                    return_value=index_path,
                ),
                mock.patch(
                    "scripts.closeout_content_store.load_closeout_object",
                    return_value=carrier,
                ),
                mock.patch.object(
                    lean_review_graph,
                    "_validated_operational_graph_carrier_inventory",
                    return_value=inventory,
                ) as validate,
                mock.patch.object(
                    packet.subprocess,
                    "run",
                    side_effect=AssertionError("checkpoint reader started a producer"),
                ),
            ):
                candidates, modules = (
                    packet._retained_terminal_graph_display_candidates(paper_dir)
                )

        claim_digest = hashlib.sha256(claim_display.encode()).hexdigest()
        library_digest = hashlib.sha256(library_display.encode()).hexdigest()
        self.assertEqual(candidates[claim_digest], {claim_display})
        self.assertEqual(
            modules[(library, library_digest)], {"AppliedModelingLib.Shared"}
        )
        self.assertEqual(
            packet._recover_accepted_displays(
                {claim: claim_digest}, candidates, label="claim"
            ),
            {claim: claim_display},
        )
        with self.assertRaisesRegex(ValueError, "missing claim display"):
            packet._recover_accepted_displays(
                {claim: hashlib.sha256(b"False").hexdigest()},
                candidates,
                label="claim",
            )
        validate.assert_called_once()

    def test_accepted_display_recovery_rejects_changed_source_before_archives(
        self,
    ) -> None:
        claim = "Fixture.claimSpec"
        projection = SimpleNamespace(
            reviewed_display_surface_complete=True,
            claim_semantic_target_sha256s_by_specification={claim: "a" * 64},
            prerequisite_semantic_target_sha256s_by_declaration={},
        )
        route_set = SimpleNamespace(result_specifications=lambda: {claim})
        with (
            mock.patch.object(
                packet.EvidenceRouteSet,
                "from_source_map",
                return_value=route_set,
            ),
            mock.patch.object(
                review_surface_owner,
                "_recorded_graph_source_cards_current",
                return_value=False,
            ),
            mock.patch.object(
                packet,
                "_retained_review_material_display_candidates",
                side_effect=AssertionError("stale source read retained review material"),
            ),
            self.assertRaisesRegex(ValueError, "exact current source cards"),
        ):
            packet.write_packet_lean_cache_from_accepted_graph(
                Path("Fixture"),
                source_map={"paper": "Fixture"},
                projection=projection,
            )

    def test_legacy_packet_preparation_is_retired(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            with mock.patch.object(
                packet,
                "raw_source_spec_screening_requested",
                return_value=False,
            ):
                with self.assertRaisesRegex(ValueError, "current typed v11"):
                    packet.write_packet_lean_cache_from_current_v11_graph(
                        paper_dir,
                        repository_root=root,
                    )

    def test_prepare_packet_prefers_current_graph_before_legacy_discovery(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            with (
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    packet,
                    "write_packet_lean_cache_from_current_v11_graph",
                    return_value=paper_dir / review_surface_owner.PACKET_LEAN_CACHE_NAME,
                ) as graph_writer,
                mock.patch.object(
                    review_surface_owner,
                    "_read_json",
                    side_effect=AssertionError("legacy packet discovery was called"),
                ),
            ):
                message = packet.prepare_packet_lean_cache(
                    "Fixture", stage="specifications"
                )

        self.assertIn("complete packet Lean cache", message)
        graph_writer.assert_called_once_with(paper_dir, repository_root=root)

    def test_prepare_packet_rejects_unknown_stage_before_graph_work(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            with (
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    packet,
                    "write_packet_lean_cache_from_current_v11_graph",
                    side_effect=AssertionError("graph work was called"),
                ),
            ):
                with self.assertRaisesRegex(ValueError, "unknown packet Lean-cache"):
                    packet.prepare_packet_lean_cache("Fixture", stage="unknown")

    def test_library_target_source_fingerprint_ignores_unrelated_modules(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            library = root / "AppliedModelingLib"
            library.mkdir()
            relevant = library / "Relevant.lean"
            unrelated = library / "Unrelated.lean"
            relevant.write_text("def relevant := True\n", encoding="utf-8")
            unrelated.write_text("def unrelated := True\n", encoding="utf-8")
            targets = {
                "AppliedModelingLib.relevant": {
                    "source_module": "AppliedModelingLib.Relevant",
                }
            }
            with mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root):
                initial = review_surface_owner._library_semantic_source_modules_sha256(targets)
                unrelated.write_text("def unrelated := False\n", encoding="utf-8")
                after_unrelated = review_surface_owner._library_semantic_source_modules_sha256(
                    targets
                )
                relevant.write_text("def relevant := False\n", encoding="utf-8")
                after_relevant = review_surface_owner._library_semantic_source_modules_sha256(
                    targets
                )

        self.assertRegex(str(initial), r"^[0-9a-f]{64}$")
        self.assertEqual(initial, after_unrelated)
        self.assertNotEqual(initial, after_relevant)

    def test_unified_graph_packet_cache_does_not_reclassify_roots_by_namespace(
        self,
    ) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "paper_root": {
                    "source_kind": "definition",
                    "inventory_role": "source_semantic_declaration",
                    "lean_declarations": ["AppliedModelingLib.PaperNamed"],
                },
                "library_root": {
                    "source_kind": "definition",
                    "inventory_role": "source_semantic_declaration",
                    "lean_declarations": ["Fixture.LibraryNamed"],
                },
                "result": {
                    "source_kind": "theorem",
                    "semantic_contract": {
                        "spec_declaration": "Fixture.claimSpec",
                        "evidence_declaration": "Fixture.claim",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                },
            },
            "paper_semantic_prerequisite_sources": {
                "AppliedModelingLib.PaperNamed": "paper_root"
            },
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            (folder / "audit").mkdir()
            with (
                mock.patch.object(review_surface_owner, "_read_json", return_value=source_map),
                mock.patch.object(review_surface_owner, "_paper_lean_tree_sha256", return_value="a" * 64),
                mock.patch.object(packet, "_lean_source_tree_sha256", return_value="b" * 64),
                mock.patch.object(review_surface_owner, "_packet_lean_display_engine_sha256", return_value="c" * 64),
            ):
                path = packet.write_packet_lean_cache_from_elaborated_graph(
                    folder,
                    semantic_targets={
                        "Fixture.claimSpec": {
                            "prerequisite_declarations": [],
                            "library_declarations": [],
                        }
                    },
                    paper_prerequisite_targets={
                        "AppliedModelingLib.PaperNamed": {
                            "direct_paper_declarations": [],
                            "direct_library_declarations": [],
                        }
                    },
                    paper_prerequisite_supporting_declarations_sha256={
                        "AppliedModelingLib.PaperNamed": ""
                    },
                    library_semantic_targets={
                        "Fixture.LibraryNamed": {
                            "direct_library_declarations": [],
                        }
                    },
                    library_declaration_sources={
                        "Fixture.LibraryNamed": {
                            "library_definition": "def LibraryNamed : Prop := True",
                            "library_definition_sha256": hashlib.sha256(
                                b"def LibraryNamed : Prop := True"
                            ).hexdigest(),
                            "library_definition_error": "",
                            "library_source_path": (
                                "papers/ReusableFixture/Model.lean"
                            ),
                            "library_line_start": 4,
                            "library_line_end": 4,
                        }
                    },
                )

            payload = json.loads(path.read_text(encoding="utf-8"))
        self.assertIn(
            "AppliedModelingLib.PaperNamed", payload["paper_prerequisite_targets"]
        )
        self.assertIn(
            "Fixture.LibraryNamed", payload["library_semantic_targets"]
        )
        self.assertEqual(
            payload["library_declaration_sources"]["Fixture.LibraryNamed"][
                "library_source_path"
            ],
            "papers/ReusableFixture/Model.lean",
        )

    def test_graph_native_packet_stage_checks_non_namespace_reusable_closure(
        self,
    ) -> None:
        routes = mock.Mock()
        routes.result_specifications.return_value = ("Fixture.claimSpec",)
        complete = {
            "semantic_targets": {
                "Fixture.claimSpec": {
                    "prerequisite_declarations": [],
                    "library_declarations": ["OtherPaper.Root"],
                }
            },
            "paper_prerequisite_targets": {},
            "library_semantic_targets": {
                "OtherPaper.Root": {
                    "direct_library_declarations": ["OtherPaper.Child"]
                }
            },
            "library_semantic_target_errors": {},
            "library_declaration_sources": {
                "OtherPaper.Root": {"library_definition": "root"}
            },
        }
        with (
            mock.patch.object(
                packet.EvidenceRouteSet, "from_source_map", return_value=routes
            ),
            mock.patch.object(
                review_surface_owner, "explicit_source_semantic_declarations", return_value=set()
            ),
            mock.patch.object(
                review_surface_owner,
                "_exact_current_packet_lean_cache_transport",
                return_value=complete,
            ),
        ):
            self.assertEqual(
                review_surface_owner.packet_lean_cache_missing_stages(Path("Fixture"), {}),
                ("library",),
            )
            complete["library_semantic_targets"]["OtherPaper.Child"] = {
                "direct_library_declarations": []
            }
            complete["library_declaration_sources"]["OtherPaper.Child"] = {
                "library_definition": "child"
            }
            self.assertEqual(
                review_surface_owner.packet_lean_cache_missing_stages(Path("Fixture"), {}),
                (),
            )

    def test_prepared_graph_surface_skips_raw_verdict_reader_and_binds_source(
        self,
    ) -> None:
        """The accepted graph alone owns verdicts on a graph-backed packet."""

        spec = "Fixture.claimSpec"
        source_text = "The source claim."
        source_bundle = "a" * 64
        display = "True"
        display_sha256 = hashlib.sha256(display.encode("utf-8")).hexdigest()
        record = {"source_status": "direct source text"}
        projection = SimpleNamespace(
            graph_sha256="f" * 64,
            review_declarations_by_source_item={"claim": (spec,)},
            card_review_declarations_by_source_item={"claim": (spec,)},
            source_lean_verdicts_by_source_item={"claim": "matches"},
            source_input_bundle_sha256s_by_source_item={
                "claim": source_bundle
            },
            source_review_metadata_by_specification={
                spec: {
                    "reason": "The accepted source and Spec agree.",
                    "validator": "recorded reviewer",
                    "validated_at": "2026-09-05T12:00:00+00:00",
                }
            },
        )
        cache = {
            "semantic_targets": {
                spec: {
                    "display": display,
                    "display_sha256": display_sha256,
                    "review_claim_manifest_sha256": "b" * 64,
                    "review_claim_atoms_sha256": "c" * 64,
                    "review_claim_atoms": [
                        {"role": "conclusion", "display": "UNBOUND_ROLE_TEXT"}
                    ],
                }
            },
            "paper_prerequisite_targets": {},
            "paper_prerequisite_supporting_declarations_sha256": {},
            "library_semantic_targets": {},
            "library_semantic_target_errors": {},
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            (paper_dir / review_surface_owner.SOURCE_MAP_NAME).parent.mkdir(
                parents=True, exist_ok=True
            )
            (paper_dir / review_surface_owner.SOURCE_MAP_NAME).write_text(
                json.dumps({"paper": "Fixture", "items": {"claim": record}}),
                encoding="utf-8",
            )
            (paper_dir / "status.json").write_text(
                json.dumps({"review_surface": {}}), encoding="utf-8"
            )
            (paper_dir / review_surface_owner.V11_SCREENING_NAME).write_text(
                json.dumps(
                    {
                        "schema": review_surface_owner.V11_SCREENING_SCHEMA,
                        "paper": "Fixture",
                        "items": {
                            spec: {
                                "judgment": "matches",
                                "reason": "Changed unbound ledger reason.",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    review_surface_owner,
                    "_typed_result_records",
                    return_value=(
                        {spec: record},
                        {"claim": SimpleNamespace(spec_declaration=spec)},
                    ),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_claim_review_rows",
                    return_value=[
                        (
                            {"full_name": spec, "kind": "def"},
                            [record],
                            "Fixture.claim",
                        )
                    ],
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_current_packet_lean_cache_selection",
                    return_value=review_surface_owner._PacketLeanCacheSelection(
                        payload=cache,
                        authority="accepted_graph",
                        recorded_graph_projection=projection,
                    ),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "source_semantic_input_bundle",
                    return_value=(source_text, source_bundle, ""),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "bind_current_v11_source_spec_screening",
                    side_effect=AssertionError("graph surface read raw verdicts"),
                ),
            ):
                prepared = review_surface_owner.prepared_review_surface("Fixture", allow_draft=True)

        row = prepared.claim_rows[0][0]
        self.assertEqual(row["llm_match_judgment"], "matches")
        self.assertTrue(row["llm_match_current"])
        self.assertEqual(row["llm_match_source"], "accepted obligation graph")
        self.assertEqual(
            row["llm_match_reason"],
            "The accepted source and Spec agree.",
        )
        self.assertNotEqual(row["llm_match_reason"], "Changed unbound ledger reason.")
        self.assertEqual(row["llm_match_validator"], "recorded reviewer")
        self.assertEqual(
            row["llm_match_validated_at"], "2026-09-05T12:00:00+00:00"
        )
        self.assertEqual(row["verbatim_source_input"], source_text)
        self.assertEqual(row["semantic_expanded_statement"], display)
        self.assertEqual(row["review_claim_atoms"], [])

    def test_prepared_graph_surface_rejects_a_different_source_bundle(self) -> None:
        """A graph verdict cannot be attached to changed source-card bytes."""

        spec = "Fixture.claimSpec"
        record = {"source_status": "direct source text"}
        display = "True"
        display_sha256 = hashlib.sha256(display.encode("utf-8")).hexdigest()
        cache = {
            "semantic_targets": {
                spec: {"display": display, "display_sha256": display_sha256}
            },
            "paper_prerequisite_targets": {},
            "paper_prerequisite_supporting_declarations_sha256": {},
            "library_semantic_targets": {},
            "library_semantic_target_errors": {},
        }
        projection = SimpleNamespace(
            graph_sha256="f" * 64,
            review_declarations_by_source_item={"claim": (spec,)},
            card_review_declarations_by_source_item={"claim": (spec,)},
            source_lean_verdicts_by_source_item={"claim": "matches"},
            source_input_bundle_sha256s_by_source_item={"claim": "a" * 64},
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            (paper_dir / review_surface_owner.SOURCE_MAP_NAME).parent.mkdir(
                parents=True, exist_ok=True
            )
            (paper_dir / review_surface_owner.SOURCE_MAP_NAME).write_text(
                json.dumps({"paper": "Fixture", "items": {"claim": record}}),
                encoding="utf-8",
            )
            (paper_dir / "status.json").write_text("{}", encoding="utf-8")
            with (
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    review_surface_owner,
                    "_typed_result_records",
                    return_value=(
                        {spec: record},
                        {"claim": SimpleNamespace(spec_declaration=spec)},
                    ),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_claim_review_rows",
                    return_value=[
                        (
                            {"full_name": spec, "kind": "def"},
                            [record],
                            "Fixture.claim",
                        )
                    ],
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_current_packet_lean_cache_selection",
                    return_value=review_surface_owner._PacketLeanCacheSelection(
                        payload=cache,
                        authority="accepted_graph",
                        recorded_graph_projection=projection,
                    ),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "source_semantic_input_bundle",
                    return_value=("changed source", "b" * 64, ""),
                ),
            ):
                with self.assertRaisesRegex(
                    ValueError, "does not authenticate the exact source card"
                ):
                    review_surface_owner.prepared_review_surface("Fixture", allow_draft=True)

    def test_recorded_graph_card_surface_rejects_an_omitted_source_item(self) -> None:
        projection = SimpleNamespace(
            review_declarations_by_source_item={
                "claim": ("Fixture.claimSpec",),
                "model": ("Fixture.Model",),
            },
            card_review_declarations_by_source_item={
                "claim": ("Fixture.claimSpec",),
                "model": ("Fixture.Model",),
            },
            source_lean_verdicts_by_source_item={
                "claim": "matches",
                "model": "matches",
            },
            source_input_bundle_sha256s_by_source_item={
                "claim": "a" * 64,
                "model": "b" * 64,
            },
        )
        claim_rows = (
            (
                {
                    "source_item_key": "claim",
                    "semantic_review_declaration": "Fixture.claimSpec",
                },
                (),
                "Fixture.claim",
            ),
        )

        with self.assertRaisesRegex(
            ValueError, "missing source items: model"
        ):
            review_surface_owner._validate_recorded_graph_card_surface(
                projection, claim_rows, (), ()
            )

    def test_recorded_graph_card_surface_rejects_a_duplicate_card(self) -> None:
        projection = SimpleNamespace(
            card_review_declarations_by_source_item={
                "claim": ("Fixture.claimSpec",),
            },
            source_lean_verdicts_by_source_item={"claim": "matches"},
            source_input_bundle_sha256s_by_source_item={"claim": "a" * 64},
        )
        claim = (
            {
                "source_item_key": "claim",
                "semantic_review_declaration": "Fixture.claimSpec",
            },
            (),
            "Fixture.claim",
        )

        with self.assertRaisesRegex(ValueError, "repeat graph identity"):
            review_surface_owner._validate_recorded_graph_card_surface(
                projection, (claim, claim), (), ()
            )

    def test_packet_cache_readiness_requires_complete_lean_dependency_closure(self) -> None:
        routes = SimpleNamespace(result_specifications=lambda: ("Fixture.claimSpec",))
        base = {
            "semantic_targets": {
                "Fixture.claimSpec": {
                    "prerequisite_declarations": ["Fixture.Model"],
                    "library_declarations": ["AppliedModelingLib.Shared.Root"],
                }
            },
            "paper_prerequisite_targets": {
                "Fixture.Model": {
                    "direct_paper_declarations": ["Fixture.Child"],
                    "direct_library_declarations": [],
                }
            },
            "library_semantic_targets": {},
            "library_semantic_target_errors": {},
        }
        with (
            mock.patch.object(
                packet.EvidenceRouteSet, "from_source_map", return_value=routes
            ),
            mock.patch.object(
                review_surface_owner, "explicit_source_semantic_declarations", return_value=set()
            ),
            mock.patch.object(
                review_surface_owner,
                "_exact_current_packet_lean_cache_transport",
                return_value=base,
            ),
        ):
            self.assertEqual(
                review_surface_owner.packet_lean_cache_missing_stages(Path("Fixture"), {}),
                ("paper-prerequisites", "library"),
            )

        complete = json.loads(json.dumps(base))
        complete["paper_prerequisite_targets"]["Fixture.Child"] = {
            "direct_paper_declarations": [],
            "direct_library_declarations": [],
        }
        complete["library_semantic_targets"] = {
            "AppliedModelingLib.Shared.Root": {
                "direct_library_declarations": ["AppliedModelingLib.Shared.Child"]
            }
        }
        with (
            mock.patch.object(
                packet.EvidenceRouteSet, "from_source_map", return_value=routes
            ),
            mock.patch.object(
                review_surface_owner, "explicit_source_semantic_declarations", return_value=set()
            ),
            mock.patch.object(
                review_surface_owner,
                "_exact_current_packet_lean_cache_transport",
                return_value=complete,
            ),
        ):
            self.assertEqual(
                review_surface_owner.packet_lean_cache_missing_stages(Path("Fixture"), {}),
                ("library",),
            )
            complete["library_semantic_targets"]["AppliedModelingLib.Shared.Child"] = {
                "direct_library_declarations": []
            }
            self.assertEqual(
                review_surface_owner.packet_lean_cache_missing_stages(Path("Fixture"), {}),
                (),
            )

    def test_source_version_falls_back_to_canonical_status_metadata(self) -> None:
        self.assertEqual(
            renderer._packet_source_version(
                {"source_version": "arXiv v1, 2026"},
                {"items": {}},
            ),
            "arXiv v1, 2026",
        )
        self.assertEqual(
            renderer._packet_source_version(
                {"source_version": "status version"},
                {"source_version": "map version"},
            ),
            "map version",
        )

    def test_paper_prerequisite_changed_signature_stales_same_display(self) -> None:
        """Pretty-printer equality cannot conceal a changed Lean proposition."""

        from scripts import reissue_paper_semantic_prerequisites as reissue

        source_sha = "a" * 64
        declaration_sha = "b" * 64
        prior = {
            "paper_semantic_target_protocol": review_surface_owner.PAPER_PREREQUISITE_TARGET_PROTOCOL,
            "paper_semantic_target_sha256": "c" * 64,
            "elaborated_signature_sha256": "d" * 64,
            "paper_declaration_sha256": declaration_sha,
            "source_input_bundle_sha256": source_sha,
            "judgment": "matches",
            "reason": "The exact source and semantic target match.",
            "validator": "prior reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-24T00:00:00+00:00",
        }
        entry = {
            "paper_semantic_target_sha256": "c" * 64,
            "elaborated_signature_sha256": "e" * 64,
            "paper_declaration_sha256": declaration_sha,
            "source_input_bundle_sha256": source_sha,
        }

        self.assertIsNone(reissue._unchanged_semantic_judgment(prior, entry))

    def test_historical_schema6_cache_uses_its_strict_semantic_reader(
        self,
    ) -> None:
        """A graph without display digests neither weakens nor reruns its reader."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            spec = "Fixture.claimSpec"
            spec_display = "True"
            spec_hash = hashlib.sha256(spec_display.encode("utf-8")).hexdigest()
            claim_manifest_hash = "6" * 64
            claim_atoms = [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {"tag": "const", "name": "True"},
                    "display": "True",
                }
            ]
            claim_atoms_hash = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 1,
                        "atoms": [
                            {
                                key: value
                                for key, value in claim_atoms[0].items()
                                if key != "display"
                            }
                        ],
                    },
                    ensure_ascii=True,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            prerequisite = "Fixture.Model"
            prerequisite_display = "structure Model where\n  size : Nat"
            prerequisite_hash = hashlib.sha256(
                prerequisite_display.encode("utf-8")
            ).hexdigest()
            library = "AppliedModelingLib.Shared.Definition"
            library_display = "def shared : Prop := True"
            library_hash = hashlib.sha256(
                library_display.encode("utf-8")
            ).hexdigest()
            payload = {
                "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
                "paper": "Fixture",
                "specifications": [spec],
                "paper_lean_tree_sha256": "d" * 64,
                "library_lean_tree_sha256": "e" * 64,
                "library_semantic_source_modules_sha256": "a" * 64,
                "lean_display_engine_sha256": "f" * 64,
                "semantic_targets": {
                    spec: {
                        "display": spec_display,
                        "display_sha256": spec_hash,
                        "review_claim_manifest_sha256": claim_manifest_hash,
                        "review_claim_atoms_sha256": claim_atoms_hash,
                        "review_claim_atoms": claim_atoms,
                    },
                },
                "paper_prerequisite_targets": {
                    prerequisite: {
                        "display": prerequisite_display,
                        "display_sha256": prerequisite_hash,
                    },
                },
                "paper_prerequisite_supporting_declarations_sha256": {
                    prerequisite: ""
                },
                "library_semantic_targets": {
                    library: {
                        "display": library_display,
                        "display_sha256": library_hash,
                    },
                },
                "library_semantic_target_errors": {},
            }
            (audit_dir / "human_review_packet_lean_cache.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            (paper_dir / review_surface_owner.V11_SCREENING_NAME).write_text(
                json.dumps(
                    {
                        "items": {
                            spec: {
                                "judgment": review_surface_owner.APPROVED_CORRECTED_TARGET_MATCH,
                                "lean_expanded_statement_sha256": spec_hash,
                                "review_claim_manifest_sha256": claim_manifest_hash,
                                "review_claim_atoms_sha256": claim_atoms_hash,
                                # Valid historical presentation trace,
                                # intentionally unequal to today's rendered
                                # worksheet bytes.
                                "source_review_target_sha256": "0" * 64,
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            (paper_dir / review_surface_owner.PAPER_PREREQUISITE_LEDGER_NAME).write_text(
                json.dumps(
                    {
                        "items": {
                            prerequisite: {
                                "judgment": "matches",
                                "paper_semantic_target_sha256": prerequisite_hash,
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            (paper_dir / review_surface_owner.LIBRARY_SEMANTIC_REVIEW_NAME).write_text(
                json.dumps(
                    {
                        "items": {
                            library: {
                                "judgment": "matches",
                                "library_semantic_target_sha256": library_hash,
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            authority = review_surface_owner.CurrentSemanticReuseAuthority(
                paper="Fixture",
                raw_audit_file_sha256="1" * 64,
                semantic_identity_sha256="2" * 64,
                reviewed_declarations=(spec,),
                watched_repository_material=(),
                result={"current": True},
            )
            with (
                mock.patch.object(
                    review_surface_owner,
                    "_recorded_graph_packet_projection",
                    return_value=(
                        True,
                        SimpleNamespace(reviewed_display_surface_complete=False),
                    ),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_paper_lean_tree_sha256",
                    side_effect=AssertionError("historical reader hashed paper tree"),
                ),
                mock.patch.object(
                    packet,
                    "_lean_source_tree_sha256",
                    side_effect=AssertionError("historical reader hashed library tree"),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_packet_lean_display_engine_sha256",
                    side_effect=AssertionError("historical reader hashed display engine"),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "current_dashboard_semantic_reuse_authority",
                    return_value=authority,
                ) as load_authority,
            ):
                current = review_surface_owner._current_packet_lean_cache(
                    paper_dir,
                    [spec],
                )

                screening_path = paper_dir / review_surface_owner.V11_SCREENING_NAME
                invalid_screening = json.loads(
                    screening_path.read_text(encoding="utf-8")
                )
                invalid_screening["items"][spec][
                    "source_review_target_sha256"
                ] = "invalid"
                screening_path.write_text(
                    json.dumps(invalid_screening), encoding="utf-8"
                )
                invalid = review_surface_owner._current_packet_lean_cache(
                    paper_dir,
                    [spec],
                    semantic_reuse_authority=authority,
                )

        self.assertEqual(current, payload)
        self.assertIsNone(invalid)
        load_authority.assert_called_once_with(paper_dir)

    def test_schema6_packet_cache_uses_recorded_graph_before_container_hashes(
        self,
    ) -> None:
        """An accepted graph authenticates displays without source or Lean probes."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            spec = "Fixture.claimSpec"
            spec_display = "True"
            spec_sha256 = hashlib.sha256(spec_display.encode("utf-8")).hexdigest()
            paper_name = "Fixture.Model"
            paper_display = "structure Model where\n  size : Nat"
            paper_sha256 = hashlib.sha256(
                paper_display.encode("utf-8")
            ).hexdigest()
            library_name = "AppliedModelingLib.Shared.Model"
            library_display = "def shared : Prop := True"
            library_sha256 = hashlib.sha256(
                library_display.encode("utf-8")
            ).hexdigest()
            atoms = [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {"tag": "const", "name": "True"},
                    "display": "True",
                }
            ]
            atoms_sha256 = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 1,
                        "atoms": [
                            {
                                key: value
                                for key, value in atoms[0].items()
                                if key != "display"
                            }
                        ],
                    },
                    ensure_ascii=True,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            payload = {
                "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
                "paper": "Fixture",
                "specifications": [spec],
                "paper_lean_tree_sha256": "1" * 64,
                "library_lean_tree_sha256": "2" * 64,
                "lean_display_engine_sha256": "3" * 64,
                "semantic_targets": {
                    spec: {
                        "display": spec_display,
                        "display_sha256": spec_sha256,
                        "review_claim_manifest_sha256": "4" * 64,
                        "review_claim_atoms_sha256": atoms_sha256,
                        "review_claim_atoms": atoms,
                    }
                },
                # The accepted authority is deliberately location-neutral. A
                # presentation partition cannot change semantic acceptance.
                "paper_prerequisite_targets": {
                    library_name: {
                        "display": library_display,
                        "display_sha256": library_sha256,
                    }
                },
                "paper_prerequisite_supporting_declarations_sha256": {
                    library_name: ""
                },
                "library_semantic_targets": {
                    paper_name: {
                        "display": paper_display,
                        "display_sha256": paper_sha256,
                    }
                },
                "library_semantic_target_errors": {},
            }
            (audit_dir / review_surface_owner.PACKET_LEAN_CACHE_NAME.split("/")[-1]).write_text(
                json.dumps(payload), encoding="utf-8"
            )
            projection = SimpleNamespace(
                claim_semantic_target_sha256s_by_specification={
                    spec: spec_sha256
                },
                prerequisite_semantic_target_sha256s_by_declaration={
                    paper_name: paper_sha256,
                    library_name: library_sha256,
                },
                reviewed_display_surface_complete=True,
            )
            with (
                mock.patch.object(
                    review_surface_owner,
                    "_recorded_graph_packet_projection",
                    return_value=(True, projection),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_paper_lean_tree_sha256",
                    side_effect=AssertionError("schema 6 hashed the paper tree"),
                ),
                mock.patch.object(
                    packet,
                    "_lean_source_tree_sha256",
                    side_effect=AssertionError("schema 6 hashed the library tree"),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "current_dashboard_semantic_reuse_authority",
                    side_effect=AssertionError("schema 6 loaded legacy authority"),
                ),
            ):
                current = review_surface_owner._current_packet_lean_cache(paper_dir, [spec])

        self.assertEqual(current, payload)

    def test_exact_partial_cache_is_resumable_transport_not_presentation_authority(
        self,
    ) -> None:
        """A bounded Lean batch can resume without impersonating an accepted cache."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            (root / "AppliedModelingLib").mkdir()
            first = "Fixture.firstSpec"
            second = "Fixture.secondSpec"
            display = "True"
            display_sha256 = hashlib.sha256(
                display.encode("utf-8")
            ).hexdigest()
            empty_library_modules_sha256 = hashlib.sha256(b"").hexdigest()
            payload = {
                "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
                "paper": "Fixture",
                "specifications": [first, second],
                "paper_lean_tree_sha256": "1" * 64,
                "library_lean_tree_sha256": "2" * 64,
                "library_semantic_source_modules_sha256": empty_library_modules_sha256,
                "lean_display_engine_sha256": "3" * 64,
                "semantic_targets": {
                    first: {
                        "display": display,
                        "display_sha256": display_sha256,
                    }
                },
                "paper_prerequisite_targets": {},
                "paper_prerequisite_supporting_declarations_sha256": {},
                "library_semantic_targets": {},
                "library_semantic_target_errors": {},
            }
            path = audit_dir / review_surface_owner.PACKET_LEAN_CACHE_NAME.split("/")[-1]
            path.write_text(json.dumps(payload), encoding="utf-8")
            with (
                mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root),
                mock.patch.object(
                    review_surface_owner, "_paper_lean_tree_sha256", return_value="1" * 64
                ),
                mock.patch.object(
                    packet, "_lean_source_tree_sha256", return_value="2" * 64
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_packet_lean_display_engine_sha256",
                    return_value="3" * 64,
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_recorded_graph_packet_projection",
                    return_value=(True, None),
                ),
            ):
                transport = review_surface_owner._exact_current_packet_lean_cache_transport(
                    paper_dir, [first, second]
                )
                presentation = review_surface_owner._current_packet_lean_cache(
                    paper_dir, [first, second]
                )

                payload["paper_lean_tree_sha256"] = "4" * 64
                path.write_text(json.dumps(payload), encoding="utf-8")
                stale = review_surface_owner._exact_current_packet_lean_cache_transport(
                    paper_dir, [first, second]
                )

                payload["paper_lean_tree_sha256"] = "1" * 64
                payload["semantic_targets"][first]["display"] = "False"
                path.write_text(json.dumps(payload), encoding="utf-8")
                tampered = review_surface_owner._exact_current_packet_lean_cache_transport(
                    paper_dir, [first, second]
                )

        self.assertEqual(transport, {
            **payload,
            "paper_lean_tree_sha256": "1" * 64,
            "semantic_targets": {
                first: {
                    "display": display,
                    "display_sha256": display_sha256,
                }
            },
        })
        self.assertIsNone(presentation)
        self.assertIsNone(stale)
        self.assertIsNone(tampered)

    def test_schema6_packet_cache_mismatch_fails_without_legacy_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            spec = "Fixture.claimSpec"
            display = "True"
            display_sha256 = hashlib.sha256(display.encode("utf-8")).hexdigest()
            atoms = [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {"tag": "const", "name": "True"},
                    "display": "True",
                }
            ]
            atoms_sha256 = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 1,
                        "atoms": [
                            {
                                key: value
                                for key, value in atoms[0].items()
                                if key != "display"
                            }
                        ],
                    },
                    ensure_ascii=True,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            payload = {
                "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
                "paper": "Fixture",
                "specifications": [spec],
                "paper_lean_tree_sha256": "1" * 64,
                "library_lean_tree_sha256": "2" * 64,
                "lean_display_engine_sha256": "3" * 64,
                "semantic_targets": {
                    spec: {
                        "display": display,
                        "display_sha256": display_sha256,
                        "review_claim_manifest_sha256": "4" * 64,
                        "review_claim_atoms_sha256": atoms_sha256,
                        "review_claim_atoms": atoms,
                    }
                },
                "paper_prerequisite_targets": {},
                "library_semantic_targets": {},
                "library_semantic_target_errors": {},
            }
            (audit_dir / review_surface_owner.PACKET_LEAN_CACHE_NAME.split("/")[-1]).write_text(
                json.dumps(payload), encoding="utf-8"
            )
            projection = SimpleNamespace(
                claim_semantic_target_sha256s_by_specification={spec: "f" * 64},
                prerequisite_semantic_target_sha256s_by_declaration={},
                reviewed_display_surface_complete=True,
            )
            with (
                mock.patch.object(
                    review_surface_owner,
                    "_recorded_graph_packet_projection",
                    return_value=(True, projection),
                ),
                mock.patch.object(
                    review_surface_owner,
                    "current_dashboard_semantic_reuse_authority",
                    side_effect=AssertionError("schema 6 loaded legacy authority"),
                ),
            ):
                mismatched = review_surface_owner._current_packet_lean_cache(paper_dir, [spec])
                payload["semantic_targets"][spec]["display"] = "False"
                (audit_dir / review_surface_owner.PACKET_LEAN_CACHE_NAME.split("/")[-1]).write_text(
                    json.dumps(payload), encoding="utf-8"
                )
                tampered = review_surface_owner._current_packet_lean_cache(paper_dir, [spec])

        self.assertIsNone(mismatched)
        self.assertIsNone(tampered)

    def test_packet_cache_rejects_changed_reviewed_display(self) -> None:
        """A changed expanded display still requires new Lean and semantic review."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            spec = "Fixture.claimSpec"
            payload = {
                "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
                "paper": "Fixture",
                "specifications": [spec],
                "paper_lean_tree_sha256": "a" * 64,
                "library_lean_tree_sha256": "b" * 64,
                "lean_display_engine_sha256": "c" * 64,
                "semantic_targets": {spec: {"display_sha256": "d" * 64}},
                "paper_prerequisite_targets": {},
                "library_semantic_targets": {},
                "library_semantic_target_errors": {},
            }
            (audit_dir / "human_review_packet_lean_cache.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            (paper_dir / review_surface_owner.V11_SCREENING_NAME).write_text(
                json.dumps(
                    {
                        "items": {
                            spec: {
                                "judgment": "matches",
                                "lean_expanded_statement_sha256": "e" * 64,
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            for relative in (
                review_surface_owner.PAPER_PREREQUISITE_LEDGER_NAME,
                review_surface_owner.LIBRARY_SEMANTIC_REVIEW_NAME,
            ):
                (paper_dir / relative).write_text(
                    json.dumps({"items": {}}), encoding="utf-8"
                )
            authority = review_surface_owner.CurrentSemanticReuseAuthority(
                paper="Fixture",
                raw_audit_file_sha256="1" * 64,
                semantic_identity_sha256="2" * 64,
                reviewed_declarations=(spec,),
                watched_repository_material=(),
                result={"current": True},
            )
            with (
                mock.patch.object(
                    review_surface_owner, "_paper_lean_tree_sha256", return_value="3" * 64
                ),
                mock.patch.object(
                    packet, "_lean_source_tree_sha256", return_value="4" * 64
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_packet_lean_display_engine_sha256",
                    return_value="5" * 64,
                ),
            ):
                current = review_surface_owner._current_packet_lean_cache(
                    paper_dir,
                    [spec],
                    semantic_reuse_authority=authority,
                )

        self.assertIsNone(current)

    def test_packet_cache_does_not_reload_explicitly_absent_authority(self) -> None:
        """A caller-owned authority lookup is not repeated after an exact miss."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            spec = "Fixture.claimSpec"
            payload = {
                "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
                "paper": "Fixture",
                "specifications": [spec],
                "paper_lean_tree_sha256": "a" * 64,
                "library_lean_tree_sha256": "b" * 64,
                "lean_display_engine_sha256": "c" * 64,
                "semantic_targets": {spec: {"display_sha256": "d" * 64}},
                "paper_prerequisite_targets": {},
                "library_semantic_targets": {},
                "library_semantic_target_errors": {},
            }
            (audit_dir / "human_review_packet_lean_cache.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            with (
                mock.patch.object(
                    review_surface_owner, "_paper_lean_tree_sha256", return_value="3" * 64
                ),
                mock.patch.object(
                    packet, "_lean_source_tree_sha256", return_value="4" * 64
                ),
                mock.patch.object(
                    review_surface_owner,
                    "_packet_lean_display_engine_sha256",
                    return_value="5" * 64,
                ),
                mock.patch.object(
                    review_surface_owner,
                    "current_dashboard_semantic_reuse_authority",
                ) as load_authority,
            ):
                current = review_surface_owner._current_packet_lean_cache(
                    paper_dir,
                    [spec],
                    semantic_reuse_authority=None,
                )

        self.assertIsNone(current)
        load_authority.assert_not_called()

    def test_packet_lean_cache_fingerprint_excludes_python_orchestration(self) -> None:
        """Dashboard and renderer edits cannot invalidate Lean display work."""

        self.assertEqual(
            {path.name for path in review_surface_owner._packet_lean_display_engine_paths()},
            {"lean_signature_manifest.py", "lean_signature_manifest_helper.lean"},
        )

    def test_packet_template_includes_fresh_clone_dashboard_instructions(self) -> None:
        """A recipient of a packet can open its interactive counterpart."""

        template = packet.TEMPLATE_PATH.read_text(encoding="utf-8")
        self.assertIn(r"\section*{Open the interactive dashboard}", template)
        self.assertIn(
            "optional alternative to using this PDF",
            template,
        )
        self.assertIn("lake exe cache get", template)
        self.assertIn("review_dashboard.py --paper @@PAPER_ID@@ --serve", template)
        self.assertIn("reviewer-owned review record", template)
        self.assertNotIn("local\nreview trace", template)

    def test_source_version_metadata_wraps_long_archive_identity(self) -> None:
        rendered = renderer._source_version_metadata_tex(
            "AAAI 2025, source archive SHA256 " + "a" * 64
        )

        self.assertIn(r"\parbox[t]{0.76\linewidth}{\raggedright", rendered)
        self.assertTrue(rendered.endswith(r"}\\"))

    def test_packet_public_projection_sanitizes_preescaped_locator_but_not_verbatim_source(self) -> None:
        rendered = renderer._public_packet_presentation_tex(
            "\\textbf{Source locator:} {\\footnotesize\\raggedright "
            "audit/\\allowbreak{}source\\_archive\\_review_surface_owner.\\allowbreak{}tex:"
            "\\allowbreak{}12-\\allowbreak{}15\\par}\n"
            "\\begin{ReviewVerbatim}\n"
            "The raw excerpt may itself mention source_archive_review_surface_owner.tex.\n"
            "\\end{ReviewVerbatim}\n",
            paper="Fixture",
        )
        self.assertNotIn("audit/\\allowbreak{}source", rendered)
        self.assertIn("cited publication, lines 12-\\allowbreak{}15", rendered)
        self.assertIn(
            "The raw excerpt may itself mention source_archive_review_surface_owner.tex.",
            rendered,
        )

    def test_existing_packet_refreshes_reviewer_record_wording(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            tex_path = Path(temp_dir) / "HUMAN_REVIEW_PACKET.tex"
            tex_path.write_text(
                "The dashboard records saved annotations in this paper's local\n"
                "review trace.\n",
                encoding="utf-8",
            )
            rendered = packet.sanitize_existing_packet("Fixture", tex_path)
        self.assertIn("reviewer-owned review record", rendered)
        self.assertNotIn("local\nreview trace", rendered)

    def test_verbatim_marks_nonprintable_source_bytes_without_dropping_them(self) -> None:
        rendered = renderer._verbatim("before\fafter\x0fend")
        self.assertIn("[form-feed in source extraction]", rendered)
        self.assertIn("[U+000F control character]", rendered)

    def test_verbatim_preserves_plain_text_norm_delimiters_when_font_lacks_unicode(self) -> None:
        rendered = renderer._verbatim("∥u - v∥")
        self.assertIn("||u - v||", rendered)
        self.assertNotIn("\x0f", rendered)

    def test_unmarked_packet_requires_an_active_v11_surface(self) -> None:
        self.assertIn(
            "has not explicitly activated",
            review_surface_owner._v11_packet_surface_error({}, {"semantic_contract_schema": 1}),
        )

    def test_v11_screening_uses_literal_source_digest_separately_from_bundle(self) -> None:
        """A context-bound source bundle must not replace the reviewed text hash."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            (paper_dir / "audit").mkdir()
            source_text = "The exact claim under review."
            bundle_digest = "a" * 64
            target = {
                "display": "True",
                "display_sha256": "b" * 64,
                # The target remains exact even when unrelated declarations
                # elsewhere in PaperInterface change the whole-file digest.
                "paper_interface_sha256": "d" * 64,
                "review_claim_manifest_sha256": "e" * 64,
                "review_claim_atoms_sha256": hashlib.sha256(
                    json.dumps(
                        {
                            "schema": 1,
                            "atoms": [
                                {
                                    "ref": "result",
                                    "role": "conclusion",
                                    "canonical": {"tag": "const", "name": "True"},
                                }
                            ],
                        },
                        ensure_ascii=True,
                        sort_keys=True,
                        separators=(",", ":"),
                    ).encode("utf-8")
                ).hexdigest(),
                "review_claim_atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": {"tag": "const", "name": "True"},
                        "display": "True",
                    }
                ],
            }
            (paper_dir / "audit" / "v11_raw_source_spec_screening.json").write_text(
                json.dumps(
                    {
                        "schema": review_surface_owner.V11_SCREENING_SCHEMA,
                        "paper": paper_dir.name,
                        "prompt_version": review_surface_owner.V11_SCREENING_PROMPT_VERSION,
                        "validator": "reviewer",
                        "validated_at": "2026-08-21T00:00:00Z",
                        "items": {
                            "Packet.claimSpec": {
                                "judgment": "matches",
                                "source_input_bundle_sha256": bundle_digest,
                                "paper_statement_sha256": review_dashboard.statement_digest(source_text),
                                "lean_expanded_statement_sha256": target["display_sha256"],
                                "review_claim_manifest_sha256": target[
                                    "review_claim_manifest_sha256"
                                ],
                                "review_claim_atoms_sha256": target[
                                    "review_claim_atoms_sha256"
                                ],
                                "source_review_target_sha256": hashlib.sha256(
                                    review_dashboard.review_claim_target_text(target).encode(
                                        "utf-8"
                                    )
                                ).hexdigest(),
                                "paper_interface_sha256": "c" * 64,
                                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                                "lean_target_protocol": packet.V11_LEAN_TARGET_PROTOCOL,
                                "semantic_target_declaration": "Packet.claimSpec",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            source_map = {
                "items": {
                    "claim": {
                        "semantic_contract": {"spec_declaration": "Packet.claimSpec"}
                    }
                }
            }
            with mock.patch.object(
                review_surface_owner,
                "source_semantic_input_bundle",
                return_value=(source_text, bundle_digest, ""),
            ):
                rows = review_surface_owner.current_v11_screening_rows(
                    paper_dir,
                    source_map,
                    {"Packet.claimSpec": target},
                )
                self.assertTrue(rows["Packet.claimSpec"]["current"])
                # Derived coverage diagnostics can change when a separately
                # reviewed prerequisite changes, without changing this Spec.
                target["review_claim_manifest_sha256"] = "f" * 64
                target["review_claim_atoms_sha256"] = "0" * 64
                rows = review_surface_owner.current_v11_screening_rows(
                    paper_dir, source_map, {"Packet.claimSpec": target},
                )
                self.assertTrue(rows["Packet.claimSpec"]["current"])
                # A different expanded theorem must still hide the old review.
                target["display_sha256"] = "1" * 64
                changed_rows = review_surface_owner.current_v11_screening_rows(
                    paper_dir, source_map, {"Packet.claimSpec": target},
                )
                self.assertFalse(changed_rows["Packet.claimSpec"]["current"])
        self.assertTrue(rows["Packet.claimSpec"]["current"])
        self.assertIn(
            "has not prepared",
            review_surface_owner._v11_packet_surface_error(
                {"review_surface": {"require_v11_raw_source_spec_screening": True}},
                {},
            ),
        )
        self.assertEqual(
            review_surface_owner._v11_packet_surface_error(
                {"review_surface": {"require_source_spec_correspondence": True}},
                {"semantic_contract_schema": 1},
            ),
            "",
        )

    def test_pending_review_notice_is_front_matter_only(self) -> None:
        self.assertIn(
            "0/2 source-claim screens; 0/1 paper-prerequisite screens; "
            "1/3 library prerequisite screens",
            renderer._review_readiness_notice(
                [{"llm_match_current": False}, {"llm_match_current": False}],
                [{"semantic_current": False}],
                [
                    {"semantic_current": True},
                    {"semantic_current": False},
                    {"semantic_current": False},
                ],
            ),
        )
        self.assertEqual(
            renderer._review_readiness_notice(
                [{"llm_match_current": True}],
                [{"semantic_current": True}],
                [{"semantic_current": True}],
            ),
            "",
        )

    def test_public_arxiv_tex_source_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "PacketPaper"
            (paper_dir / "audit").mkdir(parents=True)
            source_bytes = b"\\begin{document}official source\\end{document}\n"
            (paper_dir / "source").mkdir()
            (paper_dir / "source" / "main.tex").write_bytes(source_bytes)
            (paper_dir / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://arxiv.org/abs/2601.00001v1",
                        "source_artifact_path": "source/main.tex",
                        "source_artifact_sha256": hashlib.sha256(source_bytes).hexdigest(),
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root):
                self.assertEqual(packet.public_arxiv_tex_source_error("PacketPaper"), "")

    def test_non_arxiv_source_is_not_a_public_excerpt_exception(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "PacketPaper"
            (paper_dir / "audit").mkdir(parents=True)
            (paper_dir / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://doi.org/10.1000/example",
                        "source_artifact_path": "source/main.tex",
                        "source_artifact_sha256": "a" * 64,
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.multiple(packet, ROOT=root), mock.patch.object(review_surface_owner, "ROOT", root):
                self.assertIn(
                    "official arXiv", packet.public_arxiv_tex_source_error("PacketPaper")
                )

    def test_source_anchor_accepts_safe_repository_relative_paper_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "PacketPaper"
            source = paper_dir / "source" / "main.tex"
            source.parent.mkdir(parents=True)
            source.write_text("exact source line\n", encoding="utf-8")
            record = {
                "source_anchor_evidence": [
                    {
                        "path": "papers/PacketPaper/source/main.tex",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": "exact source line",
                    }
                ]
            }
            with mock.patch.object(review_dashboard, "ROOT", root):
                self.assertEqual(
                    review_dashboard.source_anchor_file_error(paper_dir, record),
                    "",
                )

    def test_packet_uses_one_source_and_one_interface_block(self) -> None:
        record = {
            "source_item": "Theorem 1",
            "source_location": "source/main.tex:1-2",
            "statement": "The source statement.",
            "source_anchor_evidence": [{"quoted_text": "Exact source text."}],
        }
        row = renderer._row_tex(
            {
                "name": "endpoint",
                "kind": "theorem",
                "full_name": "Paper.endpoint",
                "interface_source": "theorem endpoint : P := by exact h",
                "lean_statement": "def endpointSpec : Prop := P",
                "verbatim_source_input": "Exact source text.",
                "agent_statement": "P.",
                "llm_match_judgment": "match",
                "llm_match_reason": "Same conclusion.",
            },
            [record],
            "Paper.endpoint",
            1,
        )
        self.assertIn("Verbatim source input", row)
        self.assertIn("Expanded PaperInterface specification", row)
        self.assertIn("Exact source text.", row)
        self.assertNotIn("The source statement.", row)
        self.assertNotIn("\\textbf{Kind:}", row)

    def test_presentation_sections_reorder_cards_without_dropping_any(self) -> None:
        main = ({"full_name": "Paper.mainSpec"}, [], "Paper.main_realizes_spec")
        appendix = ({"full_name": "Paper.appendixSpec"}, [], "Paper.appendix_realizes_spec")
        grouped = review_surface_owner._claim_presentation_sections(
            {
                "review_surface": {
                    "presentation_sections": [
                        {"title": "Main-text source claims", "names": ["main"]},
                        {"title": "Appendix source claims", "names": ["appendix"]},
                    ]
                }
            },
            [main, appendix],
        )
        self.assertEqual(
            [(title, [row[0]["full_name"] for row in rows]) for title, rows in grouped],
            [
                ("Main-text source claims", ["Paper.mainSpec"]),
                ("Appendix source claims", ["Paper.appendixSpec"]),
            ],
        )

    def test_packet_and_browser_section_source_separates_assumptions(self) -> None:
        claim = ({"full_name": "Paper.mainSpec"}, (), "Paper.main")
        assumption = (
            {
                "full_name": "Paper.sourceConditionSpec",
                "is_assumption": True,
            },
            (),
            "Paper.sourceCondition",
        )
        grouped = review_surface_owner._claim_presentation_sections(
            {
                "review_surface": {
                    "presentation_sections": [
                        {"title": "Main-text source claims", "names": ["main"]}
                    ]
                }
            },
            [claim, assumption],
        )

        self.assertEqual(
            [
                (title, [row[0]["full_name"] for row in rows])
                for title, rows in grouped
            ],
            [
                ("Main-text source claims", ["Paper.mainSpec"]),
                ("Source-model assumptions", ["Paper.sourceConditionSpec"]),
            ],
        )
    def test_packet_contents_links_prerequisites_and_source_claims(self) -> None:
        claim = ({"full_name": "Paper.mainSpec", "name": "mainSpec"}, [{"source_item": "Theorem 1"}], "Paper.main")
        contents = renderer._contents_tex(
            Path("/tmp/PacketPaper"),
            [("Main-text source claims", [claim])],
            [
                {
                    "lean_name": "Paper.Model",
                    "direct_paper_declarations": [],
                }
            ],
            [{"lean_name": "AppliedModelingLib.Model", "direct_library_declarations": []}],
        )
        self.assertIn("Semantic library prerequisites (1; not paper claims)", contents)
        self.assertIn("Paper-specific semantic prerequisites (1; not paper claims)", contents)
        self.assertIn("Main-text source claims (1)", contents)
        self.assertIn("Theorem 1", contents)
        self.assertIn("\\hyperlink{", contents)
        self.assertIn("Paper.\\allowbreak{}Model", contents)
        self.assertIn("AppliedModelingLib.Model", contents.replace(r"\allowbreak{}", ""))

    def test_packet_compile_rejects_missing_exact_glyph(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            tex_path = Path(temp_dir) / "HUMAN_REVIEW_PACKET.tex"
            tex_path.write_text("fixture\n", encoding="utf-8")
            tex_path.with_suffix(".log").write_text(
                "Missing character: There is no ∖ (U+2216) in font Fixture!\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    packet.subprocess,
                    "run",
                    return_value=SimpleNamespace(returncode=0),
                ),
                self.assertRaisesRegex(RuntimeError, "omitted one or more exact"),
            ):
                packet._compile(tex_path)

    def test_presentation_sections_preserve_dag_order_with_continued_heading(self) -> None:
        main = ({"full_name": "Paper.mainSpec"}, [], "Paper.main_realizes_spec")
        appendix = ({"full_name": "Paper.appendixSpec"}, [], "Paper.appendix_realizes_spec")
        grouped = review_surface_owner._claim_presentation_sections(
            {
                "review_surface": {
                    "presentation_sections": [
                        {"title": "Main-text source claims", "names": ["main"]},
                        {"title": "Appendix source claims", "names": ["appendix"]},
                    ]
                }
            },
            [appendix, main],
        )
        self.assertEqual(
            [(title, [row[0]["full_name"] for row in rows]) for title, rows in grouped],
            [
                ("Appendix source claims", ["Paper.appendixSpec"]),
                ("Main-text source claims", ["Paper.mainSpec"]),
            ],
        )

    def test_claim_rows_coalesce_spec_and_proof_in_intake_order(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            (paper_dir / "audit").mkdir()
            (paper_dir / "audit" / "intake_freeze.json").write_text(
                json.dumps(
                    {
                        "items": [
                            {
                                "spec_declaration": "secondSpec",
                                "proof_declaration": "second",
                                "dependency_order": 2,
                            },
                            {
                                "spec_declaration": "firstSpec",
                                "proof_declaration": "first",
                                "dependency_order": 1,
                            },
                        ]
                    }
                ),
                encoding="utf-8",
            )
            source_map = {
                "items": {
                    "second": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.secondSpec",
                            "evidence_declaration": "Packet.second",
                        }
                    },
                    "first": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.firstSpec",
                            "evidence_declaration": "Packet.first",
                        }
                    },
                }
            }
            dashboard_items = [
                {"full_name": "Packet.firstSpec", "name": "firstSpec"},
                {"full_name": "Packet.first", "name": "first"},
                {"full_name": "Packet.secondSpec", "name": "secondSpec"},
                {"full_name": "Packet.second", "name": "second"},
            ]
            selected = review_surface_owner._claim_review_rows(paper_dir, source_map, dashboard_items)

        self.assertEqual(
            [(item["full_name"], proof) for item, _records, proof in selected],
            [("Packet.firstSpec", "Packet.first"), ("Packet.secondSpec", "Packet.second")],
        )

    def test_claim_rows_use_review_surface_order_without_intake_freeze(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            (paper_dir / "audit").mkdir()
            (paper_dir / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["firstSpec", "secondSpec"]
                        }
                    }
                ),
                encoding="utf-8",
            )
            source_map = {
                "items": {
                    "second": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.secondSpec",
                            "evidence_declaration": "Packet.second",
                        }
                    },
                    "first": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.firstSpec",
                            "evidence_declaration": "Packet.first",
                        }
                    },
                }
            }
            dashboard_items = [
                {"full_name": "Packet.firstSpec", "name": "firstSpec"},
                {"full_name": "Packet.secondSpec", "name": "secondSpec"},
            ]
            selected = review_surface_owner._claim_review_rows(paper_dir, source_map, dashboard_items)

        self.assertEqual(
            [(item["full_name"], proof) for item, _records, proof in selected],
            [("Packet.firstSpec", "Packet.first"), ("Packet.secondSpec", "Packet.second")],
        )

    def test_v11_claim_rows_exclude_unrouted_helpers_and_assumptions(self) -> None:
        """The packet remains source-contract claim-only despite dashboard assumption cards."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            source_map = {
                "semantic_contract_schema": 1,
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.claimSpec",
                            "evidence_declaration": "Packet.claim",
                        }
                    }
                },
            }
            dashboard_items = [
                {"full_name": "Packet.claimSpec", "name": "claimSpec"},
                {"full_name": "Packet.helperSpec", "name": "helperSpec"},
                {
                    "full_name": "Packet.modelAssumption",
                    "name": "modelAssumption",
                    "is_assumption": True,
                },
            ]
            selected = review_surface_owner._claim_review_rows(paper_dir, source_map, dashboard_items)

        self.assertEqual(
            [(item["full_name"], proof) for item, _records, proof in selected],
            [("Packet.claimSpec", "Packet.claim")],
        )

    def test_role_typed_definition_never_falls_back_to_a_claim_row(self) -> None:
        """A definition is a prerequisite card, not a theorem-denominator row."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Packet"
            paper_dir.mkdir()
            source_map = {
                "paper": "Packet",
                "semantic_route_schema": 2,
                "items": {
                    "model": {
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                        "lean_declarations": ["Packet.Model"],
                    },
                    "claim": {
                        "source_kind": "theorem",
                        "semantic_contract": {
                            "spec_declaration": "Packet.claimSpec",
                            "evidence_declaration": "Packet.claim",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    },
                },
            }
            dashboard_items = [
                {"full_name": "Packet.Model", "name": "Model"},
                {"full_name": "Packet.claimSpec", "name": "claimSpec"},
                {"full_name": "Packet.claim", "name": "claim"},
            ]
            selected = review_surface_owner._claim_review_rows(
                paper_dir,
                source_map,
                dashboard_items,
            )

        self.assertEqual(
            [(item["full_name"], proof) for item, _records, proof in selected],
            [("Packet.claimSpec", "Packet.claim")],
        )

    def test_role_typed_claim_rows_do_not_require_parser_items(self) -> None:
        """Typed routes, not a Python declaration parser, select v11 Specs."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "Packet"
            paper_dir.mkdir()
            source_map = {
                "paper": "Packet",
                "semantic_route_schema": 2,
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "semantic_contract": {
                            "spec_declaration": "Packet.claimSpec",
                            "evidence_declaration": "Packet.claim",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    },
                },
            }
            selected = review_surface_owner._claim_review_rows(paper_dir, source_map, {})

        self.assertEqual(
            [(item["full_name"], proof) for item, _records, proof in selected],
            [("Packet.claimSpec", "Packet.claim")],
        )

    @mock.patch.object(
        review_dashboard,
        "paper_statement_map_payload",
        new=lambda _folder: {"items": {}},
    )
    def test_prerequisites_show_exact_library_definition_and_source_connection(self) -> None:
        entries = review_surface_owner._prepared_library_prerequisites(
            packet.ROOT / "papers" / "HT26EFXChores",
            [
                {
                    "interface_source": (
                        "AppliedModelingLib.FairDivision.Bundle Item → "
                        "AppliedModelingLib.FairDivision.Allocation Agent Item"
                    )
                }
            ],
            semantic_targets_override={
                "AppliedModelingLib.FairDivision.Bundle": {
                    "display": "abbrev AppliedModelingLib.FairDivision.Bundle (Item : Type*) := Finset Item",
                    "declaration_kind": "abbrev",
                    "direct_library_declarations": (),
                    "review_owner_declaration": "AppliedModelingLib.FairDivision.Bundle",
                    "source_module": (
                        "AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods"
                    ),
                    "source_line_start": 17,
                    "source_column_start": 0,
                    "source_line_end": 18,
                    "source_column_end": 43,
                },
                "AppliedModelingLib.FairDivision.Allocation": {
                    "display": "abbrev AppliedModelingLib.FairDivision.Allocation (Agent Item : Type*) := Agent → AppliedModelingLib.FairDivision.Bundle Item",
                    "declaration_kind": "abbrev",
                    "direct_library_declarations": (),
                    "review_owner_declaration": "AppliedModelingLib.FairDivision.Allocation",
                    "source_module": (
                        "AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods"
                    ),
                    "source_line_start": 20,
                    "source_column_start": 0,
                    "source_line_end": 21,
                    "source_column_end": 61,
                },
            },
            semantic_target_errors_override={},
            source_map_payload={"items": {}},
        )

        rendered = renderer._prerequisites_tex(Path("Fixture"), entries)
        self.assertIn("Material library prerequisites", rendered)
        self.assertIn("Lean-expanded library semantic target", rendered)
        self.assertIn("Exact Lean library declaration", rendered)
        self.assertGreaterEqual(rendered.count(r"\clearpage"), 1)
        self.assertIn(r"\hypertarget{library-prerequisite-", rendered)
        self.assertIn("abbrev Bundle (Item : Type*) := Finset Item", rendered)
        self.assertIn("abbrev Allocation (Agent Item : Type*) := Agent → Bundle Item", rendered)
        self.assertNotIn("the same byte-pinned source bundle shown for", rendered)
        self.assertIn(r"\textbf{Verdict:} \texttt{", rendered)
        self.assertNotIn(r"\textbf{Status:}", rendered)
        self.assertIn(r"\reviewmatch", rendered)
        self.assertIn(r"\textbf{Reviewer annotation}", rendered)

    def test_reviewer_reasons_wrap_identifiers_without_changing_text(self) -> None:
        reason = (
            "Packet.Very_long_identifier.matches_source at "
            "papers/Packet/source/long_source_filename.tex:141-149; "
            "retains 100% of the claim & its assumptions."
        )
        prerequisite = {
            "lean_name": "Packet.Model",
            "label": "Model",
            "semantic_judgment": "matches",
            "semantic_reason": reason,
        }
        rendered_routes = {
            "result": renderer._row_tex(
                {"llm_match_judgment": "matches", "llm_match_reason": reason},
                [], "Packet.claim", 1,
            ),
            "paper prerequisite": renderer._paper_prerequisites_tex([prerequisite]),
            "library prerequisite": renderer._prerequisites_tex(
                Path("Packet"), [prerequisite],
            ),
        }
        for route, rendered in rendered_routes.items():
            with self.subTest(route=route):
                rendered_reason = rendered.split(r"\textbf{Reason:} ", 1)[1].splitlines()[0]
                self.assertIn(
                    "{\\raggedright\n\\textbf{Reason:} " + rendered_reason + "\n\\par}",
                    rendered,
                )
                self.assertEqual(
                    rendered_reason.replace(r"\allowbreak{}", ""),
                    renderer._tex_escape(reason),
                )
                for separator in ("/", ":", "-", ";", ".", r"\_"):
                    self.assertIn(separator + r"\allowbreak{}", rendered_reason)

    def test_paper_prerequisite_shows_one_expanded_semantic_target(self) -> None:
        rendered = renderer._paper_prerequisites_tex(
            [
                {
                    "lean_name": "Packet.Model",
                    "verbatim_source_input": "The model is finite.",
                    "source_locator": "source/main.tex:1",
                    "paper_semantic_target": "def Packet.Model := Fin 2",
                    "paper_semantic_target_kind": "definition",
                    "paper_declaration_source": "def Model := Fin 2",
                    "semantic_judgment": "matches",
                    "semantic_reason": "The source names the finite model.",
                }
            ]
        )

        self.assertIn("Verbatim paper-source connection", rendered)
        self.assertIn("Lean-expanded paper semantic target", rendered)
        self.assertIn("def Packet.Model := Fin 2", rendered)
        self.assertNotIn("Exact Lean paper declaration", rendered)
        self.assertNotIn("def Model := Fin 2", rendered)

    def test_prerequisite_cards_are_dependency_first(self) -> None:
        entries = [
            {"lean_name": "Packet.ClaimModel", "direct_paper_declarations": ["Packet.BaseModel"]},
            {"lean_name": "Packet.BaseModel", "direct_paper_declarations": []},
        ]
        ordered = review_surface_owner._dependency_first_entries(
            entries,
            name_field="lean_name",
            dependency_field="direct_paper_declarations",
        )
        self.assertEqual(
            [entry["lean_name"] for entry in ordered],
            ["Packet.BaseModel", "Packet.ClaimModel"],
        )

    def test_prerequisite_order_rejects_duplicate_cards(self) -> None:
        entries = [
            {"lean_name": "Packet.Model", "direct_paper_declarations": []},
            {"lean_name": "Packet.Model", "direct_paper_declarations": []},
        ]
        with self.assertRaisesRegex(ValueError, "repeat Lean declarations"):
            review_surface_owner._dependency_first_entries(
                entries,
                name_field="lean_name",
                dependency_field="direct_paper_declarations",
            )

    def test_prerequisite_order_rejects_a_dependency_cycle(self) -> None:
        entries = [
            {
                "lean_name": "Packet.Left",
                "direct_paper_declarations": ["Packet.Right"],
            },
            {
                "lean_name": "Packet.Right",
                "direct_paper_declarations": ["Packet.Left"],
            },
        ]
        with self.assertRaisesRegex(ValueError, "contains a cycle"):
            review_surface_owner._dependency_first_entries(
                entries,
                name_field="lean_name",
                dependency_field="direct_paper_declarations",
            )

    def test_governing_projection_deduplicates_and_links_reviewed_roots(self) -> None:
        def target(display: str, **extra: object) -> dict[str, object]:
            return {
                "display": display,
                "display_sha256": hashlib.sha256(display.encode()).hexdigest(),
                **extra,
            }

        result_targets = {
            "Packet.claimSpec": {
                "prerequisite_declarations": ["Packet.Root"],
                "library_declarations": ["AppliedModelingLib.Root"],
            }
        }
        paper_targets = {
            "Packet.Root": target(
                "def Root := Shared",
                direct_paper_declarations=["Packet.Shared"],
                direct_library_declarations=["AppliedModelingLib.Shared"],
            ),
            "Packet.Shared": target(
                "def Shared : Prop := True",
                direct_paper_declarations=[],
                direct_library_declarations=[],
            ),
            "Packet.ExplicitReviewRoot": target(
                "def ExplicitReviewRoot := Shared",
                direct_paper_declarations=["Packet.Shared"],
                direct_library_declarations=[],
            ),
        }
        library_targets = {
            "AppliedModelingLib.Root": target(
                "def Root := Shared",
                direct_library_declarations=["AppliedModelingLib.Shared"],
            ),
            "AppliedModelingLib.Shared": target(
                "def Shared : Prop := True",
                direct_library_declarations=[],
            ),
            "AppliedModelingLib.ExplicitReviewRoot": target(
                "def ExplicitReviewRoot := Shared",
                direct_library_declarations=["AppliedModelingLib.Shared"],
            ),
        }

        entries, result_links, declaration_links = (
            review_surface_owner._governing_declaration_projection(
                result_targets,
                paper_targets,
                library_targets,
                reviewed_paper_declarations=[
                    "Packet.Root",
                    "Packet.ExplicitReviewRoot",
                ],
                reviewed_library_declarations=[
                    "AppliedModelingLib.ExplicitReviewRoot"
                ],
            )
        )

        self.assertEqual(
            [entry["lean_name"] for entry in entries],
            [
                "AppliedModelingLib.Shared",
                "AppliedModelingLib.Root",
                "Packet.Shared",
            ],
        )
        self.assertEqual(
            result_links["Packet.claimSpec"],
            [
                {
                    "lean_name": "AppliedModelingLib.Root",
                    "anchor_kind": "governing-declaration",
                },
                {"lean_name": "Packet.Root", "anchor_kind": "paper-prerequisite"},
            ],
        )
        self.assertEqual(
            declaration_links["Packet.Root"],
            [
                {
                    "lean_name": "AppliedModelingLib.Shared",
                    "anchor_kind": "governing-declaration",
                },
                {
                    "lean_name": "Packet.Shared",
                    "anchor_kind": "governing-declaration",
                },
            ],
        )
        self.assertEqual(
            declaration_links["Packet.ExplicitReviewRoot"],
            [
                {
                    "lean_name": "Packet.Shared",
                    "anchor_kind": "governing-declaration",
                }
            ],
        )
        self.assertEqual(
            declaration_links["AppliedModelingLib.ExplicitReviewRoot"],
            [
                {
                    "lean_name": "AppliedModelingLib.Shared",
                    "anchor_kind": "governing-declaration",
                }
            ],
        )
        self.assertEqual(
            sum(
                entry["lean_name"] == "AppliedModelingLib.Shared"
                for entry in entries
            ),
            1,
        )

    def test_governing_projection_fails_closed_on_missing_display_and_cycles(self) -> None:
        display = "def Left := Right"
        left = {
            "display": display,
            "display_sha256": hashlib.sha256(display.encode()).hexdigest(),
            "direct_paper_declarations": ["Packet.Right"],
            "direct_library_declarations": [],
        }
        semantic = {
            "Packet.claimSpec": {
                "prerequisite_declarations": ["Packet.Left"],
                "library_declarations": [],
            }
        }
        with self.assertRaisesRegex(ValueError, "display is unavailable"):
            review_surface_owner._governing_declaration_projection(
                semantic, {"Packet.Left": left}, {}
            )

        right_display = "def Right := Left"
        right = {
            "display": right_display,
            "display_sha256": hashlib.sha256(right_display.encode()).hexdigest(),
            "direct_paper_declarations": ["Packet.Left"],
            "direct_library_declarations": [],
        }
        with self.assertRaisesRegex(ValueError, "contains a cycle"):
            review_surface_owner._governing_declaration_projection(
                semantic, {"Packet.Left": left, "Packet.Right": right}, {}
            )

    def test_packet_renderers_consume_prepared_prerequisite_order(self) -> None:
        library = [{"lean_name": "AppliedModelingLib.Model", "label": "Model"}]
        paper = [{"lean_name": "Packet.Model"}]
        with mock.patch.object(
            review_surface_owner,
            "_dependency_first_entries",
            side_effect=AssertionError("renderer repeated dependency ordering"),
        ):
            renderer._contents_tex(Path("Packet"), (), paper, library)
            renderer._prerequisites_tex(
                Path("Packet"), library
            )
            renderer._paper_prerequisites_tex(paper)

    def test_corrected_source_target_is_visible_and_not_a_raw_match(self) -> None:
        record = {
            "source_location": "source/main.tex:1-2",
            "source_anchor_evidence": [{"quoted_text": "False archival text."}],
            "coverage_status": "corrected_source_statement",
            "corrected_target": {
                "statement": "The approved corrected proposition.",
                "archival_source_locator": "source/main.tex:1-2",
                "approval": {
                    "reference": (
                        "Repository user approved the correction in "
                        "docs/PRIVATE_APPROVAL_RECORD.md."
                    )
                },
            },
        }
        row = renderer._row_tex(
            {
                "verbatim_source_input": "False archival text.",
                "semantic_expanded_statement": "def claimSpec : Prop := True",
                "llm_match_judgment": "matches_approved_corrected_target",
                "llm_match_reason": "The corrected target matches the Spec.",
            },
            [record],
            "Paper.claim",
            1,
        )
        self.assertIn("Formalized review target", row)
        self.assertIn("The approved corrected proposition.", row)
        self.assertNotIn("Recorded basis", row)
        self.assertNotIn("Repository user approved", row)
        self.assertNotIn("PRIVATE_APPROVAL_RECORD", row)
        self.assertIn("Matches formalized target", row)
        self.assertNotIn("\\reviewmatch{Matches source input}", row)

    def test_corrected_library_prerequisite_context_is_identity_bound(self) -> None:
        corrected_target = {
            "schema": 1,
            "statement": "Each nonempty round has an error strictly between zero and one.",
            "archival_equivalence_claimed": False,
            "archival_source_locator": "source/main.tex:10-12",
        }
        digest = review_surface_owner.corrected_target_review_digest(
            corrected_target
        )
        corrected_target["corrected_target_review_sha256"] = digest
        source_items = {
            "algorithm": {
                "coverage_status": "corrected_source_statement",
                "corrected_target": corrected_target,
            }
        }
        entry = {
            "lean_name": "Library.Algorithm",
            "source_item": "algorithm",
            "source_locator": "source/main.tex:10-12",
            "verbatim_source_input": "The archival algorithm text.",
            "library_semantic_target": "type: Prop; value: True",
            "library_semantic_target_kind": "definition",
            "library_definition": "def Algorithm : Prop := True",
            "semantic_judgment": "matches_approved_corrected_target",
            "semantic_reason": "The formalized target matches the declaration.",
            "semantic_current": True,
            "corrected_target_review_sha256": digest,
        }
        review_surface_owner._attach_identity_bound_prerequisite_contexts(
            [entry], source_items
        )
        rendered = renderer._prerequisites_tex(Path("Fixture"), [entry])
        self.assertIn("Formalized review target", rendered)
        self.assertIn(corrected_target["statement"], rendered)
        self.assertIn("matches\\_approved\\_corrected\\_target", rendered)
        self.assertIn("Matches formalized target", rendered)
        self.assertIn("Exact Lean library declaration", rendered)

        accepted_only = {key: value for key, value in entry.items()}
        review_surface_owner._attach_recorded_graph_prerequisite_contexts(
            [accepted_only], {"items": source_items}
        )
        self.assertEqual(accepted_only["corrected_target"], corrected_target)

        historical_matches = {
            **entry,
            "semantic_judgment": "matches",
        }
        historical_matches.pop("corrected_target", None)
        historical_matches.pop("corrected_target_required", None)
        review_surface_owner._attach_recorded_graph_prerequisite_contexts(
            [historical_matches], {"items": source_items}
        )
        self.assertNotIn("corrected_target", historical_matches)
        self.assertNotIn("corrected_target_required", historical_matches)

        forged = dict(entry)
        forged.pop("corrected_target", None)
        forged.pop("coverage_status", None)
        forged["corrected_target_review_sha256"] = "0" * 64
        review_surface_owner._attach_identity_bound_prerequisite_contexts(
            [forged], source_items
        )
        with self.assertRaisesRegex(ValueError, "identity-bound formalized review target"):
            renderer._prerequisites_tex(Path("Fixture"), [forged])

    def test_settled_source_reading_is_visible_beside_raw_source(self) -> None:
        context = {
            "kind": "source_model_convention",
            "id": "FIXTURE-CALENDAR-01",
            "report_summary": "Old semantic-record wording.",
        }
        presentation = ReportContextPresentation(
            paper="Fixture",
            summaries_by_id={
                "FIXTURE-CALENDAR-01": (
                    "An incident born before the interval may first report inside it."
                )
            },
            presentation_sha256="a" * 64,
        )
        row = renderer._row_tex(
            {
                "verbatim_source_input": "Raw archival statement.",
                "semantic_expanded_statement": "def claimSpec : Prop := True",
                "approved_review_contexts": [context],
                "approved_review_context_presentation": row_context_presentation(
                    [context], presentation
                ),
            },
            [{"source_location": "source/main.tex:1"}],
            "Paper.claim",
            1,
        )
        self.assertLess(row.index("Raw archival statement."), row.index("Settled source reading"))
        self.assertIn("An incident born before the interval", row)
        self.assertNotIn("Old semantic-record wording", row)


class RecordedPacketProjectionTests(unittest.TestCase):
    def setUp(self) -> None:
        def target(display: str) -> dict[str, str]:
            return {"display": display, "display_sha256": hashlib.sha256(display.encode()).hexdigest()}

        self.cache = {
            "schema": review_surface_owner.PACKET_LEAN_CACHE_SCHEMA,
            "paper": "Fixture",
            "specifications": ["Fixture.claimSpec"],
            "semantic_targets": {"Fixture.claimSpec": target("True")},
            "paper_prerequisite_targets": {
                "Fixture.Model": target("def model := True"),
                "Fixture.helper": target("def helper := True"),
            },
            "paper_prerequisite_supporting_declarations_sha256": {
                "Fixture.Model": "", "Fixture.helper": ""
            },
            "paper_semantic_review_targets": {},
            "paper_semantic_review_supporting_declarations_sha256": {},
            "library_semantic_targets": {"Library.Model": target("def library := True")},
            "library_semantic_target_errors": {},
            "library_declaration_sources": {
                "Library.Model": {
                    "library_definition": "def library := True",
                    "library_definition_sha256": hashlib.sha256(b"def library := True").hexdigest(),
                    "library_source_path": "Library.lean",
                }
            },
        }
        self.projection = SimpleNamespace(
            reviewed_display_surface_complete=True,
            claim_semantic_target_sha256s_by_specification={
                "Fixture.claimSpec": self.cache["semantic_targets"]["Fixture.claimSpec"]["display_sha256"]
            },
            prerequisite_semantic_target_sha256s_by_declaration={
                name: self.cache[field][name]["display_sha256"]
                for field, name in [
                    ("paper_prerequisite_targets", "Fixture.Model"),
                    ("library_semantic_targets", "Library.Model"),
                ]
            },
            card_review_declarations_by_source_item={
                "claim": ("Fixture.claimSpec",),
                "model": ("Fixture.Model",),
                "library": ("Library.Model",),
            },
        )

    def is_current(self) -> bool:
        return review_surface_owner._recorded_graph_packet_cache_current(
            self.cache, self.cache["specifications"], self.projection
        )

    def test_source_context_check_covers_results_and_both_prerequisite_locations(self) -> None:
        def record(text: str) -> dict:
            return {"source_anchor_evidence": [{
                "quoted_text": text,
                "quoted_text_sha256": hashlib.sha256(text.encode()).hexdigest(),
            }]}

        items = {key: record(key) for key in ("claim", "model", "library")}
        self.projection.source_input_bundle_sha256s_by_source_item = {
            key: review_dashboard.source_semantic_input_bundle(
                value, require_context_roles=True
            )[1] for key, value in items.items()
        }
        self.assertTrue(review_surface_owner._recorded_graph_source_cards_current({"items": items}, self.projection))
        for key in items:
            with self.subTest(source_card=key):
                changed = {**items, key: record("Changed " + key)}
                self.assertFalse(review_surface_owner._recorded_graph_source_cards_current(
                    {"items": changed}, self.projection
                ))
                missing = {name: value for name, value in items.items() if name != key}
                self.assertFalse(review_surface_owner._recorded_graph_source_cards_current(
                    {"items": missing}, self.projection
                ))
                malformed = {**items, key: {**items[key], "semantic_context_requirements": [{
                    "semantic_role": "not_a_permitted_role",
                    "source_anchor_evidence": record("Context")["source_anchor_evidence"],
                }]}}
                self.assertFalse(review_surface_owner._recorded_graph_source_cards_current(
                    {"items": malformed}, self.projection
                ))

    def test_source_context_check_accepts_only_recorded_shared_atom_bundle(self) -> None:
        def record(text: str) -> dict:
            return {"source_anchor_evidence": [{
                "quoted_text": text,
                "quoted_text_sha256": hashlib.sha256(text.encode()).hexdigest(),
            }]}

        current = record("Current source card")
        current_digest = review_dashboard.source_semantic_input_bundle(
            current, require_context_roles=True
        )[1]
        other_digest = hashlib.sha256(b"Other reviewed source card").hexdigest()
        self.projection.card_review_declarations_by_source_item = {
            "claim": ("Fixture.claimSpec",)
        }
        self.projection.source_input_bundle_sha256s_by_source_item = {
            "claim": tuple(sorted((current_digest, other_digest)))
        }

        self.assertTrue(
            review_surface_owner._recorded_graph_source_cards_current(
                {"items": {"claim": current}}, self.projection
            )
        )
        self.assertFalse(
            review_surface_owner._recorded_graph_source_cards_current(
                {"items": {"claim": record("Unreviewed source card")}},
                self.projection,
            )
        )

    def test_extra_closure_helper_is_not_authorized_as_a_review_card(self) -> None:
        self.assertTrue(self.is_current())
        selected = review_surface_owner._recorded_graph_packet_cache_projection(self.cache, self.projection)
        self.assertEqual(set(selected["paper_prerequisite_targets"]), {"Fixture.Model"})
        self.assertEqual(set(selected["paper_semantic_review_targets"]), {"Fixture.Model"})
        self.assertNotIn("Fixture.helper", selected["paper_prerequisite_supporting_declarations_sha256"])
        self.assertIn("Fixture.helper", self.cache["paper_prerequisite_targets"])

    def test_every_reviewed_prerequisite_must_be_present(self) -> None:
        del self.cache["library_semantic_targets"]["Library.Model"]
        self.cache["library_declaration_sources"] = {}
        self.assertFalse(self.is_current())

    def test_changed_reviewed_prerequisite_digest_is_rejected(self) -> None:
        changed = self.cache["library_semantic_targets"]["Library.Model"]
        changed.update(display="False", display_sha256=hashlib.sha256(b"False").hexdigest())
        self.assertFalse(self.is_current())

    def test_missing_or_changed_reviewed_result_is_rejected(self) -> None:
        target = self.cache["semantic_targets"].pop("Fixture.claimSpec")
        self.assertFalse(self.is_current())
        self.cache["semantic_targets"]["Fixture.claimSpec"] = {
            **target, "display": "False", "display_sha256": hashlib.sha256(b"False").hexdigest()
        }
        self.assertFalse(self.is_current())

    def test_changed_display_protocol_is_not_ignored_by_graph_reader(self) -> None:
        self.cache["display_protocols"] = {**review_surface_owner._current_packet_display_protocols(), "spec_proposition": "changed"}
        self.assertFalse(self.is_current())

    def test_extra_helpers_do_not_authorize_prospective_transport(self) -> None:
        self.cache.update(
            paper_lean_tree_sha256="a" * 64,
            lean_display_engine_sha256="b" * 64,
            library_semantic_source_modules_sha256="c" * 64,
        )
        with (
            mock.patch.object(Path, "is_file", return_value=True),
            mock.patch.object(review_surface_owner, "_read_json", return_value=self.cache),
            mock.patch.object(review_surface_owner, "_paper_lean_tree_sha256", return_value="d" * 64),
            mock.patch.object(review_surface_owner, "_library_semantic_source_modules_sha256", return_value="c" * 64),
            mock.patch.object(review_surface_owner, "_recorded_graph_packet_projection", return_value=(True, self.projection)),
        ):
            self.assertIsNone(review_surface_owner._exact_current_packet_lean_cache_transport(
                Path("Fixture"), self.cache["specifications"]
            ))

    def test_graph_routes_own_cards_without_fresh_worksheet_maps(self) -> None:
        selected = review_surface_owner._recorded_graph_packet_cache_projection(self.cache, self.projection)
        self.projection.prerequisite_review_metadata_by_declaration = {
            "Fixture.Model": {"reason": "Recorded paper reason."},
            "Library.Model": {"reason": "Recorded library reason."},
        }
        source_map = {"semantic_route_schema": 2, "items": {
            "model": {"source_location": "source.tex:1"},
            "library": {"source_location": "source.tex:2"},
        }}
        with (
            mock.patch.object(review_surface_owner, "source_anchor_display_state", return_value=("local_source", "")),
            mock.patch.object(review_surface_owner, "source_semantic_input_bundle", return_value=("Exact source", "f" * 64, "")),
            mock.patch.object(review_surface_owner, "selected_paper_semantic_prerequisite_targets", side_effect=AssertionError("fresh selector")),
            mock.patch.object(review_surface_owner, "selected_library_semantic_prerequisite_targets", side_effect=AssertionError("fresh selector")),
            mock.patch.object(
                review_surface_owner,
                "_authenticated_recorded_prerequisite_row",
                side_effect=lambda _paper, _projection, *, location, **_kwargs: {
                    "judgment": "matches",
                    "library_definition_sha256": hashlib.sha256(
                        b"def library := True"
                    ).hexdigest(),
                }
                if location == "library"
                else {"judgment": "matches"},
            ),
            mock.patch.object(
                review_surface_owner,
                "_recorded_library_declaration_source",
                return_value={
                    "library_definition": "def library := True",
                    "library_definition_sha256": hashlib.sha256(
                        b"def library := True"
                    ).hexdigest(),
                    "library_definition_recorded_graph_authenticated": True,
                },
            ),
        ):
            paper, library = review_surface_owner._recorded_graph_prerequisite_cards(
                Path("Fixture"), source_map, selected, self.projection
            )
        self.assertEqual([(x["source_item"], x["lean_name"]) for x in paper], [("model", "Fixture.Model")])
        self.assertEqual([(x["source_item"], x["lean_name"]) for x in library], [("library", "Library.Model")])
        self.assertEqual(paper[0]["semantic_reason"], "Recorded paper reason.")
        self.assertEqual(library[0]["semantic_reason"], "Recorded library reason.")
        self.assertEqual(library[0]["library_definition"], "def library := True")
        self.assertTrue(
            library[0]["library_definition_recorded_graph_authenticated"]
        )

    def test_graph_card_still_checks_current_source_bytes(self) -> None:
        selected = review_surface_owner._recorded_graph_packet_cache_projection(self.cache, self.projection)
        with mock.patch.object(review_surface_owner, "source_anchor_display_state", return_value=("", "source bytes changed")):
            with self.assertRaisesRegex(ValueError, "source bytes changed"):
                review_surface_owner._recorded_graph_prerequisite_cards(
                    Path("Fixture"), {"items": {"model": {}}}, selected, self.projection
                )

    def test_recorded_library_source_uses_authenticated_row_and_exact_live_slice(
        self,
    ) -> None:
        definition = "/-- Exact model. -/\ndef library := True"
        definition_sha256 = hashlib.sha256(definition.encode()).hexdigest()
        target_sha256 = self.cache["library_semantic_targets"]["Library.Model"][
            "display_sha256"
        ]
        row = {
            "library_declaration": "Library.Model",
            "source_item": "library",
            "library_semantic_target_sha256": target_sha256,
            "library_semantic_target_protocol": (
                review_surface_owner.LIBRARY_SEMANTIC_TARGET_PROTOCOL
            ),
            "library_definition_sha256": definition_sha256,
            "library_source_path": "Library.lean",
            "library_line_start": 1,
            "library_line_end": 2,
            "judgment": "matches",
            "reason": "Authenticated reason.",
        }
        projection = SimpleNamespace(
            prerequisite_review_metadata_by_declaration={
                "Library.Model": {
                    "reason": "Authenticated reason.",
                    "_evidence_record_sha256": hashlib.sha256(
                        review_surface_owner.canonical_json_bytes(row)
                    ).hexdigest(),
                }
            }
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "Fixture"
            (paper_dir / "audit").mkdir(parents=True)
            source_path = root / "Library.lean"
            source_path.write_text(definition + "\n", encoding="utf-8")
            ledger_path = paper_dir / review_surface_owner.LIBRARY_SEMANTIC_REVIEW_NAME
            ledger_path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": "Fixture",
                        "items": {"Library.Model": row},
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(review_surface_owner, "ROOT", root):
                authenticated_row = (
                    review_surface_owner._authenticated_recorded_prerequisite_row(
                        paper_dir,
                        projection,
                        location="library",
                        declaration="Library.Model",
                        source_item="library",
                        semantic_target_sha256=target_sha256,
                    )
                )
                declaration_source = (
                    review_surface_owner._recorded_library_declaration_source(
                        "Library.Model", authenticated_row
                    )
                )
                self.assertEqual(
                    declaration_source["library_definition"], definition
                )
                self.assertTrue(
                    declaration_source[
                        "library_definition_recorded_graph_authenticated"
                    ]
                )

                source_path.write_text(
                    "/-- Exact model. -/\ndef library := False\n",
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    ValueError, "authenticated declaration digest"
                ):
                    review_surface_owner._recorded_library_declaration_source(
                        "Library.Model", authenticated_row
                    )

                forged_row = {
                    **row,
                    "library_definition_sha256": "0" * 64,
                    "library_source_path": "Changed.lean",
                }
                ledger_path.write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": "Fixture",
                            "items": {"Library.Model": forged_row},
                        }
                    ),
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    ValueError, "authenticated accepted-graph metadata"
                ):
                    review_surface_owner._authenticated_recorded_prerequisite_row(
                        paper_dir,
                        projection,
                        location="library",
                        declaration="Library.Model",
                        source_item="library",
                        semantic_target_sha256=target_sha256,
                    )

    def test_self_hashed_library_code_is_not_graph_authenticated_display(self) -> None:
        raw_source = self.cache["library_declaration_sources"]["Library.Model"]
        raw_source.update(
            library_definition="TAMPERED_SOURCE_CODE",
            library_definition_sha256=hashlib.sha256(b"TAMPERED_SOURCE_CODE").hexdigest(),
        )
        self.assertTrue(self.is_current())
        selected = review_surface_owner._recorded_graph_packet_cache_projection(self.cache, self.projection)
        self.assertNotIn("library_declaration_sources", selected)
        rendered = renderer._prerequisites_tex(Path("Fixture"), [{
            "lean_name": "Library.Model",
            "library_semantic_target": "type: Prop; value: True",
            "library_definition": "TAMPERED_SOURCE_CODE",
            "semantic_recorded_graph_sha256": "f" * 64,
        }])
        self.assertIn("type: Prop; value: True", rendered)
        self.assertIn("Lean-expanded library semantic target", rendered)
        self.assertNotIn("TAMPERED_SOURCE_CODE", rendered)
        self.assertNotIn("Exact Lean library declaration", rendered)

        authenticated = renderer._prerequisites_tex(Path("Fixture"), [{
            "lean_name": "Library.Model",
            "library_semantic_target": "type: Prop; value: True",
            "library_definition": "def library := True",
            "library_definition_recorded_graph_authenticated": True,
            "semantic_recorded_graph_sha256": "f" * 64,
        }])
        self.assertIn("Exact Lean library declaration", authenticated)
        self.assertIn("def library := True", authenticated)

    def test_recorded_library_source_relocates_one_authenticated_line_window(
        self,
    ) -> None:
        definition = "/-- Exact model. -/\ndef library := True"
        row = {
            "library_definition_sha256": hashlib.sha256(
                definition.encode()
            ).hexdigest(),
            "library_source_path": "Library.lean",
            "library_line_start": 1,
            "library_line_end": 2,
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "Library.lean").write_text(
                "-- Inserted line one.\n-- Inserted line two.\n"
                + definition
                + "\n",
                encoding="utf-8",
            )
            with mock.patch.object(review_surface_owner, "ROOT", root):
                source = review_surface_owner._recorded_library_declaration_source(
                    "Library.Model", row
                )
        self.assertEqual(source["library_definition"], definition)
        self.assertEqual(source["library_line_start"], 3)
        self.assertEqual(source["library_line_end"], 4)

    def test_recorded_library_source_rejects_duplicate_authenticated_windows(
        self,
    ) -> None:
        definition = "/-- Exact model. -/\ndef library := True"
        row = {
            "library_definition_sha256": hashlib.sha256(
                definition.encode()
            ).hexdigest(),
            "library_source_path": "Library.lean",
            "library_line_start": 1,
            "library_line_end": 2,
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "Library.lean").write_text(
                "-- Inserted line one.\n-- Inserted line two.\n"
                + definition
                + "\n\n"
                + definition
                + "\n",
                encoding="utf-8",
            )
            with mock.patch.object(review_surface_owner, "ROOT", root):
                with self.assertRaisesRegex(ValueError, "does not uniquely match"):
                    review_surface_owner._recorded_library_declaration_source(
                        "Library.Model", row
                    )
