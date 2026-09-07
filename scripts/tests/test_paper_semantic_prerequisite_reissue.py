"""Tests for dependency-routed paper-prerequisite decision templates."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from scripts.reissue_paper_semantic_prerequisites import (
    _current_projection_row,
    _unchanged_semantic_judgment,
    current_changed_decision_template_and_path,
    decision_template,
    reissue,
)
from scripts.semantic_prerequisite_projection import (
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    empty_paper_semantic_prerequisite_ledger,
)
from scripts.semantic_review_decision_queue import changed_only_template_surface


class PaperSemanticPrerequisiteDecisionTemplateTests(unittest.TestCase):
    def test_current_projection_uses_current_typed_source_route(self) -> None:
        row = _current_projection_row(
            {
                "source_item": "current_definition",
                "candidate_source_items": ["current_definition"],
                "judgment": "",
                "reason": "",
            },
            {
                "source_item": "stale_definition",
                "source_anchor_evidence": [{"path": "stale.txt"}],
                "judgment": "mismatch",
                "reason": "The old source route did not match.",
            },
        )

        self.assertEqual(row["source_item"], "current_definition")
        self.assertEqual(row["candidate_source_items"], ["current_definition"])
        self.assertNotIn("source_anchor_evidence", row)
        self.assertEqual(row["judgment"], "mismatch")

    def test_changed_only_emits_stable_lean_row_when_source_route_changes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Paper"
            (paper_dir / "audit").mkdir(parents=True)
            name = "Paper.Model"
            source_map = {
                "items": {
                    "old_definition": {
                        "source_kind": "definition",
                        "claim_bearing": True,
                    },
                    "current_definition": {
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                        "claim_bearing": True,
                        "lean_declarations": [name],
                    },
                },
                "paper_semantic_prerequisite_sources": {
                    name: "current_definition"
                },
            }
            prior = {
                "source_item": "old_definition",
                "paper_declaration": name,
                "paper_semantic_target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
                "paper_declaration_sha256": "a" * 64,
                "paper_semantic_target_sha256": "b" * 64,
                "elaborated_signature_sha256": "b" * 64,
                "source_input_bundle_sha256": "c" * 64,
                "judgment": "mismatch",
                "reason": "The old source route did not match.",
                "validator": "Reviewer",
                "validator_type": "llm_as_judge",
                "validated_at": "2026-08-26T00:00:00+00:00",
            }
            (paper_dir / "audit" / "paper_semantic_prerequisites.json").write_text(
                json.dumps({"items": {name: prior}}),
                encoding="utf-8",
            )

            def project(_paper_dir: Path, *, ledger: dict[str, object]):
                source_item = ledger["items"][name]["source_item"]
                self.assertEqual(source_item, "current_definition")
                return [
                    {
                        "lean_name": name,
                        "source_item": source_item,
                        "paper_declaration_source": "def Model : Prop := True",
                        "paper_declaration_sha256": "705a6d4e5cb05a900860c5926bc8b0a7d3e87344a04b67ad5f6be8811a3c972e",
                        "paper_semantic_target": "Prop",
                        "paper_semantic_target_sha256": "b" * 64,
                        "elaborated_signature_sha256": "b" * 64,
                        "source_input_bundle_sha256": "d" * 64,
                    }
                ]

            graph = SimpleNamespace(
                context=SimpleNamespace(statement_map=source_map),
                semantic_targets={},
                paper_prerequisite_targets={
                    name: {
                        "display": "Prop",
                        "display_sha256": "57d968860fabe1008d2c72342adec04b70f4bae48b7bcf6ebca915624100c353",
                        "direct_paper_declarations": [],
                    }
                },
                paper_declaration_sources={
                    name: {
                        "paper_declaration_source": "def Model : Prop := True",
                        "paper_declaration_sha256": "705a6d4e5cb05a900860c5926bc8b0a7d3e87344a04b67ad5f6be8811a3c972e",
                    }
                },
                project_paper_prerequisites=project,
            )
            with (
                patch(
                    "scripts.reissue_paper_semantic_prerequisites.review_queue.enrich_queue",
                    side_effect=lambda payload, **_kwargs: payload,
                ),
                patch(
                    "scripts.reissue_paper_semantic_prerequisites._content_addressed_queue_path",
                    return_value=paper_dir / "audit" / "changed.json",
                ),
            ):
                result = current_changed_decision_template_and_path(
                    paper_dir,
                    review_graph=graph,
                )

        self.assertIsNotNone(result)
        payload, _path = result
        self.assertEqual(set(payload["items"]), {name})
        self.assertEqual(payload["items"][name]["source_item"], "current_definition")
        self.assertEqual(payload["items"][name]["judgment"], "")

    def test_reissue_materializes_lean_proved_empty_surface(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Paper"
            paper_dir.mkdir(parents=True)
            graph = SimpleNamespace(
                context=SimpleNamespace(statement_map={"items": {}}),
                semantic_targets={},
                paper_prerequisite_targets={},
                project_paper_prerequisites=lambda *_args, **_kwargs: self.fail(
                    "empty surfaces need no row projection"
                ),
            )

            payload = reissue(
                paper_dir,
                {},
                validator="",
                review_graph=graph,
            )

        self.assertEqual(
            payload,
            empty_paper_semantic_prerequisite_ledger("Paper"),
        )

    def test_changed_only_reuses_only_exact_semantic_identities(self) -> None:
        current_entry = {
            "lean_name": "Paper.Stable",
            "elaborated_signature_sha256": "a" * 64,
            "source_input_bundle_sha256": "b" * 64,
        }
        prior = {
            "judgment": "matches",
            "reason": "The exact source and Lean target agree.",
            "validator": "Reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-26T00:00:00+00:00",
            "paper_semantic_target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
            "elaborated_signature_sha256": "a" * 64,
            "source_input_bundle_sha256": "b" * 64,
        }
        self.assertIsNotNone(_unchanged_semantic_judgment(prior, current_entry))

        # A changed route from archival source text to an approved corrected
        # mathematical target needs its own review.  The raw source bytes and
        # Lean declaration may be unchanged, but the reviewer-visible target
        # is not.
        self.assertIsNone(
            _unchanged_semantic_judgment(
                prior,
                {
                    **current_entry,
                    "corrected_target_review_sha256": "d" * 64,
                },
            )
        )

        supported_prior = {
            **prior,
            "semantic_supporting_declarations_sha256": "c" * 64,
        }
        supported_current = {
            **current_entry,
            "semantic_supporting_declarations_sha256": "c" * 64,
        }
        self.assertIsNotNone(
            _unchanged_semantic_judgment(supported_prior, supported_current)
        )
        self.assertIsNotNone(
            _unchanged_semantic_judgment(
                supported_prior,
                {
                    **supported_current,
                    "semantic_supporting_declarations_sha256": "d" * 64,
                },
            )
        )

        changed_entry = {
            **current_entry,
            "lean_name": "Paper.Changed",
            "elaborated_signature_sha256": "c" * 64,
        }
        payload, entries = changed_only_template_surface(
            {
                "items": {"Paper.Stable": {}, "Paper.Changed": {}},
                "unrouted_declarations": ["Paper.Stable", "Paper.Changed"],
            },
            [current_entry, changed_entry],
            {"Paper.Stable": prior, "Paper.Changed": prior},
            reusable_judgment=_unchanged_semantic_judgment,
        )
        self.assertEqual(set(payload["items"]), {"Paper.Changed"})
        self.assertEqual(payload["unrouted_declarations"], ["Paper.Changed"])
        self.assertEqual(
            [entry["lean_name"] for entry in entries], ["Paper.Changed"]
        )

    def test_template_selects_only_explicit_source_boundary_without_verdicts(self) -> None:
        source_map = {
            "semantic_route_schema": 2,
            "items": {
                "definition": {
                    "source_kind": "definition",
                    "inventory_role": "source_semantic_declaration",
                    "claim_bearing": True,
                    "lean_declarations": ["Paper.Model"],
                },
                "result": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "semantic_contract": {
                        "spec_declaration": "Paper.ResultSpec",
                        "evidence_declaration": "Paper.result",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                },
            },
            "paper_semantic_prerequisite_sources": {
                "Paper.Model": "definition"
            },
        }
        semantic_targets = {
            "Paper.ResultSpec": {
                "prerequisite_declarations": ["Paper.Carrier"],
            }
        }
        prerequisite_targets = {
            "Paper.Model": {
                "direct_paper_declarations": ["Paper.Shared"],
            },
            "Paper.Carrier": {
                "direct_paper_declarations": ["Paper.Shared"],
            },
            "Paper.Shared": {"direct_paper_declarations": []},
        }

        payload = decision_template(
            source_map,
            semantic_targets,
            prerequisite_targets,
            paper="Paper",
        )

        self.assertEqual(payload["unrouted_declarations"], [])
        self.assertEqual(set(payload["items"]), {"Paper.Model"})
        self.assertEqual(
            payload["items"]["Paper.Model"]["candidate_source_items"],
            ["definition"],
        )
        self.assertEqual(payload["items"]["Paper.Model"]["source_item"], "definition")
        for row in payload["items"].values():
            self.assertEqual(row["judgment"], "")
            self.assertEqual(row["reason"], "")

    def test_template_keeps_unrouted_internal_helpers_in_lean_closure_only(self) -> None:
        payload = decision_template(
            {"semantic_route_schema": 2, "items": {}},
            {},
            {"Paper.Unrouted": {"direct_paper_declarations": []}},
            paper="Paper",
        )
        self.assertEqual(payload["unrouted_declarations"], [])
        self.assertEqual(payload["items"], {})

    def test_explicit_direct_source_overrides_incidental_dependency_owner(self) -> None:
        source_map = {
            "semantic_route_schema": 2,
            "items": {
                "result": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "semantic_contract": {
                        "spec_declaration": "Paper.ResultSpec",
                        "evidence_declaration": "Paper.result",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                },
                    "direct_definition": {
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                    "claim_bearing": True,
                        "lean_declarations": ["Paper.Shared"],
                },
            },
            "paper_semantic_prerequisite_sources": {
                "Paper.Shared": "direct_definition"
            },
        }
        payload = decision_template(
            source_map,
            {
                "Paper.ResultSpec": {
                    "prerequisite_declarations": ["Paper.Shared"]
                }
            },
            {"Paper.Shared": {"direct_paper_declarations": []}},
            paper="Paper",
        )
        self.assertEqual(payload["unrouted_declarations"], [])
        self.assertEqual(
            payload["items"]["Paper.Shared"]["candidate_source_items"],
            ["direct_definition"],
        )
        self.assertEqual(
            payload["items"]["Paper.Shared"]["source_item"],
            "direct_definition",
        )
        self.assertEqual(payload["items"]["Paper.Shared"]["judgment"], "")

    def test_explicit_direct_source_must_name_current_prerequisite(self) -> None:
        with self.assertRaisesRegex(
            ValueError,
            "outside the current Lean prerequisite surface",
        ):
            decision_template(
                {
                    "semantic_route_schema": 2,
                    "items": {"definition": {"source_kind": "definition"}},
                    "paper_semantic_prerequisite_sources": {
                        "Paper.NotCurrent": "definition"
                    },
                },
                {},
                {"Paper.Current": {"direct_paper_declarations": []}},
                paper="Paper",
            )

    def test_reissue_rebinds_a_unique_semantic_rename(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Paper"
            (paper_dir / "audit").mkdir(parents=True)
            old_name = "Paper.OldModel"
            new_name = "Paper.Model"
            source_map = {
                "items": {
                    "definition": {
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                        "claim_bearing": True,
                        "lean_declarations": [new_name],
                    }
                },
                "paper_semantic_prerequisite_sources": {
                    new_name: "definition"
                },
            }
            (paper_dir / "audit" / "paper_semantic_prerequisites.json").write_text(
                json.dumps(
                    {
                        "items": {
                            old_name: {
                                "paper_declaration": old_name,
                                "paper_semantic_target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
                                "paper_declaration_sha256": "c" * 64,
                                "paper_semantic_target_sha256": "d" * 64,
                                "elaborated_signature_sha256": "a" * 64,
                                "source_input_bundle_sha256": "b" * 64,
                                "judgment": "matches",
                                "reason": "The exact source and Lean target agree.",
                                "validator": "Reviewer",
                                "validator_type": "llm_as_judge",
                                "validated_at": "2026-08-26T00:00:00+00:00",
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            entry = {
                "lean_name": new_name,
                "paper_source_path": "papers/Paper/PaperInterface.lean",
                "paper_line_start": 4,
                "paper_line_end": 4,
                "paper_declaration_source": "def Model : Prop := True",
                "paper_declaration_sha256": "c" * 64,
                "paper_semantic_target": "Prop",
                "paper_semantic_target_sha256": "d" * 64,
                "elaborated_signature_sha256": "a" * 64,
                "verbatim_source_input": "Definition. The model is true.",
                "source_input_bundle_sha256": "b" * 64,
                "source_anchor_bundle_sha256": "e" * 64,
                "source_item": "definition",
                "source_locator": "sources/paper.txt:1",
            }
            graph = SimpleNamespace(
                context=SimpleNamespace(statement_map=source_map),
                semantic_targets={},
                paper_prerequisite_targets={
                    new_name: {
                        "display": "Prop",
                        "display_sha256": "57d968860fabe1008d2c72342adec04b70f4bae48b7bcf6ebca915624100c353",
                        "direct_paper_declarations": [],
                    }
                },
                paper_declaration_sources={
                    new_name: {
                        "paper_declaration_source": "def Model : Prop := True",
                        "paper_declaration_sha256": "705a6d4e5cb05a900860c5926bc8b0a7d3e87344a04b67ad5f6be8811a3c972e",
                    }
                },
                paper_prerequisite_review_support=lambda _roots: (
                    {}, {new_name: (new_name,)}, {new_name: ""}
                ),
                project_paper_prerequisites=lambda _folder, *, ledger: [entry],
            )

            payload = reissue(
                paper_dir,
                {},
                validator="",
                review_graph=graph,
            )

            self.assertEqual(set(payload["items"]), {new_name})
            self.assertEqual(payload["items"][new_name]["validator"], "Reviewer")
            self.assertEqual(payload["items"][new_name]["source_item"], "definition")
            self.assertEqual(
                payload["items"][new_name]["paper_declaration"], new_name
            )


if __name__ == "__main__":
    unittest.main()
