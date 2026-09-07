"""Tests for activation of a fresh v11 human-review surface."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.activate_v11_review_surface import activate, status_route_projection_errors
from scripts.current_closeout import planner


class ActivateV11ReviewSurfaceTests(unittest.TestCase):
    def test_activation_resets_the_saved_human_review_queue(self) -> None:
        activated = activate(
            {
                "review_surface": {"include_names": ["legacy"]},
                "human_review": {"reviewed_rows": 12, "total_rows": 12},
            },
            {
                "paper": "Fixture",
                "items": {
                    "first": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.PaperInterface.firstSpec",
                            "evidence_declaration": "Fixture.PaperInterface.first_realizes_spec",
                        }
                    },
                    "second": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.PaperInterface.secondSpec",
                            "evidence_declaration": "Fixture.PaperInterface.second_proof",
                        }
                    },
                },
            },
            paper="Fixture",
        )
        self.assertEqual(activated["review_surface"]["include_names"], ["firstSpec", "secondSpec"])
        self.assertEqual(
            activated["review_surface"]["proposition_spec_proofs"],
            {"firstSpec": "first_realizes_spec", "secondSpec": "second_proof"},
        )
        self.assertEqual(activated["human_review"]["reviewed_rows"], 0)
        self.assertEqual(activated["human_review"]["total_rows"], 2)
        self.assertEqual(activated["human_review"]["mismatch_rows"], 0)

    def test_activation_accepts_a_root_namespace_paper_interface_module(self) -> None:
        """Legacy modules may expose review Specs directly under the paper namespace."""

        activated = activate(
            {},
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.claimSpec",
                            "evidence_declaration": "Fixture.claim_proof",
                        }
                    }
                },
            },
            paper="Fixture",
        )

        self.assertEqual(activated["review_surface"]["include_names"], ["claimSpec"])
        self.assertEqual(
            activated["review_surface"]["proposition_spec_proofs"],
            {"claimSpec": "claim_proof"},
        )

    def test_activation_reconciles_human_slices_to_current_specs(self) -> None:
        activated = activate(
            {
                "review_surface": {
                    "slices": [
                        {
                            "id": "main",
                            "title": "Main results",
                            "names": ["oldSpec", "firstSpec"],
                        }
                    ]
                }
            },
            {
                "paper": "Fixture",
                "items": {
                    "first": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.firstSpec",
                            "evidence_declaration": "Fixture.first_proof",
                        }
                    },
                    "second": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.secondSpec",
                            "evidence_declaration": "Fixture.second_proof",
                        }
                    },
                },
            },
            paper="Fixture",
        )

        self.assertEqual(
            activated["review_surface"]["slices"],
            [
                {"id": "main", "title": "Main results", "names": ["firstSpec"]},
                {
                    "id": "additional_source_results",
                    "title": "Additional source results",
                    "names": ["secondSpec"],
                },
            ],
        )

    def test_activation_uses_an_explicit_interface_namespace(self) -> None:
        activated = activate(
            {},
            {
                "paper": "FolderId",
                "paper_interface_namespace": "AppliedModelingLib.Example.Paper",
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "AppliedModelingLib.Example.Paper.PaperInterface.claimSpec",
                            "evidence_declaration": "AppliedModelingLib.Example.Paper.PaperInterface.claim_proof",
                        }
                    }
                },
            },
            paper="FolderId",
        )
        self.assertEqual(activated["review_surface"]["include_names"], ["claimSpec"])

    def test_activation_accepts_a_separate_proof_interface_endpoint(self) -> None:
        """Current source routes pair PaperInterface Specs with ProofInterface theorems."""

        activated = activate(
            {},
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture.PaperInterface.claimSpec",
                            "evidence_declaration": "Fixture.ProofInterface.claim_proof",
                        }
                    }
                },
            },
            paper="Fixture",
        )

        self.assertEqual(activated["review_surface"]["include_names"], ["claimSpec"])
        self.assertEqual(
            activated["review_surface"]["proposition_spec_proofs"],
            {"claimSpec": "claim_proof"},
        )

    def test_status_projection_rejects_a_stale_wrapper_without_claiming_evidence(self) -> None:
        source_map = {
            "paper": "Fixture",
            "semantic_route_schema": 2,
            "items": {
                "claim": {
                    "semantic_contract": {
                        "spec_declaration": "Fixture.PaperInterface.currentSpec",
                        "evidence_declaration": "Fixture.PaperInterface.current_proof",
                    }
                }
            },
        }
        errors = status_route_projection_errors(
            {
                "review_surface": {
                    "include_names": ["staleWrapperSpec"],
                    "proposition_spec_proofs": {
                        "staleWrapperSpec": "stale_wrapper_proof"
                    },
                }
            },
            source_map,
            paper="Fixture",
        )
        self.assertEqual(len(errors), 2)
        self.assertTrue(all("not semantic or proof evidence" not in error for error in errors))
        self.assertTrue(all("activate_v11_review_surface.py --write" in error for error in errors))

    def test_static_preflight_stops_stale_navigation_before_graph_work(self) -> None:
        source_map = {
            "paper": "Fixture",
            "semantic_route_schema": 2,
            "items": {
                "claim": {
                    "semantic_contract": {
                        "spec_declaration": "Fixture.PaperInterface.currentSpec",
                        "evidence_declaration": "Fixture.PaperInterface.current_proof",
                    }
                }
            },
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (root / "papers" / "Fixture.lean").write_text("\n", encoding="utf-8")
            (folder / "PaperInterface.lean").write_text("\n", encoding="utf-8")
            (audit / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )
            stale_status = {
                "id": "Fixture",
                "status": "formalized",
                "review_surface": {
                    "include_names": ["staleWrapperSpec"],
                    "proposition_spec_proofs": {
                        "staleWrapperSpec": "stale_wrapper_proof"
                    },
                },
            }
            (folder / "status.json").write_text(
                json.dumps(stale_status), encoding="utf-8"
            )
            with mock.patch.object(planner, "ROOT", root):
                readiness = planner.static_closeout_readiness(
                    folder, include_intake=False, require_terminal_documents=False
                )
            self.assertFalse(readiness["ready"])
            self.assertTrue(
                any(
                    "review-surface projection" in blocker
                    for blocker in readiness["blockers"]
                )
            )


if __name__ == "__main__":
    unittest.main()
