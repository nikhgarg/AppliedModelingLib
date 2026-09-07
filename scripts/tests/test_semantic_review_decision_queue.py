"""Tests for identity-bound semantic-review work queues."""

from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import semantic_review_decision_queue as queue


def digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


class SemanticReviewDecisionQueueTests(unittest.TestCase):
    def material(self) -> dict[str, dict[str, str]]:
        return {
            "Paper.Model": {
                "target": "fun x => x = x",
                "target_sha": digest("fun x => x = x"),
                "declaration": "def Model (x : Nat) : Prop := x = x",
                "declaration_sha": digest("def Model (x : Nat) : Prop := x = x"),
                "claim_identity": digest("canonical claim atoms"),
            }
        }

    def supporting_declarations(self) -> dict[str, dict[str, str]]:
        paper_target = "fun n : Nat => n + 1"
        paper_source = "def successor (n : Nat) := n + 1"
        return {
            "Paper.successor": {
                "scope": "paper_prerequisite",
                "semantic_target": paper_target,
                "semantic_target_sha256": digest(paper_target),
                "declaration_source": paper_source,
                "declaration_source_sha256": digest(paper_source),
            }
        }

    def enriched(
        self,
        *,
        with_support: bool = False,
        per_item_support: bool = False,
    ) -> dict:
        routed = {
            "schema": 1,
            "paper": "Paper",
            "items": {
                "Paper.Model": {
                    "source_item": "definition",
                    "candidate_source_items": ["definition"],
                    "judgment": "",
                    "reason": "",
                }
            },
        }
        source_map = {"items": {"definition": {"source_location": "paper.txt:1"}}}
        source_context = {
            "source_locator": "paper.txt:1",
            "verbatim_source_input": "Source definition.",
            "verbatim_source_input_sha256": digest("Source definition."),
            "source_input_bundle_sha256": digest("source bundle"),
        }
        with tempfile.TemporaryDirectory() as temporary, mock.patch.object(
            queue,
            "_source_context",
            return_value=source_context,
        ):
            return queue.enrich_queue(
                routed,
                paper_dir=Path(temporary),
                source_map=source_map,
                material_by_name=self.material(),
                semantic_target_field="target",
                semantic_target_sha256_field="target_sha",
                declaration_source_field="declaration",
                declaration_source_sha256_field="declaration_sha",
                declaration_identity_fields=("claim_identity",),
                supporting_declarations=(
                    self.supporting_declarations() if with_support else None
                ),
                supporting_declaration_names_by_item=(
                    {"Paper.Model": ["Paper.successor"]}
                    if per_item_support
                    else None
                ),
            )

    def test_queue_is_self_contained_and_identity_bound(self) -> None:
        payload = self.enriched()
        row = payload["items"]["Paper.Model"]
        row["judgment"] = "matches"
        row["reason"] = "The displayed source definition and Lean predicate agree."

        items = queue.validated_queue_items(payload, paper="Paper")

        self.assertEqual(
            items["Paper.Model"]["_reviewed_semantic_target_sha256"],
            digest("fun x => x = x"),
        )
        self.assertEqual(
            items["Paper.Model"]["_reviewed_declaration_source_sha256"],
            digest("def Model (x : Nat) : Prop := x = x"),
        )
        self.assertEqual(
            items["Paper.Model"]["_reviewed_source_input_bundle_sha256"],
            digest("source bundle"),
        )
        self.assertEqual(
            items["Paper.Model"]["_reviewed_declaration_identity"],
            {"claim_identity": digest("canonical claim atoms")},
        )

    def test_queue_retains_approved_context_for_reviewer(self) -> None:
        payload = self.enriched()
        source_context = payload["review_material"]["source_items"]["definition"]
        authority = {
            "protocol": "approved-source-review-context-v1",
            "id": "FIXTURE-CALENDAR-01",
            "kind": "source_model_convention",
            "formal_meaning": "Count events by calendar event time.",
        }
        authority["record_sha256"] = queue._canonical_digest(authority)
        source_context["approved_review_contexts"] = [authority]
        payload["review_material_sha256"] = queue._canonical_digest(
            payload["review_material"]
        )

        items = queue.validated_queue_items(payload, paper="Paper")

        self.assertIn("Paper.Model", items)
        self.assertEqual(
            source_context["approved_review_contexts"][0]["formal_meaning"],
            "Count events by calendar event time.",
        )

    def test_modified_embedded_review_material_is_rejected(self) -> None:
        payload = self.enriched()
        payload["review_material"]["source_items"]["definition"][
            "verbatim_source_input"
        ] = "Different source."

        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "embedded review material was modified",
        ):
            queue.validated_queue_items(payload, paper="Paper")

    def test_queue_rejects_pretty_printer_elision_in_semantic_target(self) -> None:
        """No source-to-Lean judgment may be issued from a partial display."""

        material = self.material()
        target = "∀ x : Nat, ⋯ → x = x"
        material["Paper.Model"]["target"] = target
        material["Paper.Model"]["target_sha"] = digest(target)
        with (
            mock.patch.object(self, "material", return_value=material),
            self.assertRaisesRegex(
                queue.SemanticReviewDecisionQueueError, "pretty-printer elision"
            ),
        ):
            self.enriched()

    def test_supporting_declarations_are_reviewer_context_not_receipt_identity(self) -> None:
        payload = self.enriched(with_support=True)
        row = payload["items"]["Paper.Model"]
        row["judgment"] = "matches"
        row["reason"] = "The source and Lean target agree in the displayed model."
        decision = queue.validated_queue_items(payload, paper="Paper")[
            "Paper.Model"
        ]
        support_digest = queue.supporting_declarations_sha256(
            self.supporting_declarations()
        )
        self.assertEqual(
            decision["_reviewed_supporting_declarations_sha256"],
            support_digest,
        )
        current = {
            "target_sha": digest("fun x => x = x"),
            "declaration_sha": digest("def Model (x : Nat) : Prop := x = x"),
            "source_input_bundle_sha256": digest("source bundle"),
            "verbatim_source_input": "Source definition.",
        }
        queue.validate_current_identity(
            "Paper.Model",
            decision,
            current,
            semantic_target_sha256_field="target_sha",
            declaration_source_sha256_field="declaration_sha",
        )

        # Supplying current context opts an in-progress issuance into exact
        # queue-material binding, without changing historical reuse identity.
        current["semantic_supporting_declarations_sha256"] = support_digest
        queue.validate_current_identity(
            "Paper.Model", decision, current,
            semantic_target_sha256_field="target_sha",
            declaration_source_sha256_field="declaration_sha",
        )
        changed_support = self.supporting_declarations()
        changed_support["Paper.successor"]["semantic_target"] = "fun n : Nat => n + 2"
        changed_support["Paper.successor"]["semantic_target_sha256"] = digest("fun n : Nat => n + 2")
        current["semantic_supporting_declarations_sha256"] = (
            queue.supporting_declarations_sha256(changed_support)
        )
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError, "supporting semantic context changed"
        ):
            queue.validate_current_identity(
                "Paper.Model", decision, current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
            )

    def test_per_item_support_selection_is_bound_without_unrelated_rows(self) -> None:
        payload = self.enriched(with_support=True, per_item_support=True)
        self.assertEqual(
            payload["items"]["Paper.Model"]["supporting_declarations"],
            ["Paper.successor"],
        )
        payload["items"]["Paper.Model"]["judgment"] = "matches"
        payload["items"]["Paper.Model"]["reason"] = "Exact displayed match."
        decision = queue.validated_queue_items(payload, paper="Paper")[
            "Paper.Model"
        ]
        self.assertEqual(
            decision["_reviewed_supporting_declarations_sha256"],
            queue.selected_supporting_declarations_sha256(
                self.supporting_declarations(),
                ["Paper.successor"],
            ),
        )

    def test_review_support_follows_only_lean_owned_dependency_edges(self) -> None:
        def target(display: str, *, paper=(), library=()) -> dict:
            return {
                "display": display,
                "display_sha256": digest(display),
                "direct_paper_declarations": list(paper),
                "direct_library_declarations": list(library),
            }

        def paper_source(source: str) -> dict:
            return {
                "paper_declaration_source": source,
                "paper_declaration_sha256": digest(source),
            }

        def library_source(source: str) -> dict:
            return {
                "library_definition": source,
                "library_definition_sha256": digest(source),
            }

        review_targets = {
            "paper_prerequisite_targets": {
                "Paper.Root": target("root", paper=("Paper.Helper",)),
                "Paper.Helper": target(
                    "helper",
                    library=("AppliedModelingLib.Leaf",),
                ),
                "Paper.Unrelated": target("unrelated"),
            },
            "library_semantic_targets": {
                "AppliedModelingLib.Leaf": target("leaf"),
            },
            "paper_declaration_sources": {
                "Paper.Root": paper_source("def Root := Helper"),
                "Paper.Helper": paper_source("def Helper := Leaf"),
                "Paper.Unrelated": paper_source("def Unrelated := True"),
            },
            "library_declaration_sources": {
                "AppliedModelingLib.Leaf": library_source("def Leaf := True"),
            },
            "library_semantic_target_errors": {},
        }
        support, names_by_root = queue.review_support_from_targets(
            review_targets,
            root_declarations={"Paper.Root"},
        )
        self.assertEqual(
            set(support),
            {"Paper.Root", "Paper.Helper", "AppliedModelingLib.Leaf"},
        )
        self.assertEqual(
            set(names_by_root["Paper.Root"]),
            {"Paper.Root", "Paper.Helper", "AppliedModelingLib.Leaf"},
        )

    def test_review_support_includes_nearest_source_claim_use_context(self) -> None:
        """A generic leaf is reviewed with its Lean-proved model-restricted use."""

        def target(display: str, *, paper=()) -> dict:
            return {
                "display": display,
                "display_sha256": digest(display),
                "direct_paper_declarations": list(paper),
                "direct_library_declarations": [],
            }

        def paper_source(source: str) -> dict:
            return {
                "paper_declaration_source": source,
                "paper_declaration_sha256": digest(source),
            }

        review_targets = {
            "semantic_targets": {
                "Paper.ResultSpec": {
                    "prerequisite_declarations": ["Paper.SourceModel"],
                    "display": "SourceModel gaussianLaw",
                    "display_sha256": digest("SourceModel gaussianLaw"),
                }
            },
            "paper_prerequisite_targets": {
                "Paper.SourceModel": target(
                    "source model", paper=("Paper.GaussianCandidate",)
                ),
                "Paper.GaussianCandidate": target(
                    "candidate with Gaussian-law invariant", paper=("Paper.Candidate",)
                ),
                "Paper.Candidate": target("generic candidate record"),
            },
            "library_semantic_targets": {},
            "paper_declaration_sources": {
                "Paper.SourceModel": paper_source("def SourceModel := ..."),
                "Paper.GaussianCandidate": paper_source("def GaussianCandidate := ..."),
                "Paper.Candidate": paper_source("structure Candidate where ..."),
            },
            "library_declaration_sources": {},
            "library_semantic_target_errors": {},
        }

        support, names_by_root = queue.review_support_from_targets(
            review_targets,
            root_declarations={"Paper.Candidate"},
        )

        self.assertEqual(
            set(names_by_root["Paper.Candidate"]),
            {"Paper.Candidate", "Paper.GaussianCandidate", "Paper.SourceModel",
             "source_claim_use:Paper.ResultSpec"},
        )
        self.assertEqual(
            set(support),
            {"Paper.Candidate", "Paper.GaussianCandidate", "Paper.SourceModel",
             "source_claim_use:Paper.ResultSpec"},
        )

    def test_review_support_keeps_every_nearest_use_path_and_stops_at_boundary(self) -> None:
        """Context includes both source-facing uses but not a wider proof route."""

        def target(display: str, *, paper=()) -> dict:
            return {
                "display": display,
                "display_sha256": digest(display),
                "direct_paper_declarations": list(paper),
                "direct_library_declarations": [],
            }

        def source(name: str) -> dict:
            declaration = f"def {name} := ..."
            return {
                "paper_declaration_source": declaration,
                "paper_declaration_sha256": digest(declaration),
            }

        review_targets = {
            "semantic_targets": {
                "Paper.FirstSpec": {
                    "prerequisite_declarations": ["Paper.FirstModel"],
                    "display": "FirstModel firstLaw",
                    "display_sha256": digest("FirstModel firstLaw"),
                },
                "Paper.SecondSpec": {
                    "prerequisite_declarations": ["Paper.SecondModel"],
                    "display": "SecondModel secondLaw",
                    "display_sha256": digest("SecondModel secondLaw"),
                },
            },
            "paper_prerequisite_targets": {
                "Paper.WiderRoute": target("wider", paper=("Paper.FirstModel",)),
                "Paper.FirstModel": target("first model", paper=("Paper.FirstUse",)),
                "Paper.FirstUse": target("first use", paper=("Paper.Leaf",)),
                "Paper.SecondModel": target("second model", paper=("Paper.SecondUse",)),
                "Paper.SecondUse": target("second use", paper=("Paper.Leaf",)),
                "Paper.Leaf": target("generic leaf"),
            },
            "library_semantic_targets": {},
            "paper_declaration_sources": {
                name: source(name.rsplit(".", 1)[-1])
                for name in (
                    "Paper.WiderRoute",
                    "Paper.FirstModel",
                    "Paper.FirstUse",
                    "Paper.SecondModel",
                    "Paper.SecondUse",
                    "Paper.Leaf",
                )
            },
            "library_declaration_sources": {},
            "library_semantic_target_errors": {},
        }

        _support, names_by_root = queue.review_support_from_targets(
            review_targets,
            root_declarations={"Paper.Leaf"},
        )

        self.assertEqual(
            set(names_by_root["Paper.Leaf"]),
            {
                "Paper.Leaf",
                "Paper.FirstModel",
                "Paper.FirstUse",
                "Paper.SecondModel",
                "Paper.SecondUse",
                "source_claim_use:Paper.FirstSpec",
                "source_claim_use:Paper.SecondSpec",
            },
        )
        self.assertNotIn("Paper.WiderRoute", names_by_root["Paper.Leaf"])

    def test_direct_generic_use_displays_every_consuming_spec(self) -> None:
        declaration = "def rank (value : Nat → Int) := value"
        targets = {
            "semantic_targets": {
                "Paper.RankSpec": {
                    "library_declarations": ["Library.rank"],
                    "display": "rank (fun w => -prob w)",
                    "display_sha256": digest("rank (fun w => -prob w)"),
                },
                "Paper.OtherSpec": {
                    "display": "unrelated",
                    "display_sha256": digest("unrelated"),
                },
            },
            "library_semantic_targets": {
                "Library.rank": {
                    "display": "fun value => value",
                    "display_sha256": digest("fun value => value"),
                },
            },
            "library_declaration_sources": {
                "Library.rank": {
                    "library_definition": declaration,
                    "library_definition_sha256": digest(declaration),
                },
            },
        }
        support, by_root = queue.review_support_from_targets(
            targets, root_declarations={"Library.rank"}
        )
        self.assertEqual(set(support), {"Library.rank", "source_claim_use:Paper.RankSpec"})
        self.assertEqual(set(by_root["Library.rank"]), set(support))
        use = support["source_claim_use:Paper.RankSpec"]
        self.assertEqual(use["scope"], "source_claim_use")
        self.assertEqual(use["lean_name"], "Paper.RankSpec")
        self.assertEqual(use["semantic_target"], "rank (fun w => -prob w)")
        self.assertNotIn("declaration_source", use)

        targets["semantic_targets"]["Paper.SecondSpec"] = {
            "library_declarations": ["Library.rank"],
            "display": "rank cost",
            "display_sha256": digest("rank cost"),
        }
        support, by_root = queue.review_support_from_targets(
            targets, root_declarations={"Library.rank"}
        )
        self.assertEqual(set(by_root["Library.rank"]), {
            "Library.rank", "source_claim_use:Paper.RankSpec",
            "source_claim_use:Paper.SecondSpec",
        })

        collision = "source_claim_use:Paper.RankSpec"
        targets["library_semantic_targets"][collision] = targets["library_semantic_targets"]["Library.rank"]
        targets["library_declaration_sources"][collision] = targets["library_declaration_sources"]["Library.rank"]
        with self.assertRaisesRegex(queue.SemanticReviewDecisionQueueError, "collides"):
            queue.review_support_from_targets(
                targets, root_declarations={"Library.rank", collision}
            )
        del targets["library_semantic_targets"][collision]
        del targets["library_declaration_sources"][collision]

        for mutation in ("missing", "changed"):
            with self.subTest(mutation=mutation):
                target = targets["semantic_targets"]["Paper.RankSpec"]
                target["display"] = "" if mutation == "missing" else "rank prob"
                with self.assertRaisesRegex(
                    queue.SemanticReviewDecisionQueueError, "supporting semantic target"
                ):
                    queue.review_support_from_targets(
                        targets, root_declarations={"Library.rank"}
                    )

    def test_source_use_context_is_display_only_and_identity_bound(self) -> None:
        support = {
            "source_claim_use:Paper.ResultSpec": {
                "scope": "source_claim_use",
                "lean_name": "Paper.ResultSpec",
                "semantic_target": "rank (-prob)",
                "semantic_target_sha256": digest("rank (-prob)"),
            }
        }
        original = queue.supporting_declarations_sha256(support)
        with mock.patch.object(self, "supporting_declarations", return_value=support):
            payload = self.enriched(with_support=True)
        decision = queue.validated_queue_items(payload, paper="Paper")["Paper.Model"]
        support["source_claim_use:Paper.ResultSpec"].update(
            semantic_target="rank prob", semantic_target_sha256=digest("rank prob")
        )
        self.assertNotEqual(original, queue.supporting_declarations_sha256(support))
        current = {
            "target_sha": digest("fun x => x = x"),
            "declaration_sha": digest("def Model (x : Nat) : Prop := x = x"),
            "source_input_bundle_sha256": digest("source bundle"),
            "verbatim_source_input": "Source definition.",
            "semantic_supporting_declarations_sha256": queue.supporting_declarations_sha256(support),
        }
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError, "supporting semantic context changed"
        ):
            queue.validate_current_identity(
                "Paper.Model", decision, current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
            )
        support["source_claim_use:Paper.ResultSpec"]["declaration_source"] = "invented code"
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError, "not declaration code"
        ):
            queue.supporting_declarations_sha256(support)

    def test_direct_review_support_can_show_only_selected_model_roots(self) -> None:
        """A result card's model context must not become a recursive review."""

        def target(display: str, *, paper=()) -> dict:
            return {
                "display": display,
                "display_sha256": digest(display),
                "direct_paper_declarations": list(paper),
                "direct_library_declarations": [],
            }

        def source(name: str) -> dict:
            declaration = f"def {name} := ..."
            return {
                "paper_declaration_source": declaration,
                "paper_declaration_sha256": digest(declaration),
            }

        review_targets = {
            "semantic_targets": {
                "Paper.ResultSpec": {
                    "prerequisite_declarations": ["Paper.SourceModel"]
                }
            },
            "paper_prerequisite_targets": {
                "Paper.SourceModel": target("source model", paper=("Paper.Helper",)),
                "Paper.Helper": target("helper"),
            },
            "library_semantic_targets": {},
            "paper_declaration_sources": {
                "Paper.SourceModel": source("SourceModel"),
                "Paper.Helper": source("Helper"),
            },
            "library_declaration_sources": {},
            "library_semantic_target_errors": {},
        }

        support, names_by_root = queue.review_support_from_targets(
            review_targets,
            root_declarations={"Paper.SourceModel"},
            include_descendant_context=False,
            include_nearest_source_use_context=False,
        )

        self.assertEqual(set(support), {"Paper.SourceModel"})
        self.assertEqual(set(names_by_root["Paper.SourceModel"]), {"Paper.SourceModel"})

    def test_modified_or_unscoped_supporting_declaration_is_rejected(self) -> None:
        payload = self.enriched(with_support=True)
        payload["review_material"]["supporting_declarations"]["Paper.successor"][
            "declaration_source"
        ] = "def successor (n : Nat) := n + 2"
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "embedded review material was modified",
        ):
            queue.validated_queue_items(payload, paper="Paper")

        support = self.supporting_declarations()
        support["Paper.successor"]["scope"] = "unknown"
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "invalid review scope",
        ):
            queue.supporting_declarations_sha256(support)

    def test_current_target_or_source_drift_is_rejected(self) -> None:
        payload = self.enriched()
        decision = queue.validated_queue_items(payload, paper="Paper")["Paper.Model"]
        current = {
            "target_sha": digest("different target"),
            "declaration_sha": digest("def Model (x : Nat) : Prop := x = x"),
            "source_input_bundle_sha256": digest("source bundle"),
            "verbatim_source_input": "Source definition.",
        }
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "Lean semantic target changed after review",
        ):
            queue.validate_current_identity(
                "Paper.Model",
                decision,
                current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
            )

        current["target_sha"] = decision["_reviewed_semantic_target_sha256"]
        current["declaration_sha"] = digest("def Model : Prop := True")
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "Lean declaration source changed after review",
        ):
            queue.validate_current_identity(
                "Paper.Model",
                decision,
                current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
            )

        current["declaration_sha"] = decision[
            "_reviewed_declaration_source_sha256"
        ]
        current["source_input_bundle_sha256"] = digest("different source")
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "source input changed after review",
        ):
            queue.validate_current_identity(
                "Paper.Model",
                decision,
                current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
            )

        current["source_input_bundle_sha256"] = digest("source bundle")
        current["verbatim_source_input"] = "Different displayed source."
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "verbatim source text changed after review",
        ):
            queue.validate_current_identity(
                "Paper.Model",
                decision,
                current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
            )

    def test_required_declaration_identity_is_checked_at_issuance(self) -> None:
        payload = self.enriched()
        decision = queue.validated_queue_items(payload, paper="Paper")["Paper.Model"]
        current = {
            "target_sha": digest("fun x => x = x"),
            "declaration_sha": digest("def Model (x : Nat) : Prop := x = x"),
            "source_input_bundle_sha256": digest("source bundle"),
            "verbatim_source_input": "Source definition.",
        }
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "Lean declaration identity changed after review",
        ):
            queue.validate_current_identity(
                "Paper.Model",
                decision,
                current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
                declaration_identity={"claim_identity": digest("changed atoms")},
            )

        legacy_decision = dict(decision)
        legacy_decision.pop("_reviewed_declaration_identity")
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "lacks the required Lean declaration identity",
        ):
            queue.validate_current_identity(
                "Paper.Model",
                legacy_decision,
                current,
                semantic_target_sha256_field="target_sha",
                declaration_source_sha256_field="declaration_sha",
                declaration_identity={
                    "claim_identity": digest("canonical claim atoms")
                },
            )

    def test_common_semantic_reuse_requires_source_and_lean_identity(self) -> None:
        signature = digest("elaborated signature")
        source = digest("source bundle")
        prior = {
            "judgment": "matches",
            "reason": "The exact source and semantic target agree.",
            "validator": "reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-29T00:00:00Z",
            "target_protocol": "target-v1",
            "elaborated_signature_sha256": signature,
            "source_input_bundle_sha256": source,
        }
        entry = {
            "elaborated_signature_sha256": signature,
            "source_input_bundle_sha256": source,
        }
        self.assertIsNotNone(
            queue.reusable_semantic_judgment(
                prior,
                entry,
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
            )
        )
        self.assertIsNone(
            queue.reusable_semantic_judgment(
                prior,
                {**entry, "source_input_bundle_sha256": digest("changed source")},
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
            )
        )
        self.assertIsNone(
            queue.reusable_semantic_judgment(
                {**prior, "source_input_bundle_sha256": ""},
                {**entry, "source_input_bundle_sha256": ""},
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
            )
        )
        self.assertIsNone(
            queue.reusable_semantic_judgment(
                prior,
                {**entry, "elaborated_signature_sha256": digest("changed Lean")},
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
            )
        )

    def test_common_semantic_reuse_rebinds_an_approved_context_only(self) -> None:
        """A settled clarification changes reviewer guidance, not raw semantics."""

        signature = digest("elaborated signature")
        anchor = digest("verbatim source anchors")
        prior = {
            "judgment": "matches",
            "reason": "The exact source and semantic target agree.",
            "validator": "reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-29T00:00:00Z",
            "target_protocol": "target-v1",
            "elaborated_signature_sha256": signature,
            # Schema-1 source bundles predate the explicit anchor field.
            "source_input_bundle_sha256": anchor,
        }
        entry = {
            "elaborated_signature_sha256": signature,
            "source_input_bundle_sha256": digest(
                "same anchors plus approved clarification"
            ),
            "source_anchor_bundle_sha256": anchor,
        }
        self.assertIsNotNone(
            queue.reusable_semantic_judgment(
                prior,
                entry,
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
            )
        )
        self.assertIsNone(
            queue.reusable_semantic_judgment(
                prior,
                {**entry, "source_anchor_bundle_sha256": digest("new source")},
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
            )
        )

    def test_common_semantic_reuse_accepts_the_exact_legacy_review_target(self) -> None:
        source = digest("source bundle")
        target = digest("exact reviewed target")
        prior = {
            "judgment": "matches",
            "reason": "The exact source and semantic target agree.",
            "validator": "reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-29T00:00:00Z",
            "target_protocol": "target-v1",
            "target_sha256": target,
            "source_input_bundle_sha256": source,
        }
        entry = {
            "target_sha256": target,
            "source_input_bundle_sha256": source,
        }

        self.assertIsNotNone(
            queue.reusable_semantic_judgment(
                prior,
                entry,
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
                prior_target_sha256_field="target_sha256",
                current_target_sha256_field="target_sha256",
            )
        )
        self.assertIsNone(
            queue.reusable_semantic_judgment(
                prior,
                {**entry, "target_sha256": digest("changed target")},
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
                prior_target_sha256_field="target_sha256",
                current_target_sha256_field="target_sha256",
            )
        )
    def test_common_delta_filter_keeps_only_nonreusable_rows(self) -> None:
        payload = {
            "items": {"Current": {}, "Changed": {}},
            "unrouted_declarations": ["Current", "Changed"],
        }
        entries = [
            {"lean_name": "Current"},
            {"lean_name": "Changed"},
        ]
        filtered, changed_entries = queue.changed_only_template_surface(
            payload,
            entries,
            {"Current": {}, "Changed": {}},
            reusable_judgment=lambda _prior, entry: (
                {"judgment": "matches"}
                if entry["lean_name"] == "Current"
                else None
            ),
        )
        self.assertEqual(set(filtered["items"]), {"Changed"})
        self.assertEqual(filtered["unrouted_declarations"], ["Changed"])
        self.assertEqual(changed_entries, [{"lean_name": "Changed"}])

    def test_common_delta_filter_rebinds_one_semantically_identical_rename(self) -> None:
        signature = digest("same elaborated signature")
        source = digest("same source bundle")
        prior = {
            "judgment": "matches",
            "reason": "The exact source and Lean semantics agree.",
            "validator": "reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-29T00:00:00Z",
            "target_protocol": "target-v1",
            "elaborated_signature_sha256": signature,
            "source_input_bundle_sha256": source,
        }
        entry = {
            "lean_name": "Renamed.Model",
            "elaborated_signature_sha256": signature,
            "source_input_bundle_sha256": source,
        }

        filtered, changed_entries = queue.changed_only_template_surface(
            {
                "items": {"Renamed.Model": {}},
                "unrouted_declarations": ["Renamed.Model"],
            },
            [entry],
            {"Old.Model": prior},
            reusable_judgment=lambda old, current: queue.reusable_semantic_judgment(
                old,
                current,
                target_protocol_field="target_protocol",
                target_protocol="target-v1",
                prior_code_sha256_field="code_sha256",
                current_code_sha256_field="code_sha256",
            ),
        )

        self.assertEqual(filtered["items"], {})
        self.assertEqual(filtered["unrouted_declarations"], [])
        self.assertEqual(changed_entries, [])

    def test_common_semantic_rebind_refuses_a_rename_collision(self) -> None:
        signature = digest("shared elaborated signature")
        source = digest("shared source bundle")
        prior = {
            "judgment": "matches",
            "reason": "The exact source and Lean semantics agree.",
            "validator": "reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-29T00:00:00Z",
            "target_protocol": "target-v1",
            "elaborated_signature_sha256": signature,
            "source_input_bundle_sha256": source,
        }
        entries = [
            {
                "lean_name": name,
                "elaborated_signature_sha256": signature,
                "source_input_bundle_sha256": source,
            }
            for name in ("Renamed.First", "Renamed.Second")
        ]
        reusable = lambda old, current: queue.reusable_semantic_judgment(
            old,
            current,
            target_protocol_field="target_protocol",
            target_protocol="target-v1",
            prior_code_sha256_field="code_sha256",
            current_code_sha256_field="code_sha256",
        )

        bindings = queue.unique_reusable_judgment_bindings(
            {entry["lean_name"]: entry for entry in entries},
            {"Old.Model": prior},
            reusable_judgment=reusable,
        )

        self.assertEqual(bindings, {})

    def test_exact_name_consumes_a_colliding_prior_before_rename_matching(self) -> None:
        signature = digest("shared elaborated signature")
        source = digest("shared source bundle")
        prior = {
            "judgment": "matches",
            "reason": "The exact source and Lean semantics agree.",
            "validator": "reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-08-29T00:00:00Z",
            "target_protocol": "target-v1",
            "elaborated_signature_sha256": signature,
            "source_input_bundle_sha256": source,
        }
        entries = {
            name: {
                "lean_name": name,
                "elaborated_signature_sha256": signature,
                "source_input_bundle_sha256": source,
            }
            for name in ("Stable.Model", "Renamed.Model")
        }
        reusable = lambda old, current: queue.reusable_semantic_judgment(
            old,
            current,
            target_protocol_field="target_protocol",
            target_protocol="target-v1",
            prior_code_sha256_field="code_sha256",
            current_code_sha256_field="code_sha256",
        )

        bindings = queue.unique_reusable_judgment_bindings(
            entries,
            {"Stable.Model": prior},
            reusable_judgment=reusable,
        )

        self.assertEqual(set(bindings), {"Stable.Model"})
        self.assertEqual(bindings["Stable.Model"][0], "Stable.Model")

    def test_template_output_path_is_new_and_paper_local(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper = root / "papers" / "Paper"
            paper.mkdir(parents=True)
            path = queue.template_output_path(
                paper,
                Path("papers/Paper/audit/queue.json"),
                repository_root=root,
            )
            self.assertEqual(path, paper / "audit" / "queue.json")
            path.parent.mkdir()
            path.write_text("{}\n", encoding="utf-8")
            with self.assertRaisesRegex(
                queue.SemanticReviewDecisionQueueError,
                "refusing to overwrite",
            ):
                queue.template_output_path(
                    paper,
                    Path("papers/Paper/audit/queue.json"),
                    repository_root=root,
                )
            with self.assertRaisesRegex(
                queue.SemanticReviewDecisionQueueError,
                "inside the paper folder",
            ):
                queue.template_output_path(
                    paper,
                    Path("outside.json"),
                    repository_root=root,
                )

    def test_content_addressed_queue_path_requires_exact_material_digest(self) -> None:
        paper = Path("papers/Paper")
        material_digest = digest("review material")
        self.assertEqual(
            queue.content_addressed_queue_path(
                paper,
                {"review_material_sha256": material_digest},
                filename_prefix="semantic_review_",
            ),
            paper / "audit" / f"semantic_review_{material_digest}.json",
        )
        with self.assertRaisesRegex(
            queue.SemanticReviewDecisionQueueError,
            "exact material identity",
        ):
            queue.content_addressed_queue_path(
                paper,
                {},
                filename_prefix="semantic_review_",
            )

    def test_normalized_decisions_apply_only_explicit_source_redirects(self) -> None:
        payload = self.enriched()
        payload["source_item_redirects"] = {"definition": "corrected_definition"}
        payload["items"]["Paper.Model"].update(
            {
                "judgment": "MATCHES",
                "reason": "The exact source and Lean target agree.",
            }
        )
        decisions = queue.normalized_decisions(
            payload,
            paper="Paper",
            valid_verdicts=frozenset({"matches", "mismatch", "uncertain"}),
        )
        self.assertEqual(decisions["Paper.Model"]["judgment"], "matches")
        self.assertEqual(
            decisions["Paper.Model"]["source_item"], "corrected_definition"
        )


if __name__ == "__main__":
    unittest.main()
