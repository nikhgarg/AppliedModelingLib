from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts.direct_semantic_review_binding import (
    LEAN_TARGET_PROTOCOL,
    SOURCE_INPUT_PROTOCOL,
    normalized_direct_screening_ledger,
    reusable_direct_source_spec_judgment,
)
from scripts.corrected_target_identity import CORRECTED_TARGET_REVIEW_PROTOCOL
from scripts.obligation_routes import EvidenceRouteSet
from scripts.source_review_input import source_semantic_input_bundle, statement_digest
from scripts.v11_screening_contract import V11_SCREENING_PROMPT_VERSION


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def semantic_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


class DirectSemanticReviewBindingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / "Fixture"
        self.paper_dir.mkdir(parents=True)
        self.source_path = self.paper_dir / "source.txt"
        self.source_path.write_text("Theorem. The result is true.\n", encoding="utf-8")
        self.atoms = [
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {"tag": "const", "name": "True"},
                "display": "True",
            }
        ]
        semantic_atoms = [
            {key: value for key, value in atom.items() if key != "display"}
            for atom in self.atoms
        ]
        self.target = {
            "lean_target_protocol": LEAN_TARGET_PROTOCOL,
            "display_sha256": digest("review display"),
            "review_claim_manifest_sha256": digest("manifest"),
            "review_claim_atoms_sha256": semantic_digest(
                {"schema": 1, "atoms": semantic_atoms}
            ),
            "review_claim_atoms": self.atoms,
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _source_item(self, spec: str) -> dict[str, object]:
        quote = "Theorem. The result is true."
        return {
            "source_kind": "theorem",
            "source_location": "source.txt:1",
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": quote,
                    "quoted_text_sha256": digest(quote),
                }
            ],
            "semantic_contract": {
                "spec_declaration": spec,
                "evidence_declaration": spec.removesuffix("Spec") + "Proof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }

    def _source_map(
        self,
        routes: dict[str, str] | None = None,
    ) -> dict[str, object]:
        configured = routes or {"claim": "Fixture.CurrentSpec"}
        return {
            "paper": "Fixture",
            "semantic_contract_schema": 1,
            "items": {
                source_item: self._source_item(spec)
                for source_item, spec in configured.items()
            },
        }

    def _prior_row(
        self,
        *,
        source_item: str = "claim",
        declaration: str = "Fixture.PriorSpec",
    ) -> dict[str, object]:
        source = self._source_item("Fixture.CurrentSpec")
        source_text, source_sha256, error = source_semantic_input_bundle(
            source,
            require_context_roles=True,
        )
        self.assertEqual(error, "")
        return {
            "judgment": "matches",
            "reason": "The exact source assertion and Lean claim agree.",
            "source_input_protocol": SOURCE_INPUT_PROTOCOL,
            "source_input_bundle_sha256": source_sha256,
            "paper_statement_sha256": statement_digest(source_text),
            "lean_target_protocol": LEAN_TARGET_PROTOCOL,
            "semantic_target_declaration": declaration,
            "lean_expanded_statement_sha256": digest("review display"),
            "review_claim_manifest_sha256": self.target[
                "review_claim_manifest_sha256"
            ],
            "review_claim_atoms_sha256": self.target[
                "review_claim_atoms_sha256"
            ],
            "source_review_target_sha256": digest("source review target"),
            "paper_interface_sha256": digest("paper interface"),
            "source_item": source_item,
        }

    def _screening(
        self,
        items: dict[str, dict[str, object]] | None = None,
    ) -> dict[str, object]:
        return {
            "schema": 3,
            "paper": "Fixture",
            "prompt_version": V11_SCREENING_PROMPT_VERSION,
            "validator": "independent semantic reviewer",
            "validated_at": "2026-08-29T00:00:00Z",
            "items": items
            or {"Fixture.PriorSpec": self._prior_row()},
        }

    def _normalize(
        self,
        *,
        source_map: dict[str, object] | None = None,
        screening: dict[str, object] | None = None,
        semantic_targets: dict[str, dict[str, object]] | None = None,
    ) -> dict[str, object]:
        selected_map = source_map or self._source_map()
        return normalized_direct_screening_ledger(
            paper_dir=self.paper_dir,
            source_map=selected_map,
            screening=screening or self._screening(),
            route_set=EvidenceRouteSet.from_source_map(selected_map),
            semantic_targets=semantic_targets
            or {"Fixture.CurrentSpec": self.target},
            repository_root=self.root,
        )

    def test_unique_declaration_rename_rebinds_without_rewriting_evidence(self) -> None:
        normalized = self._normalize()
        self.assertEqual(set(normalized["items"]), {"Fixture.CurrentSpec"})
        row = normalized["items"]["Fixture.CurrentSpec"]
        self.assertEqual(row["semantic_target_declaration"], "Fixture.CurrentSpec")
        self.assertEqual(row["source_item"], "claim")
        self.assertEqual(
            row["reason"], "The exact source assertion and Lean claim agree."
        )

    def test_definition_review_target_is_bound_beneath_its_spec_route(self) -> None:
        source_map = self._source_map()
        item = source_map["items"]["claim"]
        item["semantic_review_target"] = {
            "schema": 1,
            "kind": "definition_declaration",
            "declaration": "Fixture.CurrentDefinition",
        }
        target = {
            **self.target,
            "semantic_review_declaration": "Fixture.CurrentDefinition",
        }
        screening = self._screening()
        screening["items"]["Fixture.PriorSpec"][
            "semantic_review_declaration"
        ] = "Fixture.PriorDefinition"

        normalized = self._normalize(
            source_map=source_map,
            screening=screening,
            semantic_targets={"Fixture.CurrentSpec": target},
        )

        row = normalized["items"]["Fixture.CurrentSpec"]
        self.assertEqual(
            row["semantic_review_declaration"],
            "Fixture.CurrentDefinition",
        )

    def test_source_item_key_is_navigation_not_semantic_identity(self) -> None:
        source_map = self._source_map({"renamed_claim": "Fixture.CurrentSpec"})
        normalized = self._normalize(source_map=source_map)
        row = normalized["items"]["Fixture.CurrentSpec"]
        self.assertEqual(row["source_item"], "renamed_claim")

    def test_ambiguous_duplicate_semantics_fail_closed(self) -> None:
        source_map = self._source_map(
            {
                "claim_one": "Fixture.CurrentOneSpec",
                "claim_two": "Fixture.CurrentTwoSpec",
            }
        )
        screening = self._screening(
            {
                "Fixture.PriorOneSpec": self._prior_row(
                    source_item="old_one",
                    declaration="Fixture.PriorOneSpec",
                ),
                "Fixture.PriorTwoSpec": self._prior_row(
                    source_item="old_two",
                    declaration="Fixture.PriorTwoSpec",
                ),
            }
        )
        with self.assertRaisesRegex(ValueError, "complete one-to-one"):
            self._normalize(
                source_map=source_map,
                screening=screening,
                semantic_targets={
                    "Fixture.CurrentOneSpec": self.target,
                    "Fixture.CurrentTwoSpec": self.target,
                },
            )

    def test_changed_source_bundle_requires_new_review(self) -> None:
        changed = self._source_map()
        item = changed["items"]["claim"]
        item["source_anchor_evidence"][0]["quoted_text"] = (
            "Theorem. The changed result is true."
        )
        item["source_anchor_evidence"][0]["quoted_text_sha256"] = digest(
            "Theorem. The changed result is true."
        )
        self.source_path.write_text(
            "Theorem. The changed result is true.\n",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(ValueError, "complete one-to-one"):
            self._normalize(source_map=changed)

    def test_changed_lean_claim_requires_new_review(self) -> None:
        changed = copy.deepcopy(self.target)
        changed["display_sha256"] = digest("changed expanded statement")
        with self.assertRaisesRegex(ValueError, "complete one-to-one"):
            self._normalize(
                semantic_targets={"Fixture.CurrentSpec": changed},
            )

    def test_renderer_trace_change_does_not_replace_semantic_identity(self) -> None:
        screening = self._screening()
        row = screening["items"]["Fixture.PriorSpec"]
        row["source_review_target_sha256"] = digest("older rendered target")
        row["paper_interface_sha256"] = digest("older interface bytes")
        target = {
            **self.target,
            "paper_interface_sha256": digest("current interface bytes"),
        }

        normalized = self._normalize(
            screening=screening,
            semantic_targets={"Fixture.CurrentSpec": target},
        )

        self.assertEqual(set(normalized["items"]), {"Fixture.CurrentSpec"})

    def test_missing_reviewer_container_metadata_fails(self) -> None:
        screening = self._screening()
        screening["validator"] = ""
        with self.assertRaisesRegex(ValueError, "reviewer"):
            self._normalize(screening=screening)

    def test_legacy_schema_cannot_cross_a_declaration_rename(self) -> None:
        screening = self._screening()
        screening["schema"] = 2
        with self.assertRaisesRegex(ValueError, "legacy.*declaration names"):
            self._normalize(screening=screening)

    def test_corrected_target_identity_change_is_not_reusable(self) -> None:
        current = {
            "source_input_bundle_sha256": digest("source"),
            "paper_statement_sha256": digest("statement"),
            "lean_target_protocol": LEAN_TARGET_PROTOCOL,
            "lean_expanded_statement_sha256": digest("expanded"),
            "review_claim_manifest_sha256": digest("manifest"),
            "review_claim_atoms_sha256": digest("atoms"),
            "coverage_status": "corrected_source_statement",
            "corrected_target_review_sha256": digest("approved correction"),
        }
        prior = {
            **current,
            "source_input_protocol": SOURCE_INPUT_PROTOCOL,
            "judgment": "matches_approved_corrected_target",
            "reason": "The approved correction and Lean claim agree.",
            "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
        }
        self.assertIsNotNone(
            reusable_direct_source_spec_judgment(prior, current)
        )
        changed = {
            **current,
            "corrected_target_review_sha256": digest("changed approval"),
        }
        self.assertIsNone(
            reusable_direct_source_spec_judgment(prior, changed)
        )


if __name__ == "__main__":
    unittest.main()
