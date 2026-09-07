#!/usr/bin/env python3
"""Regression tests for source-only prose-definition coverage selection."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard  # noqa: E402
from scripts import audit_evidence_integrity as integrity  # noqa: E402
from scripts import source_named_result_index  # noqa: E402
from scripts.source_coverage_scope import (  # noqa: E402
    NAMED_THEORETICAL_STATEMENTS,
    SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD,
    SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD,
    SOURCE_PROSE_DEFINITION_EXCLUSION_JUDGMENT,
    SOURCE_PROSE_DEFINITION_NORMAL_SCOPE,
    SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD,
    SOURCE_PROSE_DEFINITION_RECONCILIATION_JUDGMENT,
    SOURCE_PROSE_DEFINITION_RECONCILIATION_RELATION,
    SOURCE_PROSE_DEFINITION_RECONCILIATION_SCHEMA,
    SOURCE_PROSE_DEFINITION_REPEATED_SCOPE,
    SOURCE_PROSE_DEFINITION_REPETITION_JUDGMENT,
    source_index_byte_pinned_anchor_item_ids,
    source_item_coverage_sha256,
    source_map_cache_semantic_sha256,
    source_prose_definition_inventory_errors,
    source_prose_definition_clause_sha256,
    source_prose_definition_presentation_sha256,
    source_prose_definition_presentations_sha256,
    source_prose_definition_statement_sha256,
)


class ProseDefinitionCoverageTests(unittest.TestCase):
    SOURCE_TEXT = (
        "We use R to denote auction revenue. R is the sum of all sale prices.\n"
        "We say an auction is truthful if truthful bidding is a dominant strategy.\n"
        "Algorithm 3. Apply the update rule.\n"
    )

    @staticmethod
    def _anchor(source_text: str, line_start: int, line_end: int) -> dict[str, object]:
        lines = source_text.rstrip("\n").split("\n")
        quote = "\n".join(lines[line_start - 1 : line_end])
        return {
            "path": "source.txt",
            "line_start": line_start,
            "line_end": line_end,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
        }

    def _payload(self) -> dict[str, object]:
        revenue_anchor = self._anchor(self.SOURCE_TEXT, 1, 1)
        truthful_anchor = self._anchor(self.SOURCE_TEXT, 2, 2)
        algorithm_anchor = self._anchor(self.SOURCE_TEXT, 3, 3)
        presentations = [
            {
                "schema": 1,
                "presentation_kind": "definition",
                "defined_entity_kind": "object",
                "defined_object": "R",
                "definitional_clause": (
                    "We use R to denote auction revenue. R is the sum of all sale prices."
                ),
                "scope_disposition": SOURCE_PROSE_DEFINITION_NORMAL_SCOPE,
                "source_anchor": revenue_anchor,
            },
            {
                "schema": 1,
                "presentation_kind": "definition",
                "defined_entity_kind": "predicate",
                "defined_object": "truthful",
                "definitional_clause": (
                    "We say an auction is truthful if truthful bidding is a dominant strategy."
                ),
                "scope_disposition": SOURCE_PROSE_DEFINITION_NORMAL_SCOPE,
                "source_anchor": truthful_anchor,
            },
        ]

        def reconciliation(
            presentation: dict[str, object], statement: str
        ) -> dict[str, object]:
            return {
                "schema": SOURCE_PROSE_DEFINITION_RECONCILIATION_SCHEMA,
                "relation": SOURCE_PROSE_DEFINITION_RECONCILIATION_RELATION,
                "presentation_sha256": source_prose_definition_presentation_sha256(
                    presentation
                ),
                "source_item_statement_sha256": (
                    source_prose_definition_statement_sha256(
                        {"statement": statement}
                    )
                ),
                "judgment": SOURCE_PROSE_DEFINITION_RECONCILIATION_JUDGMENT,
                "semantic_basis": (
                    "The exact source clause defines the complete object represented by "
                    "this source-map statement."
                ),
                "validator": "independent prose-definition semantic judge",
                "validator_type": "agent",
                "validated_at": "2026-08-02T12:00:00Z",
            }

        source_digest = hashlib.sha256(self.SOURCE_TEXT.encode("utf-8")).hexdigest()
        return {
            "schema": 1,
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_digest,
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "source-only prose-definition fixture",
                "validated_at": "2026-08-02T12:00:00Z",
                "method": (
                    "Independent source-byte extraction of visible result headings and "
                    "prose-presented named definitions."
                ),
                "source_artifact_sha256": source_digest,
                "discovered_named_result_sha256": "0" * 64,
                SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD: presentations,
                SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD: (
                    source_prose_definition_presentations_sha256(presentations)
                ),
            },
            "items": {
                "misleading_theorem_key": {
                    "source_kind": "definition",
                    "statement": "Auction revenue is the sum of all sale prices.",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [revenue_anchor],
                    "lean_declarations": ["Fixture.NotARevenueName"],
                    SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD: reconciliation(
                        presentations[0],
                        "Auction revenue is the sum of all sale prices.",
                    ),
                },
                "caption_like_key": {
                    "source_kind": "definition",
                    "statement": (
                        "Truthfulness is dominant-strategy optimal reporting with other "
                        "reports fixed."
                    ),
                    "source_location": "source.txt:2",
                    "source_anchor_evidence": [truthful_anchor],
                    "lean_declarations": ["Fixture.UnrelatedSpelling"],
                    SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD: reconciliation(
                        presentations[1],
                        (
                            "Truthfulness is dominant-strategy optimal reporting with "
                            "other reports fixed."
                        ),
                    ),
                },
                "definition_in_key_only": {
                    "source_kind": "algorithm",
                    "statement": "Algorithm 3. Apply the update rule.",
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [algorithm_anchor],
                    "lean_declarations": ["Fixture.DefinitionInLeanName"],
                },
            },
        }

    def _paper(
        self,
        root: Path,
        payload: dict[str, object],
        *,
        source_text: str | None = None,
    ) -> Path:
        paper = root / "papers" / "FixturePaper"
        (paper / "audit").mkdir(parents=True)
        (paper / "source.txt").write_text(
            source_text if source_text is not None else self.SOURCE_TEXT,
            encoding="utf-8",
        )
        (paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(payload, indent=2) + "\n", encoding="utf-8"
        )
        return paper

    def test_current_source_only_prose_definitions_enter_normal_scope(self) -> None:
        payload = self._payload()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            selected = source_index_byte_pinned_anchor_item_ids(
                paper,
                payload,
                NAMED_THEORETICAL_STATEMENTS,
                repository_root=root,
            )
            self.assertEqual(
                selected, {"misleading_theorem_key", "caption_like_key"}
            )
            self.assertEqual(
                source_prose_definition_inventory_errors(
                    paper, payload, repository_root=root
                ),
                [],
            )

            _full, canonical, mode, error = review_dashboard.paper_coverage_inventory(
                paper
            )
            self.assertEqual(mode, NAMED_THEORETICAL_STATEMENTS)
            self.assertEqual(error, "")
            self.assertEqual(
                set(canonical), {"misleading_theorem_key", "caption_like_key"}
            )

    def test_prose_ledger_does_not_hide_unrelated_numbered_definitions(self) -> None:
        """One prose definition refines no other Definition heading by default."""

        source_text = (
            "Definition 1. A first object has the first property.\n"
            "\n"
            "Definition 2. A second object has the second property.\n"
            "\n"
            "Definition 3. A third object has the third property.\n"
            "\n"
            "4 Revenue setup\n"
            "We use R to denote auction revenue. R is the sum of all sale prices.\n"
        )

        def anchor(start: int, end: int | None = None) -> dict[str, object]:
            final = end or start
            quote = "\n".join(source_text.rstrip("\n").split("\n")[start - 1 : final])
            return {
                "path": "source.txt",
                "line_start": start,
                "line_end": final,
                "quoted_text": quote,
                "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
            }

        prose_clause = "We use R to denote auction revenue. R is the sum of all sale prices."
        prose_presentation = {
            "schema": 1,
            "presentation_kind": "definition",
            "defined_entity_kind": "object",
            "defined_object": "R",
            "definitional_clause": prose_clause,
            "scope_disposition": SOURCE_PROSE_DEFINITION_NORMAL_SCOPE,
            "source_anchor": anchor(8),
        }
        prose_statement = "Auction revenue is the sum of all sale prices."
        prose_reconciliation = {
            "schema": SOURCE_PROSE_DEFINITION_RECONCILIATION_SCHEMA,
            "relation": SOURCE_PROSE_DEFINITION_RECONCILIATION_RELATION,
            "presentation_sha256": source_prose_definition_presentation_sha256(
                prose_presentation
            ),
            "source_item_statement_sha256": source_prose_definition_statement_sha256(
                {"statement": prose_statement}
            ),
            "judgment": SOURCE_PROSE_DEFINITION_RECONCILIATION_JUDGMENT,
            "semantic_basis": "The exact prose clause defines auction revenue.",
            "validator": "independent prose-definition semantic judge",
            "validator_type": "human",
            "validated_at": "2026-08-19T00:00:00Z",
        }
        digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
        payload: dict[str, object] = {
            "schema": 1,
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": digest,
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "source_anchor_evidence_required": True,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "independent source-only named-result index",
                "validated_at": "2026-08-19T00:00:00Z",
                "method": "Independent source-heading and prose-definition inventory.",
                "source_artifact_sha256": digest,
                "prose_definition_presentations": [prose_presentation],
                "discovered_prose_definition_sha256": (
                    source_prose_definition_presentations_sha256([prose_presentation])
                ),
            },
            "items": {
                "first": {
                    "source_kind": "definition",
                    "claim_bearing": True,
                    "statement": "A first object has the first property.",
                    "source_anchor_evidence": [anchor(1)],
                    "lean_declarations": ["Fixture.first"],
                },
                "second": {
                    "source_kind": "definition",
                    "claim_bearing": True,
                    "statement": "A second object has the second property.",
                    "source_anchor_evidence": [anchor(3)],
                    "lean_declarations": ["Fixture.second"],
                },
                "third": {
                    "source_kind": "definition",
                    "claim_bearing": True,
                    "statement": "A third object has the third property.",
                    "source_anchor_evidence": [anchor(5)],
                    "lean_declarations": ["Fixture.third"],
                },
                "revenue": {
                    "source_kind": "definition",
                    "claim_bearing": True,
                    "statement": prose_statement,
                    "source_anchor_evidence": [anchor(8)],
                    "lean_declarations": ["Fixture.revenue"],
                    SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD: prose_reconciliation,
                },
            },
        }
        source_presentations = source_named_result_index.extract_named_result_presentations(
            source_text, source_format="text"
        )
        review = payload["source_named_result_inventory_review"]
        assert isinstance(review, dict)
        review["discovered_named_result_sha256"] = (
            integrity.named_result_presentations_sha256(
                [
                    presentation
                    for presentation in source_presentations
                    if integrity.source_named_presentation_in_coverage_scope(
                        presentation.kind, NAMED_THEORETICAL_STATEMENTS
                    )
                ]
            )
        )

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload, source_text=source_text)
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                {"first", "second", "third", "revenue"},
            )
            previous_root = integrity.ROOT
            integrity.ROOT = root
            try:
                self.assertEqual(
                    integrity.source_named_result_inventory_findings(
                        paper,
                        "formalized",
                        paper / "audit" / "paper_statement_map.json",
                        payload,
                    ),
                    [],
                )
            finally:
                integrity.ROOT = previous_root

    def test_kind_or_names_without_source_reconciliation_cannot_select(self) -> None:
        payload = self._payload()
        items = payload["items"]
        assert isinstance(items, dict)
        row = items["misleading_theorem_key"]
        assert isinstance(row, dict)
        row.pop(SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD)
        row["lean_declarations"] = ["Fixture.DefinitionRevenueTheorem"]

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("must reconcile to exactly one" in error for error in errors),
                errors,
            )
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                set(),
            )

    def test_semantic_judge_must_be_independent_from_inventory_extractor(self) -> None:
        payload = self._payload()
        review = payload["source_named_result_inventory_review"]
        items = payload["items"]
        assert isinstance(review, dict)
        assert isinstance(items, dict)
        row = items["misleading_theorem_key"]
        assert isinstance(row, dict)
        reconciliation = row[SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD]
        assert isinstance(reconciliation, dict)
        reconciliation["validator"] = review["validator"]

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("must be independent" in error for error in errors), errors
            )

    def test_prose_definition_inventory_must_be_explicit_even_when_empty(self) -> None:
        for missing_field in (
            SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD,
            SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD,
        ):
            with self.subTest(missing_field=missing_field):
                payload = self._payload()
                review = payload["source_named_result_inventory_review"]
                assert isinstance(review, dict)
                review.pop(missing_field)
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    paper = self._paper(root, payload)
                    errors = source_prose_definition_inventory_errors(
                        paper, payload, repository_root=root
                    )
                    self.assertTrue(errors)
                    self.assertEqual(
                        source_index_byte_pinned_anchor_item_ids(
                            paper,
                            payload,
                            NAMED_THEORETICAL_STATEMENTS,
                            repository_root=root,
                        ),
                        set(),
                    )

    def test_broad_anchor_cannot_reuse_judgment_for_changed_statement(self) -> None:
        payload = self._payload()
        items = payload["items"]
        assert isinstance(items, dict)
        row = items["misleading_theorem_key"]
        assert isinstance(row, dict)
        row["statement"] = "Truthful bidding is a dominant strategy."
        row["source_anchor_evidence"] = [self._anchor(self.SOURCE_TEXT, 1, 2)]

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("source_item_statement_sha256" in error for error in errors),
                errors,
            )
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                set(),
            )

    def test_prose_definition_anchor_rejects_absolute_or_parent_relative_path(
        self,
    ) -> None:
        for unsafe_path in ("../source.txt", "/source.txt", "C:/source.txt"):
            with self.subTest(unsafe_path=unsafe_path):
                payload = self._payload()
                review = payload["source_named_result_inventory_review"]
                assert isinstance(review, dict)
                presentations = review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD]
                assert isinstance(presentations, list)
                presentation = presentations[0]
                assert isinstance(presentation, dict)
                anchor = presentation["source_anchor"]
                assert isinstance(anchor, dict)
                anchor["path"] = unsafe_path
                review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
                    source_prose_definition_presentations_sha256(presentations)
                )
                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    paper = self._paper(root, payload)
                    errors = source_prose_definition_inventory_errors(
                        paper, payload, repository_root=root
                    )
                    self.assertTrue(
                        any("exact current source slice" in error for error in errors),
                        errors,
                    )

    def test_excluded_prose_definition_is_catalogued_without_normal_credit(self) -> None:
        payload = self._payload()
        review = payload["source_named_result_inventory_review"]
        assert isinstance(review, dict)
        presentations = review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD]
        assert isinstance(presentations, list)
        algorithm_anchor = self._anchor(self.SOURCE_TEXT, 3, 3)
        excluded = {
            "schema": 1,
            "presentation_kind": "definition",
            "defined_entity_kind": "object",
            "defined_object": "update rule",
            "definitional_clause": "Algorithm 3. Apply the update rule.",
            "scope_disposition": "computational_definition",
            "scope_reason": (
                "This is an algorithm-local computational instruction, not a "
                "paper-facing theoretical definition."
            ),
            "scope_judgment": SOURCE_PROSE_DEFINITION_EXCLUSION_JUDGMENT,
            "validator": "independent prose-definition scope judge",
            "validator_type": "agent",
            "validated_at": "2026-08-02T12:00:00Z",
            "source_anchor": algorithm_anchor,
        }
        excluded["scope_judgment_source_sha256"] = (
            source_prose_definition_clause_sha256(excluded)
        )
        presentations.append(excluded)
        review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
            source_prose_definition_presentations_sha256(presentations)
        )

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            self.assertEqual(
                source_prose_definition_inventory_errors(
                    paper, payload, repository_root=root
                ),
                [],
            )
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                {"misleading_theorem_key", "caption_like_key"},
            )

        original_clause = str(excluded["definitional_clause"])
        excluded["definitional_clause"] = (
            "Algorithm 3. Apply a materially different update rule."
        )
        review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
            source_prose_definition_presentations_sha256(presentations)
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("scope_judgment_source_sha256" in error for error in errors),
                errors,
            )
        excluded["definitional_clause"] = original_clause

        excluded["scope_reason"] = "local"
        review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
            source_prose_definition_presentations_sha256(presentations)
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            self.assertTrue(
                source_prose_definition_inventory_errors(
                    paper, payload, repository_root=root
                )
            )

        excluded["scope_reason"] = (
            "This broad classification is intentionally missing the explicit "
            "approval required for a catch-all deep-only exclusion."
        )
        excluded["scope_disposition"] = "deep_only_definition"
        excluded["scope_judgment_source_sha256"] = (
            source_prose_definition_clause_sha256(excluded)
        )
        review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
            source_prose_definition_presentations_sha256(presentations)
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("requires explicit" in error for error in errors), errors
            )

    def test_repeated_definition_presentation_reuses_one_semantic_obligation(
        self,
    ) -> None:
        source_text = self.SOURCE_TEXT + (
            "For clarity, R denotes auction revenue, the sum of all sale prices.\n"
        )
        payload = self._payload()
        source_digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
        payload["source_artifact_sha256"] = source_digest
        review = payload["source_named_result_inventory_review"]
        assert isinstance(review, dict)
        review["source_artifact_sha256"] = source_digest
        presentations = review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD]
        assert isinstance(presentations, list)
        canonical = presentations[0]
        assert isinstance(canonical, dict)
        repeated = {
            "schema": 1,
            "presentation_kind": "definition",
            "defined_entity_kind": "object",
            "defined_object": "R",
            "definitional_clause": (
                "For clarity, R denotes auction revenue, the sum of all sale prices."
            ),
            "scope_disposition": SOURCE_PROSE_DEFINITION_REPEATED_SCOPE,
            "canonical_presentation_sha256": (
                source_prose_definition_presentation_sha256(canonical)
            ),
            "repetition_judgment": SOURCE_PROSE_DEFINITION_REPETITION_JUDGMENT,
            "semantic_basis": (
                "The later clause restates the same revenue object and sum-of-sale-"
                "prices definition without changing its domain or operation."
            ),
            "validator": "independent repeated-definition fixture reviewer",
            "validator_type": "agent",
            "validated_at": "2026-08-02T12:00:00Z",
            "source_anchor": self._anchor(source_text, 4, 4),
        }
        repeated["repetition_judgment_source_sha256"] = (
            source_prose_definition_clause_sha256(repeated)
        )
        presentations.append(repeated)
        review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
            source_prose_definition_presentations_sha256(presentations)
        )

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload, source_text=source_text)
            self.assertEqual(
                source_prose_definition_inventory_errors(
                    paper, payload, repository_root=root
                ),
                [],
            )
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                {"misleading_theorem_key", "caption_like_key"},
            )

        repeated["canonical_presentation_sha256"] = "f" * 64
        review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
            source_prose_definition_presentations_sha256(presentations)
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload, source_text=source_text)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("does not designate a presentation" in error for error in errors),
                errors,
            )

    def test_stale_clause_or_ambiguous_binding_fails_closed(self) -> None:
        for mutation in ("stale_source", "duplicate_binding"):
            with self.subTest(mutation=mutation):
                payload = self._payload()
                if mutation == "stale_source":
                    review = payload["source_named_result_inventory_review"]
                    assert isinstance(review, dict)
                    presentations = review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD]
                    assert isinstance(presentations, list)
                    presentation = presentations[0]
                    assert isinstance(presentation, dict)
                    presentation["definitional_clause"] = "R is unrelated text."
                    review[SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD] = (
                        source_prose_definition_presentations_sha256(presentations)
                    )
                else:
                    items = payload["items"]
                    assert isinstance(items, dict)
                    duplicate = deepcopy(items["misleading_theorem_key"])
                    duplicate["lean_declarations"] = ["Fixture.DifferentNavigation"]
                    items["second_opaque_coordinate"] = duplicate

                with tempfile.TemporaryDirectory() as tmp:
                    root = Path(tmp)
                    paper = self._paper(root, payload)
                    errors = source_prose_definition_inventory_errors(
                        paper, payload, repository_root=root
                    )
                    self.assertTrue(errors)
                    self.assertEqual(
                        source_index_byte_pinned_anchor_item_ids(
                            paper,
                            payload,
                            NAMED_THEORETICAL_STATEMENTS,
                            repository_root=root,
                        ),
                        set(),
                    )

    def test_map_key_and_lean_route_renames_do_not_change_semantic_selection(
        self,
    ) -> None:
        first = self._payload()
        second = deepcopy(first)
        second_items = second["items"]
        assert isinstance(second_items, dict)
        moved = second_items.pop("misleading_theorem_key")
        assert isinstance(moved, dict)
        moved["lean_declarations"] = ["Fixture.RenamedNavigationOnly"]
        second_items["opaque_coordinate_94"] = moved

        selected_statements: list[set[str]] = []
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for index, payload in enumerate((first, second)):
                paper = self._paper(root / str(index), payload)
                selected = source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root / str(index),
                )
                items = payload["items"]
                assert isinstance(items, dict)
                selected_statements.append(
                    {
                        str(items[item_id]["statement"])
                        for item_id in selected
                        if isinstance(items[item_id], dict)
                    }
                )
        self.assertEqual(selected_statements[0], selected_statements[1])

    def test_reviewer_credentials_do_not_change_semantic_reuse_identity(self) -> None:
        first = self._payload()
        second = deepcopy(first)
        second_items = second["items"]
        assert isinstance(second_items, dict)
        second_item = second_items["misleading_theorem_key"]
        assert isinstance(second_item, dict)
        reconciliation = second_item[SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD]
        assert isinstance(reconciliation, dict)
        reconciliation["semantic_basis"] = (
            "A different reviewer explanation of the same pinned source-clause "
            "and map-statement equivalence."
        )
        reconciliation["validator"] = "replacement independent semantic judge"
        reconciliation["validator_type"] = "human"
        reconciliation["validated_at"] = "2026-08-03T12:00:00Z"

        first_items = first["items"]
        assert isinstance(first_items, dict)
        first_item = first_items["misleading_theorem_key"]
        assert isinstance(first_item, dict)
        self.assertEqual(
            source_item_coverage_sha256(
                first_item, NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                second_item, NAMED_THEORETICAL_STATEMENTS
            ),
        )
        self.assertEqual(
            source_map_cache_semantic_sha256(first),
            source_map_cache_semantic_sha256(second),
        )

        reconciliation["judgment"] = "not_equivalent"
        self.assertNotEqual(
            source_item_coverage_sha256(
                first_item, NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                second_item, NAMED_THEORETICAL_STATEMENTS
            ),
        )


if __name__ == "__main__":
    unittest.main()
