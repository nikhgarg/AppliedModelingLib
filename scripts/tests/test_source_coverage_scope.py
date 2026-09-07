#!/usr/bin/env python3
"""Regression tests for source-semantic coverage-scope selection."""

from __future__ import annotations

import hashlib
import importlib.util
import sys
import unittest
from copy import deepcopy
import json
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

from source_coverage_scope import (  # noqa: E402
    DEFAULT_SOURCE_COVERAGE_MODE,
    DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
    LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    NAMED_THEORETICAL_STATEMENTS,
    PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    deep_source_coverage_attestation_error,
    explicit_raw_source_spec_screening_requested,
    filter_source_inventory_for_coverage,
    filter_source_map_items_for_coverage,
    source_named_result_environment_kinds_from_map,
    source_coverage_mode_from_map,
    source_coverage_modes_compatible,
    source_item_coverage_sha256,
    source_item_coverage_receipt_matches,
    source_item_direct_status_policy_projection,
    source_item_effective_route_policy,
    source_item_is_named_theoretical_statement,
    source_record_human_review_semantic_sha256,
    source_record_source_item_projection,
    source_record_source_item_record_sha256,
    source_record_source_item_semantic_sha256,
    source_record_source_item_supported_identity_sha256s,
    legacy_source_item_coverage_sha256_before_navigation_key_exclusion,
    legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion,
    legacy_source_item_coverage_sha256_before_direct_source_status_exclusion,
    legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
    legacy_source_map_cache_semantic_sha256,
    source_item_scope_classification_errors,
    source_index_byte_pinned_anchor_item_ids,
    source_map_cache_semantic_projection,
    source_map_cache_semantic_sha256,
    source_map_structural_errors,
    source_named_presentation_in_coverage_scope,
    source_presentation_aliases,
    source_map_uses_conditional_antecedent_subpart_selection,
)
from corrected_target_identity import (  # noqa: E402
    CORRECTED_TARGET_APPROVAL_PROTOCOL,
    CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD,
    corrected_target_approval_artifact_error,
    corrected_target_record_digest,
    corrected_target_review_digest,
)
import new_paper  # noqa: E402
import review_dashboard  # noqa: E402
import source_coverage_scope as coverage_scope  # noqa: E402


SOURCE_DIGEST = "a" * 64
SOURCE_RECORD_AUDIT_PATH = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)
SOURCE_RECORD_AUDIT_SPEC = importlib.util.spec_from_file_location(
    "coverage_scope_source_record_audit", SOURCE_RECORD_AUDIT_PATH
)
assert SOURCE_RECORD_AUDIT_SPEC is not None and SOURCE_RECORD_AUDIT_SPEC.loader is not None
SOURCE_RECORD_AUDIT = importlib.util.module_from_spec(SOURCE_RECORD_AUDIT_SPEC)
sys.modules[SOURCE_RECORD_AUDIT_SPEC.name] = SOURCE_RECORD_AUDIT
SOURCE_RECORD_AUDIT_SPEC.loader.exec_module(SOURCE_RECORD_AUDIT)


class SourceCoverageScopeTests(unittest.TestCase):
    def test_repeated_prose_alias_requires_current_independent_source_binding(self) -> None:
        from tempfile import TemporaryDirectory

        source = "Call a value positive when it exceeds zero.\nAgain, positive means exceeding zero.\n"
        digest = hashlib.sha256(source.encode()).hexdigest()
        lines = source.splitlines()

        def anchor(line: int) -> dict:
            return {
                "path": "source.txt", "line_start": line, "line_end": line,
                "quoted_text": lines[line - 1],
                "quoted_text_sha256": hashlib.sha256(lines[line - 1].encode()).hexdigest(),
            }

        canonical = {
            "schema": 1, "presentation_kind": "definition",
            "defined_entity_kind": "predicate", "defined_object": "positive",
            "definitional_clause": lines[0], "source_anchor": anchor(1),
            "scope_disposition": "normal_named_theory_definition",
        }
        repeated = {
            **canonical, "definitional_clause": lines[1], "source_anchor": anchor(2),
            "scope_disposition": "repeated_normal_definition",
            "canonical_presentation_sha256": coverage_scope.source_prose_definition_presentation_sha256(canonical),
            "repetition_judgment": "semantically_equivalent_restatement",
            "semantic_basis": "Both clauses define positivity by the identical strict comparison with zero.",
            "validator": "independent repetition reviewer", "validator_type": "agent",
            "validated_at": "2026-09-07T00:00:00Z",
        }
        repeated["repetition_judgment_source_sha256"] = coverage_scope.source_prose_definition_clause_sha256(repeated)
        item = {
            "source_kind": "definition", "statement": lines[0], "claim_bearing": True,
            "source_location": "source.txt:1", "source_anchor_evidence": [anchor(1)],
        }
        item["source_prose_definition_reconciliation"] = {
            "schema": 2, "relation": "source_item_represents_prose_definition",
            "presentation_sha256": coverage_scope.source_prose_definition_presentation_sha256(canonical),
            "source_item_statement_sha256": coverage_scope.source_item_statement_sha256(item),
            "judgment": "semantically_equivalent",
            "semantic_basis": "The source-map statement is exactly the first pinned source clause.",
            "validator": "independent binding reviewer", "validator_type": "agent",
            "validated_at": "2026-09-07T00:00:00Z",
        }
        alias = {
            "source_kind": "definition", "statement": lines[1],
            "source_location": "source.txt:2", "source_anchor_evidence": [anchor(2)],
            "source_presentation_alias": {
                "schema": 1, "relation": "repeated_source_presentation",
                "canonical_source_item": "canonical", "semantic_basis": repeated["semantic_basis"],
                "validator": "independent repetition reviewer", "validated_at": "2026-09-07T00:00:00Z",
            },
        }
        payload = {
            "source_artifact_path": "source.txt", "source_artifact_sha256": digest,
            "items": {"canonical": item, "repeat": alias},
            "source_named_result_inventory_review": {
                "complete": True, "validator": "source-only extractor",
                "source_artifact_sha256": digest,
                "prose_definition_presentations": [canonical, repeated],
            },
        }

        def refresh_inventory(value: dict) -> None:
            review = value["source_named_result_inventory_review"]
            review["discovered_prose_definition_sha256"] = coverage_scope.source_prose_definition_presentations_sha256(review["prose_definition_presentations"])

        refresh_inventory(payload)
        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "source.txt").write_text(source)
            self.assertEqual(coverage_scope.source_prose_definition_inventory_errors(folder, payload), [])
            self.assertEqual(coverage_scope.source_prose_definition_alias_pairs(folder, payload), {"repeat": "canonical"})
            # Neither a stale reading nor an unrelated source span can acquire
            # the exemption from numbered-heading reconciliation.
            for mutation in ("stale", "wrong_span", "self_review", "wrong_canonical"):
                with self.subTest(mutation=mutation):
                    changed = deepcopy(payload)
                    record = changed["source_named_result_inventory_review"]["prose_definition_presentations"][1]
                    if mutation == "stale":
                        record["repetition_judgment_source_sha256"] = "0" * 64
                    elif mutation == "wrong_span":
                        changed["items"]["repeat"]["source_anchor_evidence"] = [anchor(1)]
                    elif mutation == "self_review":
                        record["validator"] = "source-only extractor"
                    else:
                        record["canonical_presentation_sha256"] = "0" * 64
                    refresh_inventory(changed)
                    self.assertEqual(coverage_scope.source_prose_definition_alias_pairs(folder, changed), {})

    @staticmethod
    def approved_corrected_target(
        artifact_path: str = "docs/SOURCE_CLARIFICATIONS.md",
    ) -> dict[str, object]:
        excerpt = (
            "The task owner approved this exact corrected mathematical target "
            "for the formalization."
        )
        target: dict[str, object] = {
            "schema": 1,
            "statement": "For every x, the corrected conclusion holds.",
            "governing_defect_ids": ["FIXTURE-DEFECT-1"],
            "archival_equivalence_claimed": False,
            "archival_source_locator": "sources/Fixture.txt:40-43",
            "archival_source_quote_sha256": "b" * 64,
            "approval": {
                "kind": "explicit_user_instruction",
                "recorded_at": "2026-09-05",
                "reference": "Approved corrected target.",
                "target_statement_sha256": hashlib.sha256(
                    b"For every x, the corrected conclusion holds."
                ).hexdigest(),
                "artifact_path": artifact_path,
                "artifact_protocol": CORRECTED_TARGET_APPROVAL_PROTOCOL,
                "artifact_excerpt": excerpt,
                "artifact_excerpt_sha256": hashlib.sha256(
                    excerpt.encode("utf-8")
                ).hexdigest(),
            },
        }
        target["corrected_target_sha256"] = corrected_target_record_digest(target)
        target["corrected_target_review_sha256"] = corrected_target_review_digest(
            target
        )
        return target

    def test_explicit_v11_activation_spellings_share_one_predicate(self) -> None:
        statuses = (
            {"review_surface": {"require_source_spec_correspondence": True}},
            {"review_surface": {"require_v11_raw_source_spec_screening": True}},
            {
                "review_surface": {
                    "llm_statement_review": {
                        "require_theorem_realization_contract_schema": 1
                    }
                }
            },
        )
        for status in statuses:
            with self.subTest(status=status):
                self.assertTrue(
                    explicit_raw_source_spec_screening_requested(status)
                )
        self.assertTrue(
            explicit_raw_source_spec_screening_requested(
                {}, {"source_spec_correspondence_schema": 1}
            )
        )
        self.assertFalse(
            explicit_raw_source_spec_screening_requested(
                {"review_surface": {"require_source_spec_correspondence": False}},
                {"source_spec_correspondence_schema": True},
            )
        )

    def test_named_open_problem_is_not_an_ordinary_proof_obligation(self) -> None:
        quote = "Conjecture 1. Every admissible input has a witness."
        item = {
            "source_kind": "open_problem",
            "claim_bearing": False,
            "source_location": "source.txt:1",
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                }
            ],
            "source_scope_classification": (
                "source_declared_open_nonresult_observation"
            ),
            "coverage_status": "source_declared_open",
            "protocol_role": "source_declared_open",
            "scope_reason": "The paper explicitly presents this as open.",
            "source_evidence": "The byte-pinned source labels it Conjecture 1.",
        }

        self.assertFalse(source_item_is_named_theoretical_statement(item))
        self.assertEqual(source_item_scope_classification_errors(item), [])

    @staticmethod
    def _valid_repeated_presentation_alias_items() -> dict[str, dict[str, object]]:
        """Minimal source metadata for one repeated named presentation."""

        return {
            "main_theorem": {
                "source_kind": "theorem",
                "source_location": "source.txt:10-12",
            },
            "appendix_restatement": {
                "source_kind": "theorem",
                "source_location": "source.txt:100-102",
                "source_presentation_alias": {
                    "schema": 1,
                    "relation": "repeated_source_presentation",
                    "canonical_source_item": "main_theorem",
                    "semantic_basis": (
                        "The two source-pinned presentations have the same "
                        "hypotheses, scope, and conclusion."
                    ),
                    "validator": "independent-source-review",
                    "validated_at": "2026-07-27T12:00:00Z",
                },
            },
        }

    def test_repeated_presentation_alias_maps_to_route_free_same_kind_canonical(
        self,
    ) -> None:
        aliases, errors = source_presentation_aliases(
            self._valid_repeated_presentation_alias_items()
        )

        self.assertEqual(aliases, {"appendix_restatement": "main_theorem"})
        self.assertEqual(errors, [])

    def test_repeated_presentation_alias_is_not_a_second_coverage_obligation(
        self,
    ) -> None:
        items = self._valid_repeated_presentation_alias_items()
        for item in items.values():
            item["statement"] = "Theorem 1. Every input has a witness."

        selected = filter_source_inventory_for_coverage(
            items, NAMED_THEORETICAL_STATEMENTS
        )

        self.assertEqual(set(selected), {"main_theorem"})

    def test_conditional_subpart_feature_is_source_grammar_and_mode_scoped(
        self,
    ) -> None:
        source_text = (
            "Proposition 1. Suppose the model has finite support.\n"
            "(i) The first condition holds.\n"
            "(ii) The second condition holds.\n"
            "Then the optimizer is unique.\n"
        )
        payload = {
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "items": {
                # The opaque source-map key and deliberately unrelated Lean
                # route must not decide whether this source grammar is used.
                "unrelated_row_key": {
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 1,
                            "line_end": 4,
                            "quoted_text": source_text,
                            "quoted_text_sha256": hashlib.sha256(
                                source_text.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                    "lean_declarations": ["Fixture.unrelatedRoute"],
                }
            },
        }

        self.assertTrue(
            source_map_uses_conditional_antecedent_subpart_selection(payload)
        )
        payload["source_coverage_mode"] = DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        self.assertFalse(
            source_map_uses_conditional_antecedent_subpart_selection(payload)
        )

    def test_source_index_reconciles_alias_while_coverage_counts_only_canonical(
        self,
    ) -> None:
        """A verified repeated presentation is needed for reconciliation, not coverage."""

        from tempfile import TemporaryDirectory

        source_text = (
            "Theorem 1. Every admissible input has a witness.\n"
            "Theorem 1. Every admissible input has a witness.\n"
        )
        source_digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "RepeatedPresentationPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "source.txt").write_text(source_text, encoding="utf-8")

            def anchor(line: int) -> dict[str, object]:
                quoted = source_text.splitlines()[line - 1]
                return {
                    "path": "source.txt",
                    "line_start": line,
                    "line_end": line,
                    "quoted_text": quoted,
                    "quoted_text_sha256": hashlib.sha256(
                        quoted.encode("utf-8")
                    ).hexdigest(),
                }

            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": source_digest,
                "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                "items": {
                    "canonical": {
                        "source_kind": "theorem",
                        "statement": "Theorem 1. Every admissible input has a witness.",
                        "source_location": "source.txt:1",
                        "source_url": "https://example.invalid/paper",
                        "source_anchor_evidence": [anchor(1)],
                        "lean_declarations": ["Fixture.canonical"],
                    },
                    "appendix_restatement": {
                        "source_kind": "theorem",
                        "statement": "Theorem 1. Every admissible input has a witness.",
                        "source_location": "source.txt:2",
                        "source_url": "https://example.invalid/paper",
                        "source_anchor_evidence": [anchor(2)],
                        "source_presentation_alias": {
                            "schema": 1,
                            "relation": "repeated_source_presentation",
                            "canonical_source_item": "canonical",
                            "semantic_basis": (
                                "The two exact source presentations have the same "
                                "hypotheses, scope, and conclusion."
                            ),
                            "validator": "fixture source reconciliation",
                            "validated_at": "2026-07-27T12:00:00Z",
                        },
                    },
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )

            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    folder,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=ROOT,
                ),
                {"canonical", "appendix_restatement"},
            )
            _full, selected, _mode, error = review_dashboard.paper_coverage_inventory(
                folder
            )
            self.assertEqual(error, "")
            self.assertEqual(set(selected), {"canonical"})

    def test_source_index_uses_one_reviewed_candidate_classification(self) -> None:
        """Material candidates enter coverage; reviewed deep material does not."""

        from tempfile import TemporaryDirectory

        source_text = (
            "Theorem 1. Every admissible input has a witness.\n"
            "Remark 4. The witness is unique under strict preferences.\n"
            "Note 5. This paragraph gives historical motivation only.\n"
        )
        source_digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ReviewedCandidatePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "source.txt").write_text(source_text, encoding="utf-8")

            def anchor(line: int) -> dict[str, object]:
                quoted = source_text.splitlines()[line - 1]
                return {
                    "path": "source.txt",
                    "line_start": line,
                    "line_end": line,
                    "quoted_text": quoted,
                    "quoted_text_sha256": hashlib.sha256(
                        quoted.encode("utf-8")
                    ).hexdigest(),
                }

            candidates = [
                {
                    "schema": 1,
                    "id": "remark4",
                    "presentation_label": "Remark 4",
                    "visible_kind": "remark",
                    "scope_disposition": "material_named_claim",
                    "semantic_basis": (
                        "The source presents a distinct uniqueness conclusion."
                    ),
                    "discovery_basis": "mechanical_labelled_heading",
                    "source_anchor": anchor(2),
                },
                {
                    "schema": 1,
                    "id": "note5",
                    "presentation_label": "Note 5",
                    "visible_kind": "note",
                    "scope_disposition": "deep_audit_material",
                    "semantic_basis": (
                        "The passage is historical motivation and states no paper claim."
                    ),
                    "discovery_basis": "mechanical_labelled_heading",
                    "source_anchor": anchor(3),
                },
            ]
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": source_digest,
                "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                "source_named_result_inventory_review": {
                    "candidate_presentations": candidates,
                },
                "items": {
                    "theorem": {
                        "source_kind": "theorem",
                        "source_anchor_evidence": [anchor(1)],
                    },
                    "material_remark": {
                        "source_kind": "claim",
                        "source_anchor_evidence": [anchor(2)],
                    },
                    "deep_note": {
                        "source_kind": "note",
                        "source_anchor_evidence": [anchor(3)],
                    },
                },
            }

            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    folder,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=ROOT,
                ),
                {"theorem", "material_remark"},
            )

    def test_repeated_presentation_alias_rejects_direct_lean_route(self) -> None:
        items = self._valid_repeated_presentation_alias_items()
        # The field, rather than the declaration spelling, is the source-map
        # route metadata that makes this alias invalid.
        items["appendix_restatement"]["lean_declarations"] = ["unused-route"]

        _aliases, errors = source_presentation_aliases(items)

        self.assertTrue(
            any(
                "alias item must not own direct `lean_declarations` routes" in error
                for error in errors
            ),
            errors,
        )

    def test_renumbered_presentation_alias_requires_explicit_relation_evidence(
        self,
    ) -> None:
        items = self._valid_repeated_presentation_alias_items()
        relation = items["appendix_restatement"]["source_presentation_alias"]
        assert isinstance(relation, dict)
        relation["label_relation"] = "source_explicit_renumbered_restatement"

        _aliases, errors = source_presentation_aliases(items)

        self.assertTrue(
            any("source_restatement_evidence" in error for error in errors), errors
        )

    def test_repeated_presentation_alias_rejects_alias_to_alias_and_cycle(
        self,
    ) -> None:
        with self.subTest("alias_to_alias"):
            items = self._valid_repeated_presentation_alias_items()
            items["appendix_repetition"] = {
                "source_kind": "theorem",
                "source_location": "source.txt:200-202",
                "source_presentation_alias": {
                    "schema": 1,
                    "relation": "repeated_source_presentation",
                    "canonical_source_item": "appendix_restatement",
                    "semantic_basis": "A second repeated source presentation.",
                    "validator": "independent-source-review",
                    "validated_at": "2026-07-27T12:00:00Z",
                },
            }

            _aliases, errors = source_presentation_aliases(items)

            self.assertTrue(
                any(
                    "canonical_source_item `appendix_restatement` cannot itself "
                    "be a presentation alias" in error
                    for error in errors
                ),
                errors,
            )

        with self.subTest("cycle"):
            items = self._valid_repeated_presentation_alias_items()
            items["main_theorem"]["source_presentation_alias"] = {
                "schema": 1,
                "relation": "repeated_source_presentation",
                "canonical_source_item": "appendix_restatement",
                "semantic_basis": "Invalid cyclic source metadata.",
                "validator": "independent-source-review",
                "validated_at": "2026-07-27T12:00:00Z",
            }

            _aliases, errors = source_presentation_aliases(items)

            self.assertTrue(
                any(
                    "cannot itself be a presentation alias" in error
                    for error in errors
                ),
                errors,
            )

    def test_missing_mode_defaults_to_named_source_theory(self) -> None:
        mode, error = source_coverage_mode_from_map({"items": {}})

        self.assertEqual(mode, NAMED_THEORETICAL_STATEMENTS)
        self.assertEqual(error, "")

    def test_named_theory_selection_uses_source_presentation_not_map_or_lean_names(
        self,
    ) -> None:
        inventory = {
            # The deliberately misleading key and Lean route must not exclude a
            # source-labelled theorem.
            "figure_caption_named_key": {
                "source_kind": "theorem",
                "statement": "Theorem 1. The endpoint holds.",
                "lean_declarations": ["Fixture.caption_helper"],
            },
            # Conversely, a source example does not enter ordinary coverage just
            # because its key or direct route happens to contain theorem-like text.
            "Theorem_999_but_not_a_source_theorem": {
                "source_kind": "example",
                "statement": "Numerical illustration.",
                "lean_declarations": ["Fixture.mainTheorem"],
            },
            "definition": {"source_kind": "definition", "statement": "Definition 2."},
            "named_claim": {
                "source_kind": "claim",
                "statement": "Claim 2. The endpoint holds.",
            },
            "unnumbered_prose_claim": {
                "source_kind": "claim",
                "statement": "The source says that the endpoint holds.",
            },
            "equation_mislabeled_as_claim": {
                "source_kind": "claim",
                "statement": "Equation (C.1) states the displayed comparison.",
            },
            "formula": {"source_kind": "formula", "statement": "Equation (6)."},
            "caption_navigation_for_lettered_formula": {
                "source_kind": "formula",
                "statement": "Formula A gives the source-level comparison.",
                "lean_declarations": ["Fixture.figureCaption"],
            },
            "algorithmic_formula": {
                "source_kind": "algorithmic_formula",
                "statement": "Algorithmic Formula 1 gives the update rule.",
            },
            "algorithm": {"source_kind": "algorithm", "statement": "Algorithm 3."},
            "assumption": {"source_kind": "assumption", "statement": "Assumption A."},
            "legacy_label_only": {"title": "Lemma 7", "statement": "A legacy lemma."},
            "model": {"source_kind": "model", "statement": "Model setup."},
            "remark": {"source_kind": "remark", "statement": "Remark 4."},
            "prose": {"source_kind": "prose", "statement": "An unlabelled claim."},
            "nonclaim": {
                "source_kind": "theorem",
                "claim_bearing": False,
                "statement": "A source theorem with an invalid non-claim classification.",
            },
            # A curator-provided theorem category cannot turn a visible support
            # formula into an ordinary theorem obligation.
            "formula_support_mislabeled_as_theorem": {
                "source_kind": "theorem",
                "statement": "Equation (9). A support identity.",
                "lean_declarations": ["Fixture.UnrelatedTheoremRoute"],
            },
        }

        selected = filter_source_inventory_for_coverage(
            inventory, NAMED_THEORETICAL_STATEMENTS
        )

        self.assertEqual(
            set(selected),
            {
                "figure_caption_named_key",
                "definition",
                "named_claim",
                "assumption",
                "legacy_label_only",
            },
        )

    def test_named_theory_selection_accepts_only_matching_source_heading_or_pinned_environment(
        self,
    ) -> None:
        theorem_anchor = "\\begin{theorem}\\label{thm:main}\nEvery input has a witness.\n\\end{theorem}"
        restatable_anchor = (
            "\\begin{restatable}{theorem}{opaqueMacroName}\\label{thm:restated}\n"
            "Every input has a witness.\n"
            "\\end{restatable}"
        )
        inventory = {
            "metadata_only": {
                "source_kind": "theorem",
                "statement": "Every input has a witness.",
            },
            "wrong_visible_kind": {
                "source_kind": "theorem",
                "statement": "Definition 1. A witness is a designated input.",
            },
            "pinned_standard_environment": {
                "source_kind": "theorem",
                "statement": "Every input has a witness.",
                "source_anchor_evidence": [
                    {
                        "path": "source.tex",
                        "line_start": 10,
                        "line_end": 12,
                        "quoted_text": theorem_anchor,
                        "quoted_text_sha256": hashlib.sha256(
                            theorem_anchor.encode("utf-8")
                        ).hexdigest(),
                    }
                ],
            },
            "pinned_restatable_environment": {
                "source_kind": "theorem",
                "statement": "Every input has a witness.",
                "source_anchor_evidence": [
                    {
                        "path": "source.tex",
                        "line_start": 20,
                        "line_end": 22,
                        "quoted_text": restatable_anchor,
                        "quoted_text_sha256": hashlib.sha256(
                            restatable_anchor.encode("utf-8")
                        ).hexdigest(),
                    }
                ],
            },
            "unhashed_environment": {
                "source_kind": "theorem",
                "statement": "Every input has a witness.",
                "source_anchor_evidence": [
                    {
                        "path": "source.tex",
                        "line_start": 30,
                        "line_end": 32,
                        "quoted_text": theorem_anchor,
                        "quoted_text_sha256": "0" * 64,
                    }
                ],
            },
        }

        selected = filter_source_inventory_for_coverage(
            inventory, NAMED_THEORETICAL_STATEMENTS
        )

        self.assertEqual(
            set(selected),
            {"pinned_standard_environment", "pinned_restatable_environment"},
        )

    def test_standalone_formula_equation_and_algorithm_are_deep_only(self) -> None:
        ordinary_equation = (
            "\\begin{equation}\\label{eq:ordinary}\n"
            "x = y\n"
            "\\end{equation}"
        )
        tagged_equation = (
            "\\begin{equation}\\tag{Equation 1}\n"
            "x = y\n"
            "\\end{equation}"
        )
        inventory = {
            "bare_rendered_number": {
                "source_kind": "formula",
                "statement": "(C.9)",
            },
            "ordinary_latex_equation": {
                "source_kind": "equation",
                "source_anchor_evidence": [
                    {
                        "path": "source.tex",
                        "line_start": 1,
                        "line_end": 3,
                        "quoted_text": ordinary_equation,
                        "quoted_text_sha256": hashlib.sha256(
                            ordinary_equation.encode("utf-8")
                        ).hexdigest(),
                    }
                ],
            },
            "tagged_named_equation": {
                "source_kind": "formula",
                "source_anchor_evidence": [
                    {
                        "path": "source.tex",
                        "line_start": 4,
                        "line_end": 6,
                        "quoted_text": tagged_equation,
                        "quoted_text_sha256": hashlib.sha256(
                            tagged_equation.encode("utf-8")
                        ).hexdigest(),
                    }
                ],
            },
            "visible_formula_heading": {
                "source_kind": "equation",
                "statement": "Formula A gives the source-level comparison.",
            },
            "algorithmic_formula": {
                "source_kind": "algorithmic_formula",
                "statement": "Algorithmic Formula 1 gives the update rule.",
            },
            "algorithm": {
                "source_kind": "algorithm",
                "statement": "Algorithm 3 gives an update procedure.",
            },
        }

        normal_selected = filter_source_inventory_for_coverage(
            inventory, NAMED_THEORETICAL_STATEMENTS
        )
        deep_selected = filter_source_inventory_for_coverage(
            inventory, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        )

        self.assertEqual(normal_selected, {})
        self.assertEqual(set(deep_selected), set(inventory))
        self.assertFalse(
            source_named_presentation_in_coverage_scope(
                "formula", NAMED_THEORETICAL_STATEMENTS
            )
        )
        self.assertFalse(
            source_named_presentation_in_coverage_scope(
                "equation", NAMED_THEORETICAL_STATEMENTS
            )
        )
        self.assertFalse(
            source_named_presentation_in_coverage_scope(
                "algorithmic_formula", NAMED_THEORETICAL_STATEMENTS
            )
        )
        self.assertFalse(
            source_named_presentation_in_coverage_scope(
                "algorithm", NAMED_THEORETICAL_STATEMENTS
            )
        )
        self.assertTrue(
            source_named_presentation_in_coverage_scope(
                "unclassified", NAMED_THEORETICAL_STATEMENTS
            )
        )

    def test_numbered_proof_equations_are_deep_only_in_selection_and_precheck(
        self,
    ) -> None:
        """A DSWG-style proof derivation is not thirty extra named results."""

        inventory = {
            f"opaque_navigation_{number}": {
                "source_kind": "equation",
                "claim_bearing": False,
                "statement": (
                    f"Equation ({number}): one intermediate equality in the "
                    "proof of the selected theorem."
                ),
                # Deliberately theorem-like navigation must not affect scope.
                "lean_declarations": [f"Fixture.theoremProofStep{number}"],
            }
            for number in range(4, 34)
        }

        self.assertEqual(
            filter_source_inventory_for_coverage(
                inventory, NAMED_THEORETICAL_STATEMENTS
            ),
            {},
        )
        self.assertEqual(
            {
                key: source_item_scope_classification_errors(item)
                for key, item in inventory.items()
                if source_item_scope_classification_errors(item)
            },
            {},
        )
        self.assertEqual(
            set(
                filter_source_inventory_for_coverage(
                    inventory, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
                )
            ),
            set(inventory),
        )

    def test_deep_display_kind_cannot_hide_visible_theorem_presentation(self) -> None:
        """Scope follows the source presentation, not curator classification."""

        for source_kind in (
            "formula",
            "equation",
            "algorithm",
            "algorithmic_formula",
        ):
            with self.subTest(source_kind=source_kind):
                item = {
                    "source_kind": source_kind,
                    "claim_bearing": False,
                    "statement": "Theorem 4. Every feasible input has an allocation.",
                }
                self.assertTrue(source_item_is_named_theoretical_statement(item))
                errors = source_item_scope_classification_errors(item)
                self.assertTrue(
                    any("conflicts with a named theoretical" in error for error in errors)
                )
                self.assertTrue(
                    any("claim_bearing: false" in error for error in errors)
                )

    def test_named_proof_support_role_does_not_decide_source_classification(self) -> None:
        for label in ("Lemma 4.1", "Theorem 2", "Proposition A.1"):
            with self.subTest(label=label):
                item = {
                    "source_kind": label.split()[0].lower(),
                    "statement": f"{label}. Every feasible input has a witness.",
                    "claim_bearing": True,
                    "source_status": "support_only",
                    "inventory_role": "proof_support",
                    "support_lean_declarations": ["Fixture.downstreamTheoremSpec"],
                }
                errors = source_map_structural_errors({"intermediate": item})
                self.assertEqual(errors, [])
                self.assertTrue(source_item_is_named_theoretical_statement(item))
                item["claim_bearing"] = False
                self.assertTrue(any(
                    "claim_bearing: false" in error
                    for error in source_map_structural_errors({"intermediate": item})
                ))

    def test_unnumbered_proof_support_and_named_direct_routes_remain_valid(self) -> None:
        support = {
            "source_kind": "equation",
            "statement": "An intermediate equality in the proof of Theorem 2.",
            "claim_bearing": False,
            "source_status": "support_only",
            "inventory_role": "proof_support",
            "support_lean_declarations": ["Fixture.downstreamTheoremSpec"],
        }
        result = {
            "source_kind": "lemma",
            "statement": "Lemma 1. Every feasible input has a witness.",
            "claim_bearing": True,
        }
        for item in (support, result):
            with self.subTest(item=item):
                self.assertEqual(source_item_scope_classification_errors(item), [])

    def test_typed_nonclaim_algorithm_prerequisite_stays_off_result_surface(self) -> None:
        """A reviewable algorithm prerequisite is not a duplicate claim row."""

        item = {
            "source_kind": "model",
            "claim_bearing": False,
            "inventory_role": "source_semantic_declaration",
            "lean_declarations": ["Fixture.sourceAlgorithm"],
            "statement": "Algorithm 4.1 initializes the matching and repeats the stated proposal step.",
        }
        self.assertFalse(source_item_is_named_theoretical_statement(item))
        self.assertEqual(source_item_scope_classification_errors(item), [])
        self.assertEqual(
            filter_source_inventory_for_coverage(
                {"algorithm": item}, NAMED_THEORETICAL_STATEMENTS
            ),
            {},
        )

        disguised_result = {
            **item,
            "source_kind": "theorem",
            "statement": "Theorem 4. Every feasible input has the asserted property.",
        }
        self.assertTrue(source_item_is_named_theoretical_statement(disguised_result))
        self.assertTrue(
            any(
                "cannot set claim_bearing: false" in error
                for error in source_item_scope_classification_errors(disguised_result)
            )
        )

    def test_standalone_formula_is_not_promoted_by_a_support_theorem_anchor(
        self,
    ) -> None:
        """A theorem proving a formula does not make the formula a theorem row."""

        theorem_anchor = (
            "Theorem 8. The displayed condition holds for Gaussian noise.\n"
            "Proof. Apply the preceding estimates."
        )
        for statement in (
            "Equation (C.2) is the conditional monotonicity formula.",
            "After factoring (C.8), the displayed bracket is positive exactly when the next expression is positive.",
        ):
            with self.subTest(statement=statement):
                item = {
                    "source_kind": "formula",
                    "statement": statement,
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 40,
                            "line_end": 41,
                            "quoted_text": theorem_anchor,
                            "quoted_text_sha256": hashlib.sha256(
                                theorem_anchor.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                }

                self.assertFalse(source_item_is_named_theoretical_statement(item))
                self.assertEqual(
                    filter_source_inventory_for_coverage(
                        {"formula": item}, NAMED_THEORETICAL_STATEMENTS
                    ),
                    {},
                )
                self.assertEqual(
                    set(
                        filter_source_inventory_for_coverage(
                            {"formula": item}, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
                        )
                    ),
                    {"formula"},
                )

    def test_dswg_proof_equations_04_through_33_are_deep_only(self) -> None:
        """The real DSWG proof derivation stays out of normal named theory."""

        payload = json.loads(
            (
                ROOT
                / "papers"
                / "DSWG24DiscretizationBias"
                / "audit"
                / "paper_statement_map.json"
            ).read_text(encoding="utf-8")
        )
        items = payload["items"]
        equation_keys = {f"proof_equation_{number:02d}" for number in range(4, 34)}
        self.assertTrue(equation_keys <= set(items))
        self.assertEqual(source_map_structural_errors(items), [])

        normal = filter_source_map_items_for_coverage(
            items, NAMED_THEORETICAL_STATEMENTS
        )
        deep = filter_source_map_items_for_coverage(
            items, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        )
        self.assertTrue(equation_keys.isdisjoint(normal))
        self.assertTrue(equation_keys <= set(deep))

    def test_deep_mode_selects_full_inventory(self) -> None:
        items = {
            "theorem": {"source_kind": "theorem", "statement": "Theorem 1."},
            "caption": {"source_kind": "figure_caption", "statement": "Figure 1."},
            "remark": {"source_kind": "remark", "statement": "Remark 1."},
            "nonclaim": {"claim_bearing": False, "statement": "Metadata."},
        }

        selected = filter_source_map_items_for_coverage(
            items, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        )

        self.assertEqual(set(selected), set(items))

    def test_declared_custom_tex_result_requires_matching_pinned_opening(self) -> None:
        """Receipt aliases admit a real custom result, never ordinary prose."""

        custom_opening = "\\begin{customresult}\\label{custom:main}"
        payload = {
            "source_named_result_inventory_review": {
                "environment_kinds": {"customresult": "claim"}
            },
            "items": {
                "opaque_navigation_key": {
                    "source_kind": "claim",
                    "statement": "Every admissible input has a witness.",
                    "source_anchor_evidence": [
                        {
                            "path": "source.tex",
                            "line_start": 1,
                            "line_end": 1,
                            "quoted_text": custom_opening,
                            "quoted_text_sha256": hashlib.sha256(
                                custom_opening.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                },
                "misleading_route_name": {
                    "source_kind": "claim",
                    "statement": "Every admissible input has a witness.",
                    "source_anchor_evidence": [
                        {
                            "path": "source.tex",
                            "line_start": 2,
                            "line_end": 2,
                            "quoted_text": "The source says an endpoint holds.",
                            "quoted_text_sha256": hashlib.sha256(
                                b"The source says an endpoint holds."
                            ).hexdigest(),
                        }
                    ],
                    "lean_declarations": ["Fixture.CustomResult"],
                },
                "wrong_source_kind": {
                    "source_kind": "runtime_claim",
                    "statement": "Every admissible input has a witness.",
                    "source_anchor_evidence": [
                        {
                            "path": "source.tex",
                            "line_start": 3,
                            "line_end": 3,
                            "quoted_text": custom_opening,
                            "quoted_text_sha256": hashlib.sha256(
                                custom_opening.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                },
                "bad_anchor_digest": {
                    "source_kind": "claim",
                    "statement": "Every admissible input has a witness.",
                    "source_anchor_evidence": [
                        {
                            "path": "source.tex",
                            "line_start": 4,
                            "line_end": 4,
                            "quoted_text": custom_opening,
                            "quoted_text_sha256": "0" * 64,
                        }
                    ],
                },
            },
        }

        selected = filter_source_map_items_for_coverage(
            payload["items"],
            NAMED_THEORETICAL_STATEMENTS,
            declared_environment_kinds=source_named_result_environment_kinds_from_map(
                payload
            ),
        )

        self.assertEqual(set(selected), {"opaque_navigation_key"})

    def test_visibly_named_model_conditions_are_normal_scope_without_name_routes(
        self,
    ) -> None:
        inventory = {
            "misleading_caption_key": {
                "source_kind": "model",
                "statement": "Model 1. Agents have finite action sets.",
                "lean_declarations": ["Fixture.captionOnly"],
            },
            "theorem_named_but_unlabelled_model": {
                "source_kind": "model",
                "statement": "The model has finite action sets.",
                "lean_declarations": ["Fixture.MainTheorem"],
            },
            "condition": {
                "source_kind": "condition",
                "statement": "Condition A. The parameter is positive.",
            },
        }

        selected = filter_source_inventory_for_coverage(
            inventory, NAMED_THEORETICAL_STATEMENTS
        )

        self.assertEqual(set(selected), {"misleading_caption_key", "condition"})

    def test_source_record_selector_uses_explicit_routes_from_selected_source_items(
        self,
    ) -> None:
        with self.subTest("ordinary named-theory scope"):
            from tempfile import TemporaryDirectory

            with TemporaryDirectory() as temp_dir:
                paper_dir = Path(temp_dir)
                audit_dir = paper_dir / "audit"
                audit_dir.mkdir()
                (audit_dir / "paper_statement_map.json").write_text(
                    json.dumps(
                        {
                            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                            "items": {
                                # Neither map key nor declaration spelling is
                                # relied on to determine source scope.
                                "caption_named_navigation_key": {
                                    "source_kind": "theorem",
                                    "statement": "Theorem 1. Every input has a witness.",
                                    "semantic_contract": {
                                        "spec_declaration": "Fixture.EndpointSpec",
                                        "evidence_declaration": "Fixture.EndpointProof",
                                    },
                                },
                                "theorem_named_navigation_key": {
                                    "source_kind": "example",
                                    "semantic_contract": {
                                        "spec_declaration": "Fixture.CaptionSpec",
                                        "evidence_declaration": "Fixture.CaptionProof",
                                    },
                                },
                            },
                        }
                    ),
                    encoding="utf-8",
                )

                selected_rows, selected_map, selection = (
                    SOURCE_RECORD_AUDIT.source_coverage_review_rows(
                        paper_dir,
                        ["endpoint_spec", "endpoint_proof", "caption_proof"],
                        {
                            "endpoint_spec": "Fixture.EndpointSpec",
                            "endpoint_proof": "Fixture.EndpointProof",
                            "caption_proof": "Fixture.CaptionProof",
                        },
                    )
                )

        self.assertEqual(selected_rows, ["endpoint_spec", "endpoint_proof"])
        self.assertEqual(
            set(selected_map["items"]), {"caption_named_navigation_key"}
        )
        self.assertEqual(
            selection["source_coverage_selected_source_items"],
            ["caption_named_navigation_key"],
        )
        self.assertEqual(
            selection["out_of_mode_review_surface_rows"], ["caption_proof"]
        )

    def test_source_record_selector_retains_explicit_corrected_target(self) -> None:
        """A corrected obligation cannot disappear behind archival heading syntax."""

        from tempfile import TemporaryDirectory

        corrected_item = {
            "source_kind": "theorem",
            # Deliberately no visible theorem heading: the correction itself is
            # the independent source-facing obligation.
            "statement": "The archival lower-bound endpoint is repaired.",
            "coverage_status": "corrected_source_statement",
            "corrected_target": {
                "schema": 1,
                "statement": "Every admissible instance satisfies the repaired lower bound.",
                "approval": {
                    "kind": "explicit_user_instruction",
                    "reference": "fixture corrected-target approval",
                },
            },
            "lean_declarations": ["Fixture.CorrectedProof"],
        }
        self.assertEqual(
            filter_source_map_items_for_coverage(
                {"opaque_corrected_navigation": corrected_item},
                NAMED_THEORETICAL_STATEMENTS,
            ),
            {},
        )

        with TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir()
            (audit_dir / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "items": {
                            "opaque_corrected_navigation": corrected_item,
                        },
                    }
                ),
                encoding="utf-8",
            )

            selected_rows, selected_map, selection = (
                SOURCE_RECORD_AUDIT.source_coverage_review_rows(
                    paper_dir,
                    ["corrected_proof"],
                    {"corrected_proof": "Fixture.CorrectedProof"},
                )
            )

        self.assertEqual(selected_rows, ["corrected_proof"])
        self.assertEqual(
            set(selected_map["items"]), {"opaque_corrected_navigation"}
        )
        self.assertEqual(
            selection["source_coverage_selected_source_items"],
            ["opaque_corrected_navigation"],
        )
        self.assertEqual(selection["source_coverage_route_errors"], [])

    def test_source_record_selector_does_not_route_approved_exclusion(self) -> None:
        """An approved non-proof scope decision remains visible, not unrouted."""

        from tempfile import TemporaryDirectory

        ordinary_item = {
            "source_kind": "theorem",
            "statement": "Theorem 1. Every admissible input has a witness.",
            "lean_declarations": ["Fixture.NamedProof"],
        }
        excluded_item = {
            "source_kind": "theorem",
            "claim_bearing": True,
            "statement": "Theorem 2. A computational claim is outside this proof campaign.",
            "user_approved_scope_exclusion": {
                "schema": 1,
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "fixture scope decision",
                "approved_at": "2026-08-14",
                "reason": "The separately catalogued computational item is not a proof target.",
                "source_locator": "source.txt:2",
                "source_evidence": "The source item remains explicitly visible.",
                "source_anchor_quote_sha256": "a" * 64,
            },
        }
        with TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir()
            (audit_dir / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "items": {
                            "ordinary_navigation": ordinary_item,
                            "excluded_navigation": excluded_item,
                        },
                    }
                ),
                encoding="utf-8",
            )
            selected_rows, selected_map, selection = (
                SOURCE_RECORD_AUDIT.source_coverage_review_rows(
                    paper_dir,
                    ["named_proof"],
                    {"named_proof": "Fixture.NamedProof"},
                )
            )

        self.assertEqual(selected_rows, ["named_proof"])
        self.assertEqual(set(selected_map["items"]), {"ordinary_navigation"})
        self.assertEqual(selection["source_coverage_unrouted_source_items"], [])
        self.assertEqual(selection["source_coverage_route_errors"], [])

    def test_proof_obligations_preserve_but_do_not_select_excluded_correction(self) -> None:
        """Keeping a clarification's provenance must not claim its deferred proof."""

        item = {
            "source_kind": "theorem",
            "statement": "Theorem 2. Every input has a witness.",
            "source_status": "corrected_source_statement",
            "coverage_status": "user_approved_scope_exclusion",
            "source_defect_ids": ["fixture-clarification"],
            "corrected_target": {
                "schema": 1,
                "statement": "Every admissible input has a witness.",
                "approval": {
                    "kind": "explicit_user_instruction",
                    "reference": "fixture corrected-target approval",
                },
            },
            "user_approved_scope_exclusion": {
                "schema": 1,
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "fixture deferred-proof decision",
            },
        }
        before = json.dumps(item, sort_keys=True)
        # Independent source-index discovery cannot restore proof credit to
        # this inventory item. Dedicated validators check its approval pins.
        selected = coverage_scope.filter_source_map_items_for_proof_obligations(
            {"deferred": item},
            NAMED_THEORETICAL_STATEMENTS,
            additional_selected_item_ids={"deferred"},
        )
        self.assertEqual(selected, {})
        self.assertEqual(json.dumps(item, sort_keys=True), before)

        # Removing only the scope decision restores the corrected obligation.
        active_item = dict(item)
        active_item.pop("user_approved_scope_exclusion")
        selected = coverage_scope.filter_source_map_items_for_proof_obligations(
            {"active": active_item}, NAMED_THEORETICAL_STATEMENTS
        )
        self.assertEqual(selected, {"active": active_item})

    def test_source_record_selector_adds_byte_pinned_index_match(self) -> None:
        """A broad anchor may select one indexed theorem without map-name hints."""

        from tempfile import TemporaryDirectory

        source_text = (
            "Results follow.\n"
            "Theorem 1. Every admissible input has a witness.\n"
            "This completes the statement.\n"
        )
        source_quote = source_text.rstrip("\n")
        indexed_item = {
            "source_kind": "theorem",
            "statement": "Every admissible input has a witness.",
            # The broad anchor does not syntactically open with `Theorem`, so
            # the legacy item predicate omits it. The source index independently
            # finds exactly one named presentation inside these current bytes.
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 3,
                    "quoted_text": source_quote,
                    "quoted_text_sha256": hashlib.sha256(
                        source_quote.encode("utf-8")
                    ).hexdigest(),
                }
            ],
            "lean_declarations": ["Fixture.IndexedProof"],
        }
        self.assertEqual(
            filter_source_map_items_for_coverage(
                {"opaque_index_navigation": indexed_item},
                NAMED_THEORETICAL_STATEMENTS,
            ),
            {},
        )

        with TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir()
            (paper_dir / "source.txt").write_text(source_text, encoding="utf-8")
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source_text.encode("utf-8")
                ).hexdigest(),
                "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                "items": {"opaque_index_navigation": indexed_item},
            }
            (audit_dir / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )

            selected_rows, selected_map, selection = (
                SOURCE_RECORD_AUDIT.source_coverage_review_rows(
                    paper_dir,
                    ["indexed_proof"],
                    {"indexed_proof": "Fixture.IndexedProof"},
                )
            )

        self.assertEqual(selected_rows, ["indexed_proof"])
        self.assertEqual(set(selected_map["items"]), {"opaque_index_navigation"})
        self.assertEqual(
            selection["source_coverage_selected_source_items"],
            ["opaque_index_navigation"],
        )
        self.assertEqual(selection["source_coverage_route_errors"], [])

    def test_source_record_selector_propagates_missing_prose_definition_ledger(
        self,
    ) -> None:
        from tempfile import TemporaryDirectory

        source_text = "Theorem 1. Every admissible input has a witness.\n"
        source_quote = source_text.rstrip("\n")
        source_digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
        payload = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_digest,
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "fixture source-only inventory reviewer",
                "validated_at": "2026-08-02T12:00:00Z",
                "method": "Independent extraction from the exact source bytes.",
                "source_artifact_sha256": source_digest,
                "discovered_named_result_sha256": "0" * 64,
            },
            "items": {
                "opaque_navigation": {
                    "source_kind": "theorem",
                    "statement": "Theorem 1. Every admissible input has a witness.",
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 1,
                            "line_end": 1,
                            "quoted_text": source_quote,
                            "quoted_text_sha256": hashlib.sha256(
                                source_quote.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                    "lean_declarations": ["Fixture.IndexedProof"],
                }
            },
        }

        with TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir()
            (paper_dir / "source.txt").write_text(source_text, encoding="utf-8")
            (audit_dir / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            _rows, _selected_map, selection = (
                SOURCE_RECORD_AUDIT.source_coverage_review_rows(
                    paper_dir,
                    ["indexed_proof"],
                    {"indexed_proof": "Fixture.IndexedProof"},
                )
            )

        self.assertTrue(
            any(
                "prose_definition_presentations must be an explicit" in error
                for error in selection["source_coverage_route_errors"]
            ),
            selection["source_coverage_route_errors"],
        )

    def test_deep_mode_requires_current_source_pinned_attestation(self) -> None:
        payload = {
            "source_coverage_mode": DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
            "source_artifact_sha256": SOURCE_DIGEST,
        }
        self.assertIn(
            "source_prose_inventory_review",
            deep_source_coverage_attestation_error(
                payload, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
            ),
        )

        payload["source_prose_inventory_review"] = {
            "complete": True,
            "validator": "reviewer",
            "validated_at": "2026-07-26T00:00:00Z",
            "method": "screened source PDF and transcript",
            "source_artifact_sha256": SOURCE_DIGEST,
        }
        self.assertEqual(
            deep_source_coverage_attestation_error(
                payload, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
            ),
            "",
        )

        payload["source_artifact_sha256"] = "b" * 64
        self.assertIn(
            "pin the current source_artifact_sha256",
            deep_source_coverage_attestation_error(
                payload, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
            ),
        )

    def test_invalid_explicit_mode_fails_closed_to_normal_scope(self) -> None:
        mode, error = source_coverage_mode_from_map(
            {"source_coverage_mode": "everything_without_attestation"}
        )

        self.assertEqual(mode, NAMED_THEORETICAL_STATEMENTS)
        self.assertIn("must be one of", error)

    def test_deep_coverage_can_supply_normal_subset_but_not_the_reverse(self) -> None:
        self.assertTrue(
            source_coverage_modes_compatible(
                DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
                NAMED_THEORETICAL_STATEMENTS,
            )
        )
        self.assertFalse(
            source_coverage_modes_compatible(
                NAMED_THEORETICAL_STATEMENTS,
                DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
            )
        )

    def test_named_heading_cannot_be_hidden_under_a_deep_only_source_kind(self) -> None:
        disguised_result = {
            "source_kind": "example",
            "claim_bearing": False,
            "statement": "Theorem 4. Every instance has the asserted property.",
        }

        selected = filter_source_inventory_for_coverage(
            {"misleading_navigation_key": disguised_result},
            NAMED_THEORETICAL_STATEMENTS,
        )

        self.assertEqual(set(selected), {"misleading_navigation_key"})
        errors = source_item_scope_classification_errors(disguised_result)
        self.assertTrue(
            any("conflicts with a named theoretical" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("cannot set claim_bearing: false" in error for error in errors),
            errors,
        )

    def test_unknown_source_kind_fails_closed_in_cheap_precheck(self) -> None:
        from tempfile import TemporaryDirectory

        with TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / "UnknownKindPaper"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            (audit_dir / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "items": {
                            "opaque_navigation_key": {
                                "source_kind": "unrecognized_source_category",
                                "claim_bearing": True,
                                "statement": "An opaque source assertion.",
                                "source_url": "https://example.test/paper",
                                "source_location": "p. 9",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            summary = review_dashboard.source_inventory_precheck_summary(paper_dir)

        self.assertTrue(summary["needs_attention"])
        errors = summary["source_presentation_classification_errors"]
        self.assertEqual(len(errors), 1)
        self.assertIn(
            "unknown source_kind `unrecognized_source_category`", errors[0]
        )

    def test_new_statement_first_map_explicitly_declares_normal_coverage_scope(
        self,
    ) -> None:
        target = new_paper.StatementTarget(
            source_item="Theorem 1",
            source_location="p. 1",
            source_statement="The source theorem.",
            lean_name="theorem1",
            lean_type="True",
            source_kind="theorem",
        )
        spec = new_paper.StatementSpec(
            targets=[target],
            source_artifact_path=Path("source.txt"),
            source_artifact_sha256=SOURCE_DIGEST,
            source_version="v1",
        )
        payload = json.loads(
            new_paper.paper_statement_map_text(
                SimpleNamespace(
                    official_url="https://example.test/paper",
                    url="https://example.test/paper.pdf",
                ),
                "EX00Example",
                spec,
                "papers/EX00Example/source.txt",
            )
        )

        self.assertEqual(
            payload["source_coverage_mode"], NAMED_THEORETICAL_STATEMENTS
        )

    def test_item_digest_is_semantic_and_ignores_navigation_aliases(self) -> None:
        item = {
            "title": "Theorem 2",
            "statement": "Every x has the asserted property.",
            "source_kind": "theorem",
            "source_location": "p. 4",
            "source_url": "https://example.test/first-edition",
            "source_text_file": "source.txt",
            "start_line": 40,
            "end_line": 43,
            "source_item": "Theorem 2",
            "source_artifact_sha256": SOURCE_DIGEST,
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 40,
                    "line_end": 43,
                    "quoted_text": "Theorem 2. Every x has the asserted property.",
                    "quoted_text_sha256": "b" * 64,
                }
            ],
            "aliases": ["old_navigation_label"],
            "lean_declarations": ["Fixture.old_statement_route"],
            "proof_lean_declarations": ["Fixture.old_proof_route"],
            "support_lean_declarations": ["Fixture.old_support_route"],
            "spec_lean_declarations": ["Fixture.old_spec_route"],
            "semantic_contract": {
                "spec_declaration": "Fixture.old_spec_route",
                "evidence_declaration": "Fixture.old_proof_route",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        renamed_navigation = deepcopy(item)
        renamed_navigation["aliases"] = ["new_navigation_label", "another_alias"]
        renamed_navigation["lean_declarations"] = ["Fixture.new_statement_route"]
        renamed_navigation["proof_lean_declarations"] = ["Fixture.new_proof_route"]
        renamed_navigation["support_lean_declarations"] = ["Fixture.new_support_route"]
        renamed_navigation["spec_lean_declarations"] = ["Fixture.new_spec_route"]
        renamed_navigation["semantic_contract"] = {
            "spec_declaration": "Fixture.new_spec_route",
            "evidence_declaration": "Fixture.new_proof_route",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        null_presentation_alias = deepcopy(item)
        null_presentation_alias["source_presentation_alias"] = None
        actual_presentation_alias = deepcopy(item)
        actual_presentation_alias["source_presentation_alias"] = {
            "schema": 1,
            "canonical_source_item": "canonical-navigation",
            "relation": "same_visible_label",
        }
        changed_statement = deepcopy(item)
        changed_statement["statement"] = "Every x has a different property."
        changed_evidence_mode = deepcopy(item)
        changed_evidence_mode["semantic_contract"]["evidence_mode"] = "refutes"
        changed_corrected_target = deepcopy(item)
        changed_corrected_target["corrected_target"] = {
            "statement": "Every x has the repaired property."
        }
        changed_administrative_status = deepcopy(item)
        changed_administrative_status["source_status"] = (
            "repository bookkeeping label only"
        )
        changed_defect_cross_references = deepcopy(item)
        changed_defect_cross_references["source_defect_ids"] = [
            "FIXTURE-PROOF-ROUTE-01"
        ]
        changed_source_note = deepcopy(item)
        changed_source_note["source_note"] = (
            "A source-model convention with mathematical content."
        )
        changed_formalization_boundary = deepcopy(item)
        changed_formalization_boundary["formalization_boundary"] = {
            "scope": "a narrower result"
        }
        relocated_anchor = deepcopy(item)
        relocated_anchor.update(
            {
                "source_location": "revised_source.txt:71-74",
                "source_url": "https://example.test/revised-edition",
                "source_text_file": "revised_source.txt",
                "start_line": 71,
                "end_line": 74,
                "source_item": "Theorem 9",
            }
        )
        relocated_anchor["source_anchor_evidence"] = [
            {
                **item["source_anchor_evidence"][0],
                "path": "revised_source.txt",
                "line_start": 71,
                "line_end": 74,
            }
        ]
        changed_quote = deepcopy(relocated_anchor)
        changed_quote["source_anchor_evidence"][0]["quoted_text"] = (
            "Theorem 9. Every x has a different asserted property."
        )

        original_digest = source_item_coverage_sha256(
            item, NAMED_THEORETICAL_STATEMENTS
        )
        self.assertEqual(
            source_item_coverage_sha256(
                renamed_navigation, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertEqual(
            source_item_coverage_sha256(
                null_presentation_alias, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                actual_presentation_alias, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                changed_statement, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                changed_evidence_mode, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                changed_corrected_target, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertEqual(
            source_item_coverage_sha256(
                changed_administrative_status, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertEqual(
            source_item_coverage_sha256(
                changed_defect_cross_references, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                changed_source_note, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                changed_formalization_boundary, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertEqual(
            source_item_coverage_sha256(
                relocated_anchor, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                changed_quote, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertEqual(
            source_item_coverage_sha256(
                item, DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
            ),
            original_digest,
        )

    def test_item_digest_uses_corrected_target_authority_projection(self) -> None:
        item = {
            "source_kind": "theorem",
            "statement": "The archival statement has a documented defect.",
            "claim_bearing": True,
            "corrected_target": self.approved_corrected_target(),
        }
        original_digest = source_item_coverage_sha256(
            item, NAMED_THEORETICAL_STATEMENTS
        )

        moved = deepcopy(item)
        moved["corrected_target"]["approval"]["artifact_path"] = (  # type: ignore[index]
            "audit/SOURCE_TARGET_STATEMENTS.md"
        )
        self.assertEqual(
            source_item_coverage_sha256(moved, NAMED_THEORETICAL_STATEMENTS),
            original_digest,
        )

        # Locator-neutral identity does not waive the independent current-file
        # check: the exact excerpt must still occur once at the resolved path.
        approval = moved["corrected_target"]["approval"]  # type: ignore[index]
        excerpt = approval["artifact_excerpt"]  # type: ignore[index]
        self.assertEqual(
            corrected_target_approval_artifact_error(
                approval, f"Header\n\n{excerpt}\n\nFooter"
            ),
            "",
        )
        self.assertIn(
            "found 0",
            corrected_target_approval_artifact_error(
                approval, "This artifact does not contain the approved excerpt."
            ),
        )

        mutations: dict[str, dict[str, object]] = {}
        changed_statement = deepcopy(item)
        changed_statement["corrected_target"]["statement"] = (  # type: ignore[index]
            "For every x, a different corrected conclusion holds."
        )
        mutations["corrected statement"] = changed_statement

        changed_excerpt = deepcopy(item)
        replacement_excerpt = (
            "The task owner approved a different corrected mathematical target "
            "for the formalization."
        )
        changed_excerpt["corrected_target"]["approval"][  # type: ignore[index]
            "artifact_excerpt"
        ] = replacement_excerpt
        changed_excerpt["corrected_target"]["approval"][  # type: ignore[index]
            "artifact_excerpt_sha256"
        ] = hashlib.sha256(replacement_excerpt.encode("utf-8")).hexdigest()
        mutations["approval excerpt"] = changed_excerpt

        unknown_approval_field = deepcopy(item)
        unknown_approval_field["corrected_target"]["approval"][  # type: ignore[index]
            "future_semantic_condition"
        ] = "new condition"
        mutations["unknown approval field"] = unknown_approval_field

        lookalike_locator = deepcopy(item)
        lookalike_locator["corrected_target"]["approval"][  # type: ignore[index]
            "Artifact_Path"
        ] = "audit/first.md"
        changed_lookalike_locator = deepcopy(lookalike_locator)
        changed_lookalike_locator["corrected_target"]["approval"][  # type: ignore[index]
            "Artifact_Path"
        ] = "audit/second.md"
        self.assertNotEqual(
            source_item_coverage_sha256(
                lookalike_locator, NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                changed_lookalike_locator, NAMED_THEORETICAL_STATEMENTS
            ),
        )

        legacy_protocol = deepcopy(item)
        legacy_protocol["corrected_target"]["approval"][  # type: ignore[index]
            "artifact_protocol"
        ] = "whole_artifact_sha256_v0"
        moved_legacy_protocol = deepcopy(legacy_protocol)
        moved_legacy_protocol["corrected_target"]["approval"][  # type: ignore[index]
            "artifact_path"
        ] = "audit/SOURCE_TARGET_STATEMENTS.md"
        self.assertNotEqual(
            source_item_coverage_sha256(
                legacy_protocol, NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                moved_legacy_protocol, NAMED_THEORETICAL_STATEMENTS
            ),
        )

        unrelated_locator = deepcopy(item)
        unrelated_locator["review_material"] = {
            "artifact_path": "audit/first.md"
        }
        moved_unrelated_locator = deepcopy(unrelated_locator)
        moved_unrelated_locator["review_material"]["artifact_path"] = (  # type: ignore[index]
            "audit/second.md"
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                unrelated_locator, NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                moved_unrelated_locator, NAMED_THEORETICAL_STATEMENTS
            ),
        )

        for label, changed in mutations.items():
            with self.subTest(change=label):
                self.assertNotEqual(
                    source_item_coverage_sha256(
                        changed, NAMED_THEORETICAL_STATEMENTS
                    ),
                    original_digest,
                )

    def test_corrected_target_legacy_item_digests_replay_literal_old_shape(
        self,
    ) -> None:
        item = {
            "source_item_key": "fixture-key",
            "source_kind": "theorem",
            "statement": "The archival statement has a documented defect.",
            "claim_bearing": True,
            "source_status": "support_only",
            "source_defect_ids": ["FIXTURE-DEFECT-1"],
            "corrected_target": self.approved_corrected_target(),
        }
        self.assertEqual(
            legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion(
                item, NAMED_THEORETICAL_STATEMENTS
            ),
            "aaa587a6f2b73a794baf255f6f2d51cfcdcdaa67f067864d52513ed1759e23a1",
        )
        self.assertEqual(
            legacy_source_item_coverage_sha256_before_navigation_key_exclusion(
                item, NAMED_THEORETICAL_STATEMENTS
            ),
            "eceb75d2bf29b76fbba6d39a5e5acf6a92c51f01c398e7d0ac61ef4a29d40909",
        )
        self.assertEqual(
            legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                item, NAMED_THEORETICAL_STATEMENTS
            ),
            "35756aafbdfba52161b67a518748dcb4a9304dc9cb9dd748ada50254a94b99c5",
        )
        self.assertEqual(
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                item, NAMED_THEORETICAL_STATEMENTS
            ),
            "71abd998c97289627a68797dabb976f213d4169ceaebbfb0b6831e7ac3cc7654",
        )

    def test_original_locator_replays_old_schema4_and_schema5_item_preimages(
        self,
    ) -> None:
        old = {
            "source_item_key": "fixture-key",
            "source_kind": "theorem",
            "statement": "The archival statement has a documented defect.",
            "claim_bearing": True,
            "source_status": "support_only",
            "source_defect_ids": ["FIXTURE-DEFECT-1"],
            "corrected_target": self.approved_corrected_target(
                "docs/SOURCE_CLARIFICATIONS.md"
            ),
        }
        current = deepcopy(old)
        approval = current["corrected_target"]["approval"]  # type: ignore[index]
        approval["artifact_path"] = "audit/SOURCE_TARGET_STATEMENTS.md"  # type: ignore[index]
        approval[CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD] = (  # type: ignore[index]
            "docs/SOURCE_CLARIFICATIONS.md"
        )
        self.assertEqual(
            source_item_coverage_sha256(current, NAMED_THEORETICAL_STATEMENTS),
            source_item_coverage_sha256(old, NAMED_THEORETICAL_STATEMENTS),
        )
        historical_readers = (
            legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion,
            legacy_source_item_coverage_sha256_before_navigation_key_exclusion,
            legacy_source_item_coverage_sha256_before_direct_source_status_exclusion,
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
        )
        for reader in historical_readers:
            with self.subTest(reader=reader.__name__):
                old_digest = reader(old, NAMED_THEORETICAL_STATEMENTS)
                self.assertEqual(
                    reader(current, NAMED_THEORETICAL_STATEMENTS), old_digest
                )

                forged = deepcopy(current)
                forged["corrected_target"]["approval"][  # type: ignore[index]
                    CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
                ] = "docs/FORGED.md"
                self.assertNotEqual(
                    reader(forged, NAMED_THEORETICAL_STATEMENTS), old_digest
                )

                malformed = deepcopy(current)
                malformed["corrected_target"]["approval"][  # type: ignore[index]
                    CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
                ] = "../docs/SOURCE_CLARIFICATIONS.md"
                self.assertEqual(
                    reader(malformed, NAMED_THEORETICAL_STATEMENTS), ""
                )

        self.assertTrue(
            source_item_coverage_receipt_matches(
                current,
                NAMED_THEORETICAL_STATEMENTS,
                digest_schema=PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
                digest=legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion(
                    old, NAMED_THEORETICAL_STATEMENTS
                ),
            )
        )
        malformed = deepcopy(current)
        malformed["corrected_target"]["approval"][  # type: ignore[index]
            CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
        ] = "../docs/SOURCE_CLARIFICATIONS.md"
        self.assertFalse(
            source_item_coverage_receipt_matches(
                malformed,
                NAMED_THEORETICAL_STATEMENTS,
                digest_schema=PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
                digest=legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion(
                    old, NAMED_THEORETICAL_STATEMENTS
                ),
            )
        )

    def test_item_digest_separates_source_kind_review_receipts_from_semantics(
        self,
    ) -> None:
        item = {
            "statement": "Definition 2 identifies the source fairness relation.",
            "source_kind": "definition",
            "claim_bearing": True,
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 12,
                    "line_end": 14,
                    "quoted_text": "Definition 2. The source fairness relation holds.",
                    "quoted_text_sha256": "c" * 64,
                }
            ],
        }
        original_digest = source_item_coverage_sha256(
            item, NAMED_THEORETICAL_STATEMENTS
        )

        reviewed = deepcopy(item)
        reviewed.update(
            {
                "source_kind_validator": "independent source-kind validator",
                "source_kind_validated_at": "2026-08-01T05:45:00Z",
                "source_kind_human_approved": True,
                "source_kind_human_reviewer": "independent human reviewer",
                "source_kind_human_reviewed_at": "2026-08-01",
            }
        )
        refreshed = deepcopy(reviewed)
        refreshed.update(
            {
                "source_kind_validator": "replacement source-kind validator",
                "source_kind_validated_at": "2026-08-02T06:30:00Z",
                "source_kind_human_reviewer": "replacement human reviewer",
                "source_kind_human_reviewed_at": "2026-08-02",
            }
        )
        self.assertEqual(
            source_item_coverage_sha256(
                reviewed, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )
        self.assertEqual(
            source_item_coverage_sha256(
                refreshed, NAMED_THEORETICAL_STATEMENTS
            ),
            original_digest,
        )

        substantive_changes = {
            "source kind": {**reviewed, "source_kind": "theorem"},
            "statement": {
                **reviewed,
                "statement": "Definition 2 identifies a different fairness relation.",
            },
            "claim-bearing status": {**reviewed, "claim_bearing": False},
            "corrected target": {
                **reviewed,
                "corrected_target": {
                    "corrected_statement": "Definition 2 uses the corrected relation."
                },
            },
        }
        for label, changed in substantive_changes.items():
            with self.subTest(change=label):
                self.assertNotEqual(
                    source_item_coverage_sha256(
                        changed, NAMED_THEORETICAL_STATEMENTS
                    ),
                    original_digest,
                )

    def test_item_digest_excludes_normalized_map_key_with_exact_legacy_replay(
        self,
    ) -> None:
        item = {
            "source_item_key": "old-navigation-key",
            "source_kind": "theorem",
            "statement": "Every finite source object has a witness.",
            "claim_bearing": True,
        }
        renamed = {**item, "source_item_key": "new-navigation-key"}

        self.assertEqual(
            source_item_coverage_sha256(item, NAMED_THEORETICAL_STATEMENTS),
            source_item_coverage_sha256(renamed, NAMED_THEORETICAL_STATEMENTS),
        )
        self.assertNotEqual(
            legacy_source_item_coverage_sha256_before_navigation_key_exclusion(
                item, NAMED_THEORETICAL_STATEMENTS
            ),
            legacy_source_item_coverage_sha256_before_navigation_key_exclusion(
                renamed, NAMED_THEORETICAL_STATEMENTS
            ),
        )

    def test_defect_cross_reference_exclusion_is_schema_6_only(self) -> None:
        """Schema 5 remains exact while schema 6 delegates proof links."""

        item = {
            "source_kind": "theorem",
            "statement": "Every finite source object has a witness.",
            "source_defect_ids": [],
        }
        linked = {**item, "source_defect_ids": ["FIXTURE-PROOF-ROUTE-01"]}
        self.assertEqual(
            source_item_coverage_sha256(item, NAMED_THEORETICAL_STATEMENTS),
            source_item_coverage_sha256(linked, NAMED_THEORETICAL_STATEMENTS),
        )
        self.assertNotEqual(
            legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion(
                item, NAMED_THEORETICAL_STATEMENTS
            ),
            legacy_source_item_coverage_sha256_before_defect_cross_reference_exclusion(
                linked, NAMED_THEORETICAL_STATEMENTS
            ),
        )

    def test_corrected_target_spec_navigation_is_namespace_neutral(self) -> None:
        """A unique paper-owned Spec need not live in PaperInterface."""

        source_item = {
            "semantic_contract": {
                "spec_declaration": "FixturePaper.corrected_resultSpec",
                "evidence_declaration": "FixturePaper.corrected_result",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        }
        self.assertTrue(
            review_dashboard._corrected_target_contract_spec_navigation_matches(
                source_item,
                "FixturePaper.corrected_result",
                ["corrected_resultSpec"],
                {"source": source_item},
                "FixturePaper",
                semantic_contract_schema=2,
            )
        )
        other = {
            "semantic_contract": {
                "spec_declaration": "FixturePaper.Nested.corrected_resultSpec",
                "evidence_declaration": "FixturePaper.Nested.corrected_result",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        }
        self.assertFalse(
            review_dashboard._corrected_target_contract_spec_navigation_matches(
                source_item,
                "FixturePaper.corrected_result",
                ["corrected_resultSpec"],
                {"source": source_item, "other": other},
                "FixturePaper",
                semantic_contract_schema=2,
            )
        )

    def test_direct_status_projection_is_a_versioned_schema_transition(self) -> None:
        """Only the direct bookkeeping field changes across schema 4 -> 5."""

        item = {
            "source_kind": "theorem",
            "statement": "Every finite source object has a witness.",
            "source_status": "under_review",
            "source_model": {"source_status": "finite_carrier"},
        }
        direct_status_change = deepcopy(item)
        direct_status_change["source_status"] = "corrected"
        nested_status_change = deepcopy(item)
        nested_status_change["source_model"]["source_status"] = "continuous_carrier"

        current = source_item_coverage_sha256(item, NAMED_THEORETICAL_STATEMENTS)
        current_direct = source_item_coverage_sha256(
            direct_status_change, NAMED_THEORETICAL_STATEMENTS
        )
        current_nested = source_item_coverage_sha256(
            nested_status_change, NAMED_THEORETICAL_STATEMENTS
        )
        legacy = legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
            item, NAMED_THEORETICAL_STATEMENTS
        )
        legacy_direct = (
            legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                direct_status_change, NAMED_THEORETICAL_STATEMENTS
            )
        )
        legacy_nested = (
            legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                nested_status_change, NAMED_THEORETICAL_STATEMENTS
            )
        )
        legacy_excluded = (
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                item, NAMED_THEORETICAL_STATEMENTS
            )
        )
        legacy_excluded_direct = (
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                direct_status_change, NAMED_THEORETICAL_STATEMENTS
            )
        )
        legacy_excluded_nested = (
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                nested_status_change, NAMED_THEORETICAL_STATEMENTS
            )
        )

        self.assertEqual(SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA, 6)
        self.assertEqual(PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA, 5)
        self.assertEqual(LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA, 4)
        self.assertNotEqual(current, legacy)
        self.assertEqual(current, current_direct)
        self.assertNotEqual(current, current_nested)
        self.assertNotEqual(legacy, legacy_direct)
        self.assertNotEqual(legacy, legacy_nested)
        self.assertNotEqual(current, legacy_excluded)
        self.assertEqual(legacy_excluded, legacy_excluded_direct)
        self.assertNotEqual(legacy_excluded, legacy_excluded_nested)

    def test_raw_cache_map_receipt_excludes_only_direct_administrative_status(
        self,
    ) -> None:
        """Aggregate cache reuse keeps all source-model content fail-closed."""

        source_map = {
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "items": {
                "opaque_source_item": {
                    "source_kind": "theorem",
                    "statement": "Every admissible input has a witness.",
                    "source_status": "under_review",
                    "source_note": "The source uses the finite model.",
                    "lean_declarations": ["Fixture.PaperInterface.endpoint"],
                    "corrected_target": {
                        "statement": "Every finite admissible input has a witness.",
                        "approval_id": "FIXTURE-CORRECTION",
                    },
                    # A nested status can have source-model meaning.  The cache
                    # exception applies only to the direct item bookkeeping field.
                    "source_model": {"source_status": "finite_only"},
                }
            },
        }
        original = source_map_cache_semantic_sha256(source_map)
        original_item = source_item_coverage_sha256(
            source_map["items"]["opaque_source_item"],
            NAMED_THEORETICAL_STATEMENTS,
        )

        administrative = deepcopy(source_map)
        administrative["items"]["opaque_source_item"]["source_status"] = "resolved"
        self.assertEqual(source_map_cache_semantic_sha256(administrative), original)

        defect_cross_reference = deepcopy(source_map)
        defect_cross_reference["items"]["opaque_source_item"]["source_defect_ids"] = [
            "FIXTURE-PROOF-ROUTE-01"
        ]
        self.assertEqual(
            source_map_cache_semantic_sha256(defect_cross_reference), original
        )
        self.assertEqual(
            source_item_coverage_sha256(
                defect_cross_reference["items"]["opaque_source_item"],
                NAMED_THEORETICAL_STATEMENTS,
            ),
            original_item,
        )

        # Only the schema's exact field is administrative.  A misspelled or
        # whitespace/case-normalized lookalike is unknown source-map metadata
        # and must reopen the aggregate raw audit.
        for field in ("Source_Status", " source_status "):
            with self.subTest(field=field):
                lookalike = deepcopy(source_map)
                lookalike["items"]["opaque_source_item"][field] = "resolved"
                self.assertNotEqual(
                    source_map_cache_semantic_sha256(lookalike), original
                )
                self.assertNotEqual(
                    source_item_coverage_sha256(
                        lookalike["items"]["opaque_source_item"],
                        NAMED_THEORETICAL_STATEMENTS,
                    ),
                    original_item,
                )

        changed_route = deepcopy(source_map)
        changed_route["items"]["opaque_source_item"]["lean_declarations"] = [
            "Fixture.PaperInterface.repaired_endpoint"
        ]
        changed_note = deepcopy(source_map)
        changed_note["items"]["opaque_source_item"]["source_note"] = (
            "The source uses a different finite model."
        )
        changed_target = deepcopy(source_map)
        changed_target["items"]["opaque_source_item"]["corrected_target"][
            "statement"
        ] = "Every finite input has a repaired witness."
        changed_nested_status = deepcopy(source_map)
        changed_nested_status["items"]["opaque_source_item"]["source_model"][
            "source_status"
        ] = "unrestricted"
        omitted_coverage_mode = deepcopy(source_map)
        omitted_coverage_mode.pop("source_coverage_mode")
        explicit_mode, explicit_mode_error = source_coverage_mode_from_map(source_map)
        omitted_mode, omitted_mode_error = source_coverage_mode_from_map(
            omitted_coverage_mode
        )
        self.assertEqual(explicit_mode_error, "")
        self.assertEqual(omitted_mode_error, "")
        self.assertEqual(explicit_mode, DEFAULT_SOURCE_COVERAGE_MODE)
        self.assertEqual(omitted_mode, DEFAULT_SOURCE_COVERAGE_MODE)
        self.assertEqual(
            source_map_cache_semantic_projection(omitted_coverage_mode),
            source_map_cache_semantic_projection(source_map),
        )
        self.assertEqual(
            source_map_cache_semantic_sha256(omitted_coverage_mode), original
        )
        self.assertEqual(
            filter_source_map_items_for_coverage(source_map["items"], explicit_mode),
            filter_source_map_items_for_coverage(
                omitted_coverage_mode["items"], omitted_mode
            ),
        )
        noncanonical_default = deepcopy(source_map)
        noncanonical_default["source_coverage_mode"] = (
            f" {DEFAULT_SOURCE_COVERAGE_MODE} "
        )
        self.assertNotEqual(
            source_map_cache_semantic_sha256(noncanonical_default), original
        )
        for label, changed in (
            ("source route", changed_route),
            ("source note", changed_note),
            ("corrected target", changed_target),
            ("nested source status", changed_nested_status),
        ):
            with self.subTest(change=label):
                self.assertNotEqual(source_map_cache_semantic_sha256(changed), original)

    def test_closeout_scope_and_partition_do_not_rehash_unchanged_raw_items(self) -> None:
        source_map = {
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "items": {
                "claim": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "statement": "Every feasible input has a witness.",
                }
            },
            "source_named_result_inventory_review": {
                "source_region_partition": {
                    "schema": 1,
                    "source_item_regions": {"claim": "main"},
                }
            },
            "closeout_review_policy": {
                "schema": 1,
                "source_scope": "all_named_theory",
                "repeat_final_scope": "main_primary",
                "required_final_adversary_count": 1,
                "scheduling": {
                    "initial_semantic_review": [],
                    "final_adversarial_review": ["reviewer-a"],
                },
            },
        }
        original = source_map_cache_semantic_sha256(source_map)
        changed_controls = deepcopy(source_map)
        changed_controls["closeout_review_policy"][
            "required_final_adversary_count"
        ] = 2
        changed_controls["closeout_review_policy"]["scheduling"][
            "final_adversarial_review"
        ] = ["reviewer-b"]
        changed_controls["source_named_result_inventory_review"][
            "source_region_partition"
        ]["source_item_regions"] = {"claim": "renamed-main-region"}
        self.assertEqual(
            source_map_cache_semantic_sha256(changed_controls), original
        )

        changed_item = deepcopy(source_map)
        changed_item["items"]["claim"]["statement"] = (
            "Every feasible input has a unique witness."
        )
        self.assertNotEqual(source_map_cache_semantic_sha256(changed_item), original)

    def test_raw_source_record_identity_separates_valid_correspondence_lane(
        self,
    ) -> None:
        """Raw reuse ignores correspondence owned by the strict lane."""

        derived_fields = (
            "source_atoms_sha256",
            "spec_closure_sha256",
            "spec_surface_sha256",
            "closure_environment_sha256",
            "item_identity_sha256",
        )
        item: dict[str, object] = {
            "source_kind": "theorem",
            "statement": "Every admissible allocation has the stated witness.",
            "semantic_contract": {
                "spec_declaration": "Fixture.PaperInterface.endpointSpec",
                "evidence_declaration": "Fixture.PaperInterface.endpoint",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
            "source_claim_atoms": [
                {
                    "id": "endpoint.witness",
                    "semantic_claim": "Every admissible allocation has a witness.",
                    "reviewed_lean_route": "Fixture.PaperInterface.endpoint",
                }
            ],
            "source_spec_correspondence": {
                "schema": 1,
                "source_atoms_sha256": "a" * 64,
                "spec_closure_sha256": "b" * 64,
                "spec_surface_sha256": "c" * 64,
                "closure_environment_sha256": "d" * 64,
                "item_identity_sha256": "e" * 64,
                "source_atom_bindings": [
                    {
                        "source_atom_sha256": "f" * 64,
                        "spec_component_sha256s": ["1" * 64],
                        "semantic_bridge": "The Spec is the source endpoint.",
                    }
                ],
                "closure_node_dispositions": [
                    {
                        "closure_component_sha256": "2" * 64,
                        "source_atom_sha256": "f" * 64,
                        "semantic_basis": {
                            "semantic_statement": "The closure node proves the endpoint."
                        },
                    }
                ],
            },
        }

        def raw_identity(value: dict[str, object]) -> tuple[str, str, str]:
            return (
                source_record_source_item_record_sha256(value),
                source_record_source_item_semantic_sha256(value, ""),
                source_map_cache_semantic_sha256(
                    {"source_coverage_mode": NAMED_THEORETICAL_STATEMENTS, "items": {"row": value}}
                ),
            )

        original = raw_identity(item)
        projection = source_record_source_item_projection(item)
        self.assertIsInstance(projection, dict)
        self.assertNotIn("source_spec_correspondence", projection)

        valid_correspondence_changes: dict[str, dict[str, object]] = {}
        for field in derived_fields:
            changed = deepcopy(item)
            changed_correspondence = changed["source_spec_correspondence"]
            assert isinstance(changed_correspondence, dict)
            changed_correspondence[field] = "9" * 64
            valid_correspondence_changes[field] = changed

        changed_binding = deepcopy(item)
        binding_correspondence = changed_binding["source_spec_correspondence"]
        assert isinstance(binding_correspondence, dict)
        bindings = binding_correspondence["source_atom_bindings"]
        assert isinstance(bindings, list) and isinstance(bindings[0], dict)
        bindings[0]["semantic_bridge"] = "The Spec has a different source meaning."
        valid_correspondence_changes["source-atom binding"] = changed_binding

        changed_disposition = deepcopy(item)
        disposition_correspondence = changed_disposition[
            "source_spec_correspondence"
        ]
        assert isinstance(disposition_correspondence, dict)
        dispositions = disposition_correspondence["closure_node_dispositions"]
        assert isinstance(dispositions, list) and isinstance(dispositions[0], dict)
        basis = dispositions[0]["semantic_basis"]
        assert isinstance(basis, dict)
        basis["semantic_statement"] = "The closure node proves another endpoint."
        valid_correspondence_changes["closure disposition"] = changed_disposition

        for label, changed in valid_correspondence_changes.items():
            with self.subTest(strict_lane_change=label):
                self.assertEqual(raw_identity(changed), original)

        whole_root = deepcopy(item)
        whole_root_correspondence = whole_root["source_spec_correspondence"]
        assert isinstance(whole_root_correspondence, dict)
        whole_root_bindings = whole_root_correspondence["source_atom_bindings"]
        assert isinstance(whole_root_bindings, list) and isinstance(
            whole_root_bindings[0], dict
        )
        whole_root_bindings[0]["spec_component_sha256s"] = ["c" * 64]
        whole_root_identity = raw_identity(whole_root)
        supported_whole_root_identities = (
            source_record_source_item_supported_identity_sha256s(whole_root, "")
        )
        self.assertEqual(len(supported_whole_root_identities), 3)
        self.assertIn(whole_root_identity[:2], supported_whole_root_identities)
        refreshed_whole_root = deepcopy(whole_root)
        refreshed_correspondence = refreshed_whole_root[
            "source_spec_correspondence"
        ]
        assert isinstance(refreshed_correspondence, dict)
        refreshed_correspondence["spec_surface_sha256"] = "9" * 64
        refreshed_bindings = refreshed_correspondence["source_atom_bindings"]
        assert isinstance(refreshed_bindings, list) and isinstance(
            refreshed_bindings[0], dict
        )
        refreshed_bindings[0]["spec_component_sha256s"] = ["9" * 64]
        self.assertEqual(raw_identity(refreshed_whole_root), whole_root_identity)

        changed_selected_component = deepcopy(whole_root)
        selected_correspondence = changed_selected_component[
            "source_spec_correspondence"
        ]
        assert isinstance(selected_correspondence, dict)
        selected_bindings = selected_correspondence["source_atom_bindings"]
        assert isinstance(selected_bindings, list) and isinstance(
            selected_bindings[0], dict
        )
        selected_bindings[0]["spec_component_sha256s"] = ["8" * 64]
        self.assertEqual(raw_identity(changed_selected_component), whole_root_identity)
        self.assertEqual(
            len(
                source_record_source_item_supported_identity_sha256s(
                    changed_selected_component, ""
                )
            ),
            2,
        )

        substantive_changes: dict[str, dict[str, object]] = {}
        changed_contract = deepcopy(item)
        contract = changed_contract["semantic_contract"]
        assert isinstance(contract, dict)
        contract["evidence_mode"] = "refutes"
        substantive_changes["semantic contract"] = changed_contract

        changed_atoms = deepcopy(item)
        atoms = changed_atoms["source_claim_atoms"]
        assert isinstance(atoms, list) and isinstance(atoms[0], dict)
        atoms[0]["semantic_claim"] = "Every admissible allocation has a different witness."
        substantive_changes["source atom"] = changed_atoms

        changed_unknown = deepcopy(item)
        unknown_correspondence = changed_unknown["source_spec_correspondence"]
        assert isinstance(unknown_correspondence, dict)
        unknown_correspondence["future_semantic_field"] = {
            "premise": "A newly recorded semantic obligation."
        }
        substantive_changes["unknown correspondence field"] = changed_unknown

        changed_top_level_unknown = deepcopy(item)
        changed_top_level_unknown["future_source_semantic_field"] = "new premise"
        substantive_changes["unknown top-level field"] = changed_top_level_unknown

        lookalike_field = deepcopy(item)
        lookalike_field["Source_Spec_Correspondence"] = {
            field: "9" * 64 for field in derived_fields
        }
        substantive_changes["case-sensitive correspondence lookalike"] = lookalike_field

        nested_correspondence = deepcopy(item)
        nested_contract = nested_correspondence["semantic_contract"]
        assert isinstance(nested_contract, dict)
        nested_contract["source_spec_correspondence"] = {
            field: "9" * 64 for field in derived_fields
        }
        substantive_changes["nested correspondence lookalike"] = nested_correspondence

        for label, changed in substantive_changes.items():
            with self.subTest(change=label):
                changed_identity = raw_identity(changed)
                self.assertNotEqual(changed_identity[0], original[0])
                self.assertNotEqual(changed_identity[1], original[1])
                self.assertNotEqual(changed_identity[2], original[2])

    def test_raw_source_record_identity_fails_closed_for_malformed_correspondence(
        self,
    ) -> None:
        """Only a structurally valid correspondence permits lane separation."""

        item: dict[str, object] = {
            "source_kind": "theorem",
            "statement": "Every admissible allocation has the stated witness.",
            "source_spec_correspondence": {
                "schema": 1,
                "source_atoms_sha256": "a" * 64,
                "spec_closure_sha256": "b" * 64,
                "spec_surface_sha256": "c" * 64,
                "closure_environment_sha256": "d" * 64,
                "item_identity_sha256": "e" * 64,
                "source_atom_bindings": [],
                "closure_node_dispositions": [],
            },
        }

        def raw_identity(value: dict[str, object]) -> tuple[str, str, str]:
            return (
                source_record_source_item_record_sha256(value),
                source_record_source_item_semantic_sha256(value, ""),
                source_map_cache_semantic_sha256(
                    {"source_coverage_mode": NAMED_THEORETICAL_STATEMENTS, "items": {"row": value}}
                ),
            )

        original = raw_identity(item)
        initial_correspondence = item["source_spec_correspondence"]
        assert isinstance(initial_correspondence, dict)
        malformed_values: dict[str, object] = {
            "null": None,
            "string": "unparsed correspondence",
            "list": ["unparsed correspondence"],
            "invalid generated digest": {
                **initial_correspondence,
                "source_atoms_sha256": "not-a-sha256",
            },
            "missing correspondence schema": {
                key: value
                for key, value in initial_correspondence.items()
                if key != "schema"
            },
        }
        for label, malformed in malformed_values.items():
            with self.subTest(malformed=label):
                changed = deepcopy(item)
                changed["source_spec_correspondence"] = malformed
                projection = source_record_source_item_projection(changed)
                self.assertIsInstance(projection, dict)
                self.assertEqual(projection["source_spec_correspondence"], malformed)
                changed_identity = raw_identity(changed)
                self.assertNotEqual(changed_identity[0], original[0])
                self.assertNotEqual(changed_identity[1], original[1])
                self.assertNotEqual(changed_identity[2], original[2])

    def test_human_review_identity_separates_exact_correspondence_receipts(self) -> None:
        item: dict[str, object] = {
            "source_kind": "theorem",
            "statement": "Every admissible allocation has the stated witness.",
            "source_spec_correspondence": {
                "schema": 1,
                "source_atoms_sha256": "a" * 64,
                "spec_closure_sha256": "b" * 64,
                "spec_surface_sha256": "c" * 64,
                "closure_environment_sha256": "d" * 64,
                "item_identity_sha256": "e" * 64,
                "source_atom_bindings": [
                    {
                        "source_atom_sha256": "f" * 64,
                        "spec_component_sha256s": ["1" * 64],
                        "semantic_bridge": "The Spec is the source endpoint.",
                    }
                ],
                "closure_node_dispositions": [],
            },
        }
        original_raw = source_record_source_item_semantic_sha256(item, "")
        original_review = source_record_human_review_semantic_sha256(item, "")

        refreshed = deepcopy(item)
        correspondence = refreshed["source_spec_correspondence"]
        assert isinstance(correspondence, dict)
        correspondence["spec_closure_sha256"] = "9" * 64
        bindings = correspondence["source_atom_bindings"]
        assert isinstance(bindings, list) and isinstance(bindings[0], dict)
        bindings[0]["semantic_bridge"] = "A refreshed exact correspondence explanation."
        self.assertEqual(
            source_record_source_item_semantic_sha256(refreshed, ""), original_raw
        )
        self.assertEqual(
            source_record_human_review_semantic_sha256(refreshed, ""), original_review
        )

        changed_source = deepcopy(refreshed)
        changed_source["statement"] = "Every admissible allocation has another witness."
        self.assertNotEqual(
            source_record_human_review_semantic_sha256(changed_source, ""),
            original_review,
        )

        future_correspondence = deepcopy(refreshed)
        future = future_correspondence["source_spec_correspondence"]
        assert isinstance(future, dict)
        future["future_semantic_field"] = "unrecognized"
        self.assertNotEqual(
            source_record_human_review_semantic_sha256(
                future_correspondence, ""
            ),
            original_review,
        )

    def test_raw_cache_map_receipt_pins_coverage_protocol_only(self) -> None:
        source_map = {
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "items": {
                "result": {
                    "source_kind": "theorem",
                    "statement": "The endpoint holds.",
                }
            },
        }
        with patch.object(
            coverage_scope,
            "formalization_coverage_protocol_digest",
            return_value="a" * 64,
        ):
            original = source_map_cache_semantic_sha256(source_map)
        with patch.object(
            coverage_scope,
            "formalization_coverage_protocol_digest",
            return_value="b" * 64,
        ):
            changed = source_map_cache_semantic_sha256(source_map)
        self.assertNotEqual(original, changed)

        with patch.object(
            coverage_scope,
            "formalization_protocol_digest",
            return_value="c" * 64,
        ):
            first_legacy = legacy_source_map_cache_semantic_sha256(source_map)
        with patch.object(
            coverage_scope,
            "formalization_protocol_digest",
            return_value="d" * 64,
        ):
            second_legacy = legacy_source_map_cache_semantic_sha256(source_map)
        self.assertNotEqual(first_legacy, second_legacy)

    def test_named_result_reconciliation_receipt_is_audit_only_for_semantic_reuse(
        self,
    ) -> None:
        """Core pins are validated by closeout, not a reason to rerun raw review."""

        source_map = {
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "fixture source-only reviewer",
                "method": "fixture source scan",
                "validated_at": "2026-07-28T12:00:00Z",
                "source_artifact_sha256": "a" * 64,
                "discovered_named_result_sha256": "b" * 64,
                "heading_kinds": {"condition": "assumption"},
            },
            "items": {
                "opaque_source_storage": {
                    "source_kind": "theorem",
                    "statement": "Every admissible input has a witness.",
                    "source_presentation_reconciliation": {
                        "schema": 1,
                        "relation": "conservative_text_span_core",
                        "presentation_kind": "theorem",
                        "presentation_label": "Theorem 1",
                        "core_anchor": {
                            "path": "source.txt",
                            "line_start": 1,
                            "line_end": 2,
                            "quoted_text": (
                                "Theorem 1. Every admissible input has a witness.\n"
                                "Its displayed conclusion is complete."
                            ),
                            "quoted_text_sha256": "c" * 64,
                        },
                        "boundary_reason": "completed_statement_then_explanation",
                        "semantic_basis": "Fixture source-only basis.",
                        "validator": "fixture source-only reviewer",
                        "validated_at": "2026-07-28T12:00:00Z",
                    },
                }
            },
        }
        original_raw = source_map_cache_semantic_sha256(source_map)
        original_item = source_item_coverage_sha256(
            source_map["items"]["opaque_source_storage"],
            NAMED_THEORETICAL_STATEMENTS,
        )

        bookkeeping_only = deepcopy(source_map)
        bookkeeping_only["source_named_result_inventory_review"][
            "validated_at"
        ] = "2026-07-28T13:00:00Z"
        bookkeeping_only["source_named_result_inventory_review"][
            "discovered_named_result_sha256"
        ] = "d" * 64
        bookkeeping_only["items"]["opaque_source_storage"][
            "source_presentation_reconciliation"
        ]["semantic_basis"] = "Updated source-only reconciliation note."
        self.assertEqual(
            source_map_cache_semantic_sha256(bookkeeping_only), original_raw
        )
        self.assertEqual(
            source_item_coverage_sha256(
                bookkeeping_only["items"]["opaque_source_storage"],
                NAMED_THEORETICAL_STATEMENTS,
            ),
            original_item,
        )

        changed_classification = deepcopy(source_map)
        changed_classification["source_named_result_inventory_review"][
            "heading_kinds"
        ] = {"condition": "theorem"}
        self.assertNotEqual(
            source_map_cache_semantic_sha256(changed_classification), original_raw
        )

        receipt_without_classification = deepcopy(source_map)
        receipt_without_classification["source_named_result_inventory_review"].pop(
            "heading_kinds"
        )
        no_receipt = deepcopy(receipt_without_classification)
        no_receipt.pop("source_named_result_inventory_review")
        self.assertEqual(
            source_map_cache_semantic_sha256(receipt_without_classification),
            source_map_cache_semantic_sha256(no_receipt),
        )

    def test_status_cache_projection_tracks_route_effect_not_free_wording(self) -> None:
        """Only status changes with routing/quarantine meaning reopen raw reuse."""

        theorem = {
            "source_kind": "theorem",
            "statement": "Every admissible input has a witness.",
            "source_status": "under_review",
        }
        theorem_neutral = deepcopy(theorem)
        theorem_neutral["source_status"] = "resolved after independent review"
        theorem_support = deepcopy(theorem)
        theorem_support["source_status"] = "support_only"
        theorem_quarantined = deepcopy(theorem)
        theorem_quarantined["source_status"] = "quarantined_source_defect"

        # Existing normal status labels remain byte-for-byte cache compatible.
        self.assertEqual(
            source_item_coverage_sha256(theorem, NAMED_THEORETICAL_STATEMENTS),
            source_item_coverage_sha256(
                theorem_neutral, NAMED_THEORETICAL_STATEMENTS
            ),
        )
        self.assertIsNone(source_item_direct_status_policy_projection(theorem))
        self.assertIsNone(
            source_item_direct_status_policy_projection(theorem_neutral)
        )

        for changed in (theorem_support, theorem_quarantined):
            with self.subTest(status=changed["source_status"]):
                self.assertNotEqual(
                    source_item_coverage_sha256(
                        theorem, NAMED_THEORETICAL_STATEMENTS
                    ),
                    source_item_coverage_sha256(
                        changed, NAMED_THEORETICAL_STATEMENTS
                    ),
                )
                self.assertIsNotNone(
                    source_item_direct_status_policy_projection(changed)
                )

        # A model row already has a structured model route. Its redundant
        # status wording must not reopen LBG-style current evidence.
        model = {
            "source_kind": "model",
            "statement": "The observed process has the stated law.",
            "source_status": "shared source-model representation convention",
        }
        model_without_status = deepcopy(model)
        model_without_status.pop("source_status")
        self.assertTrue(source_item_effective_route_policy(model)["is_model_convention"])
        self.assertEqual(
            source_item_coverage_sha256(model, NAMED_THEORETICAL_STATEMENTS),
            source_item_coverage_sha256(
                model_without_status, NAMED_THEORETICAL_STATEMENTS
            ),
        )
        self.assertEqual(
            source_map_cache_semantic_sha256({"items": {"model": model}}),
            source_map_cache_semantic_sha256(
                {"items": {"model": model_without_status}}
            ),
        )
        self.assertIsNone(source_item_direct_status_policy_projection(model))

        # Free prose in a formula status no longer manufactures a model route.
        # In normal named-theory mode, a standalone formula is not part of the
        # raw generator's selected source surface, so its transition cannot
        # reopen an unrelated aggregate receipt. Deep mode selects it and
        # therefore retains the fail-closed transition marker.
        formula = {
            "source_kind": "formula",
            "statement": "The likelihood has the displayed domain.",
            "source_status": (
                "global-max scope is conditional on an explicit domain convention"
            ),
        }
        formula_policy = source_item_effective_route_policy(formula)
        self.assertFalse(formula_policy["is_model_convention"])
        self.assertTrue(formula_policy["allows_direct_route"])
        formula_transition = source_item_direct_status_policy_projection(formula)
        assert formula_transition is not None
        self.assertIn("legacy_status_route_policy", formula_transition)
        formula_without_status = deepcopy(formula)
        formula_without_status.pop("source_status")
        self.assertEqual(
            source_map_cache_semantic_sha256({"items": {"formula": formula}}),
            source_map_cache_semantic_sha256(
                {"items": {"formula": formula_without_status}}
            ),
        )
        self.assertNotEqual(
            source_map_cache_semantic_sha256(
                {
                    "source_coverage_mode": DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
                    "items": {"formula": formula},
                }
            ),
            source_map_cache_semantic_sha256(
                {
                    "source_coverage_mode": DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
                    "items": {"formula": formula_without_status},
                }
            ),
        )

        # Convention IDs pin prerequisite provenance. They cannot silently
        # reclassify a named theorem conclusion as a model convention.
        theorem_with_convention_dependency = {
            "source_kind": "theorem",
            "title": "Theorem 1.",
            "statement": "Every admissible input has a witness.",
            "model_convention_ids": ["MODEL-CONVENTION-1"],
        }
        dependency_policy = source_item_effective_route_policy(
            theorem_with_convention_dependency
        )
        self.assertFalse(dependency_policy["is_model_convention"])
        self.assertTrue(dependency_policy["allows_direct_route"])
        self.assertFalse(dependency_policy["allows_source_model_convention_route"])

    def test_resolved_conjecture_is_inventory_not_unresolved_open_debt(self) -> None:
        item = {
            "source_kind": "open_problem",
            "claim_bearing": False,
            "source_scope_classification": (
                "source_resolved_within_paper_observation"
            ),
            "coverage_status": "subsumed_by_selected_result",
            "protocol_role": "subsumed_by_selected_result",
            "subsumed_by_source_item": "theorem_3_1",
        }

        policy = source_item_effective_route_policy(item)

        self.assertTrue(policy["is_source_resolved_within_paper"])
        self.assertFalse(policy["allows_direct_route"])

    def test_map_key_rename_reopens_aggregate_discovery_not_item_judgment(self) -> None:
        item = {
            "title": "Theorem 3",
            "statement": "Every admissible instance has a witness.",
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_location": "p. 8",
            "source_artifact_sha256": SOURCE_DIGEST,
        }
        before = {"legacy_navigation_key": item}
        after = {"renamed_navigation_key": deepcopy(item)}

        self.assertEqual(
            source_item_coverage_sha256(
                before["legacy_navigation_key"], NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                after["renamed_navigation_key"], NAMED_THEORETICAL_STATEMENTS
            ),
        )
        self.assertNotEqual(
            review_dashboard.paper_coverage_inventory_digest(
                before, mode=NAMED_THEORETICAL_STATEMENTS
            ),
            review_dashboard.paper_coverage_inventory_digest(
                after, mode=NAMED_THEORETICAL_STATEMENTS
            ),
        )

    def test_semantic_pins_reuse_renamed_source_item_and_review_row(self) -> None:
        """Navigation-key changes reuse only the same source item and Lean type."""

        from tempfile import TemporaryDirectory

        source_key = "current_source_navigation_key"
        saved_source_key = "legacy_source_navigation_key"
        current_row_name = "current_review_row_name"
        saved_row_name = "legacy_review_row_name"
        source_statement = "Theorem 4. Every admissible input has the checked property."
        manifest: dict[str, object] = {
            "schema": 2,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {
                        "tag": "const",
                        "name": "True",
                        "levels": [],
                    },
                    "display": "True",
                }
            ],
        }
        manifest["sha256"] = review_dashboard.signature_manifest_digest(manifest)
        row = review_dashboard.ReviewItem(
            name=current_row_name,
            kind="theorem",
            lean_statement=f"theorem {current_row_name} : True",
            paper_statement=source_statement,
            agent_statement=source_statement,
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
            llm_match_judgment="matches",
            llm_match_paper_statement_sha256=review_dashboard.statement_digest(
                source_statement
            ),
        )

        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SemanticCoverageRenamePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_text = source_statement + "\n"
            (folder / "source.txt").write_text(source_text, encoding="utf-8")
            source_sha256 = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
            quote_sha256 = hashlib.sha256(source_statement.encode("utf-8")).hexdigest()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "source_artifact_path": "source.txt",
                        "source_artifact_sha256": source_sha256,
                        "items": {
                            source_key: {
                                "title": "Theorem 4",
                                "statement": source_statement,
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "source_url": "https://example.invalid/paper",
                                "source_location": "source.txt:1-1",
                                "source_anchor_evidence": [
                                    {
                                        "path": "source.txt",
                                        "line_start": 1,
                                        "line_end": 1,
                                        "quoted_text": source_statement,
                                        "quoted_text_sha256": quote_sha256,
                                    }
                                ],
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            source_item = inventory[source_key]
            item_digest = source_item_coverage_sha256(
                source_item, NAMED_THEORETICAL_STATEMENTS
            )
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": (
                            review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
                        ),
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                        "validator": "independent-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-07-26T12:00:00Z",
                        # These aggregate pins must be allowed to drift when
                        # the source item and elaborated row signature remain
                        # semantically current.
                        "paper_statement_inventory_sha256": "0" * 64,
                        "review_surface_sha256": "0" * 64,
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "items": {
                            saved_source_key: {
                                "coverage": "covered",
                                "review_rows": [saved_row_name],
                                "review_row_signature_sha256": {
                                    saved_row_name: manifest["sha256"]
                                },
                                "reason": (
                                    "The reviewed theorem establishes the exact "
                                    "source property."
                                ),
                                "source_evidence": (
                                    "The source theorem is recorded at the pinned "
                                    "source location."
                                ),
                                "statement_sha256": source_item["statement_sha256"],
                                "source_anchor_quote_identity_sha256": (
                                    review_dashboard.source_anchor_quote_identity(source_item)[0]
                                ),
                                "source_item_coverage_digest_schema": (
                                    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                                ),
                                "source_item_coverage_sha256": (
                                    item_digest
                                ),
                                "validator": "independent-test-agent",
                                "validated_at": "2026-07-26T12:00:00Z",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            cheap_summary = review_dashboard.source_inventory_precheck_summary(folder)
            full_summary = review_dashboard.paper_coverage_audit_summary(folder, [row])
            current_digest = source_item_coverage_sha256(
                review_dashboard.paper_statement_inventory(folder)[source_key],
                NAMED_THEORETICAL_STATEMENTS,
            )

        self.assertEqual(
            cheap_summary["semantic_item_rebinding_count"],
            1,
        )
        self.assertEqual(item_digest, current_digest)
        self.assertEqual(
            cheap_summary["recorded_source_coverage_mode"],
            NAMED_THEORETICAL_STATEMENTS,
        )
        self.assertFalse(cheap_summary["needs_attention"])
        self.assertFalse(full_summary["stale_inventory"])
        self.assertTrue(full_summary["stale_surface"])
        for field in (
            "missing_coverage",
            "extra_coverage",
            "out_of_mode_coverage",
            "missing_statement_digest",
            "stale_statement",
            "stale_source_items",
            "unverified_reused_source_items",
            "semantic_reuse_source_anchor_errors",
            "legacy_unpinned_items",
        ):
            self.assertEqual(
                cheap_summary[field],
                full_summary[field],
                f"fast and full coverage consumers diverged on {field}",
            )
        self.assertEqual(
            cheap_summary["source_artifact_current"],
            full_summary["source_artifact_current"],
        )
        self.assertEqual(
            cheap_summary["source_coverage_mode_mismatch"],
            full_summary["source_coverage_mode_mismatch"],
        )
        self.assertEqual(full_summary["semantic_item_rebinding_count"], 1)
        self.assertEqual(
            full_summary["semantic_item_rebindings"],
            [f"{source_key} <- {saved_source_key}"],
        )
        self.assertEqual(
            full_summary["semantic_row_rebindings"],
            [f"{source_key}: {saved_row_name} -> {current_row_name}"],
        )
        self.assertEqual(full_summary["semantic_row_rebinding_count"], 1)
        self.assertEqual(full_summary["invalid_row_links"], [])
        self.assertEqual(full_summary["coverage_row_signature_errors"], [])
        self.assertFalse(full_summary["needs_attention"])
        self.assertFalse(full_summary["source_to_lean_needs_attention"])

    def test_coverage_summary_indexes_current_row_signatures_once(self) -> None:
        """Many coverage rows share one exact current-signature index."""

        from tempfile import TemporaryDirectory

        source_statements = {
            "first_source": "Theorem 1. Every first input has the checked property.",
            "second_source": "Theorem 2. Every second input has the checked property.",
        }

        def signature_manifest(constant: str) -> dict[str, object]:
            result: dict[str, object] = {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": {
                            "tag": "const",
                            "name": constant,
                            "levels": [],
                        },
                        "display": constant,
                    }
                ],
            }
            result["sha256"] = review_dashboard.signature_manifest_digest(result)
            return result

        manifests = {
            "first": signature_manifest("True"),
            "second": signature_manifest("False"),
        }
        rows = [
            review_dashboard.ReviewItem(
                name=f"current_{label}_row",
                kind="theorem",
                lean_statement=f"theorem current_{label}_row : {constant}",
                paper_statement=source_statements[f"{label}_source"],
                agent_statement=source_statements[f"{label}_source"],
                lean_signature_manifest=manifests[label],
                lean_signature_sha256=str(manifests[label]["sha256"]),
                llm_match_judgment="matches",
                llm_match_paper_statement_sha256=(
                    review_dashboard.statement_digest(
                        source_statements[f"{label}_source"]
                    )
                ),
            )
            for label, constant in (("first", "True"), ("second", "False"))
        ]

        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SharedCoverageSignatureIndexPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_text = "\n".join(source_statements.values()) + "\n"
            (folder / "source.txt").write_text(source_text, encoding="utf-8")
            source_sha256 = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
            source_items = {
                source_key: {
                    "title": f"Theorem {line_number}",
                    "statement": source_statement,
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_url": "https://example.invalid/paper",
                    "source_location": f"source.txt:{line_number}-{line_number}",
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": line_number,
                            "line_end": line_number,
                            "quoted_text": source_statement,
                            "quoted_text_sha256": hashlib.sha256(
                                source_statement.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                }
                for line_number, (source_key, source_statement) in enumerate(
                    source_statements.items(), start=1
                )
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "source_artifact_path": "source.txt",
                        "source_artifact_sha256": source_sha256,
                        "items": source_items,
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            coverage_items = {}
            for label in ("first", "second"):
                source_key = f"{label}_source"
                old_row = f"saved_{label}_row"
                source_item = inventory[source_key]
                coverage_items[source_key] = {
                    "coverage": "covered",
                    "review_rows": [old_row],
                    "review_row_signature_sha256": {
                        old_row: manifests[label]["sha256"]
                    },
                    "reason": "The reviewed theorem establishes the source result.",
                    "source_evidence": "The pinned source theorem states the result.",
                    "statement_sha256": source_item["statement_sha256"],
                    "source_item_coverage_digest_schema": (
                        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                    ),
                    "source_item_coverage_sha256": source_item_coverage_sha256(
                        source_item, NAMED_THEORETICAL_STATEMENTS
                    ),
                    "validator": "independent-test-agent",
                    "validated_at": "2026-08-02T12:00:00Z",
                }
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": (
                            review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
                        ),
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "independent-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-08-02T12:00:00Z",
                        "paper_statement_inventory_sha256": "0" * 64,
                        "review_surface_sha256": "0" * 64,
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "items": coverage_items,
                    }
                ),
                encoding="utf-8",
            )

            with patch.object(
                review_dashboard,
                "_current_row_signature_digest",
                wraps=review_dashboard._current_row_signature_digest,
            ) as signature_digest:
                summary = review_dashboard.paper_coverage_audit_summary(folder, rows)

        self.assertEqual(signature_digest.call_count, len(rows))
        self.assertEqual(summary["semantic_row_rebinding_count"], 2)
        self.assertEqual(
            summary["semantic_row_rebindings"],
            [
                "first_source: saved_first_row -> current_first_row",
                "second_source: saved_second_row -> current_second_row",
            ],
        )

    def test_shared_signature_index_preserves_ambiguous_rebind_failure(self) -> None:
        """A renamed route still cannot choose between equal Lean signatures."""

        manifest: dict[str, object] = {
            "schema": 2,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "atoms": [
                {
                    "ref": "result",
                    "role": "conclusion",
                    "canonical": {
                        "tag": "const",
                        "name": "True",
                        "levels": [],
                    },
                    "display": "True",
                }
            ],
        }
        manifest["sha256"] = review_dashboard.signature_manifest_digest(manifest)
        rows = {
            name: review_dashboard.ReviewItem(
                name=name,
                kind="theorem",
                lean_statement=f"theorem {name} : True",
                paper_statement="Every input has the checked property.",
                agent_statement="Every input has the checked property.",
                lean_signature_manifest=manifest,
                lean_signature_sha256=str(manifest["sha256"]),
            )
            for name in ("first_current_route", "second_current_route")
        }
        raw_item = {
            "coverage": "covered",
            "review_rows": ["renamed_saved_route"],
            "review_row_signature_sha256": {
                "renamed_saved_route": manifest["sha256"]
            },
        }

        index = review_dashboard._current_row_signature_index(rows)
        rebound_item, changes, rebound = (
            review_dashboard._semantic_rebound_coverage_item(raw_item, index)
        )

        self.assertEqual(
            index,
            {
                manifest["sha256"]: [
                    "first_current_route",
                    "second_current_route",
                ]
            },
        )
        self.assertEqual(rebound_item, raw_item)
        self.assertEqual(changes, [])
        self.assertFalse(rebound)

    def test_shared_signature_index_matches_fresh_per_item_indexes(self) -> None:
        """Index reuse is state-free across every route-resolution outcome."""

        def row_with_signature(name: str, constant: str) -> review_dashboard.ReviewItem:
            manifest: dict[str, object] = {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": {
                            "tag": "const",
                            "name": constant,
                            "levels": [],
                        },
                        "display": constant,
                    }
                ],
            }
            manifest["sha256"] = review_dashboard.signature_manifest_digest(manifest)
            return review_dashboard.ReviewItem(
                name=name,
                kind="theorem",
                lean_statement=f"theorem {name} : {constant}",
                paper_statement="Every input has the checked property.",
                agent_statement="Every input has the checked property.",
                lean_signature_manifest=manifest,
                lean_signature_sha256=str(manifest["sha256"]),
            )

        rows = {
            row.name: row
            for row in (
                row_with_signature("unique_current_route", "False"),
                row_with_signature("duplicate_current_route_a", "True"),
                row_with_signature("duplicate_current_route_b", "True"),
            )
        }
        unique_digest = rows[
            "unique_current_route"
        ].lean_signature_sha256
        duplicate_digest = rows[
            "duplicate_current_route_a"
        ].lean_signature_sha256
        raw_items = [
            {
                "review_rows": ["unique_saved_route"],
                "review_row_signature_sha256": {
                    "unique_saved_route": unique_digest
                },
            },
            {
                "review_rows": ["duplicate_saved_route"],
                "review_row_signature_sha256": {
                    "duplicate_saved_route": duplicate_digest
                },
            },
            {
                "review_rows": ["unique_current_route"],
                "review_row_signature_sha256": {
                    "unique_current_route": unique_digest
                },
            },
            {
                "review_rows": ["unique_saved_route"],
                "review_row_signature_sha256": {},
            },
        ]

        shared_index = review_dashboard._current_row_signature_index(rows)
        original_index = deepcopy(shared_index)
        reused_results = [
            review_dashboard._semantic_rebound_coverage_item(item, shared_index)
            for item in raw_items
        ]
        fresh_results = [
            review_dashboard._semantic_rebound_coverage_item(
                item, review_dashboard._current_row_signature_index(rows)
            )
            for item in raw_items
        ]

        self.assertEqual(reused_results, fresh_results)
        self.assertEqual(shared_index, original_index)
        self.assertTrue(reused_results[0][2])
        self.assertFalse(reused_results[1][2])
        self.assertFalse(reused_results[2][2])
        self.assertFalse(reused_results[3][2])

    def test_unanchored_current_item_digest_cannot_bypass_stale_aggregate_review(
        self,
    ) -> None:
        """A map's own statement text is not source-byte evidence for reuse."""

        from tempfile import TemporaryDirectory

        source_key = "opaque_source_item"
        source_statement = "Theorem 5. Every checked input has a source witness."
        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "UnanchoredSemanticReusePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_text = source_statement + "\n"
            (folder / "source.txt").write_text(source_text, encoding="utf-8")
            source_sha256 = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_curated": True,
                        "source_inventory_kind": "curated_test",
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "source_artifact_path": "source.txt",
                        "source_artifact_sha256": source_sha256,
                        "items": {
                            source_key: {
                                "title": "Theorem 5",
                                "statement": source_statement,
                                "source_kind": "theorem",
                                "claim_bearing": True,
                                "source_url": "https://example.invalid/paper",
                                "source_location": "source.txt:1-1",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            inventory = review_dashboard.paper_statement_inventory(folder)
            source_item = inventory[source_key]
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": (
                            review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
                        ),
                        "audit_kind": "source_to_dashboard_agent",
                        "source_grounded": True,
                        "validator": "independent-test-agent",
                        "validator_type": "agent",
                        "validated_at": "2026-07-26T12:00:00Z",
                        # Force the narrow semantic-reuse path rather than
                        # accepting historical aggregate freshness.
                        "paper_statement_inventory_sha256": "0" * 64,
                        "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                        "items": {
                            source_key: {
                                "coverage": "covered",
                                "review_rows": [],
                                "reason": "The source claim was reviewed.",
                                "source_evidence": "The exact source line is recorded.",
                                "statement_sha256": source_item["statement_sha256"],
                                "source_item_coverage_digest_schema": (
                                    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                                ),
                                "source_item_coverage_sha256": (
                                    source_item_coverage_sha256(
                                        source_item,
                                        NAMED_THEORETICAL_STATEMENTS,
                                    )
                                ),
                                "validator": "independent-test-agent",
                                "validated_at": "2026-07-26T12:00:00Z",
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            summary = review_dashboard.source_inventory_precheck_summary(folder)

        self.assertEqual(summary["stale_source_items"], [])
        self.assertEqual(summary["unverified_reused_source_items"], [source_key])
        self.assertIn(source_key, summary["semantic_reuse_source_anchor_errors"])
        self.assertTrue(summary["needs_attention"])

    def test_source_artifact_change_revalidates_each_reused_anchor(self) -> None:
        """Unchanged item text cannot bypass changed canonical source bytes."""

        from tempfile import TemporaryDirectory

        source_key = "opaque_source_item"
        source_statement = "Theorem 1. Every checked input has a source witness."
        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "SourceArtifactReusePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_path = folder / "source.txt"
            source_path.write_text(
                "Preface.\n" + source_statement + "\n", encoding="utf-8"
            )
            initial_source_sha256 = hashlib.sha256(source_path.read_bytes()).hexdigest()
            quote_sha256 = hashlib.sha256(source_statement.encode("utf-8")).hexdigest()
            source_map = {
                "source_curated": True,
                "source_inventory_kind": "curated_test",
                "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": initial_source_sha256,
                "items": {
                    source_key: {
                        "title": "Theorem 1",
                        "statement": source_statement,
                        "source_kind": "theorem",
                        "claim_bearing": True,
                        "source_url": "https://example.invalid/paper",
                        "source_location": "source.txt:2-2",
                        "source_anchor_evidence": [
                            {
                                "path": "source.txt",
                                "line_start": 2,
                                "line_end": 2,
                                "quoted_text": source_statement,
                                "quoted_text_sha256": quote_sha256,
                            }
                        ],
                    }
                },
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(source_map), encoding="utf-8")
            inventory = review_dashboard.paper_statement_inventory(folder)
            item = inventory[source_key]
            inventory_digest = review_dashboard.paper_coverage_inventory_digest(
                inventory,
                mode=NAMED_THEORETICAL_STATEMENTS,
                statement_map_payload=source_map,
            )
            coverage_sidecar = {
                "schema": 1,
                "paper": folder.name,
                "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                "audit_kind": "source_to_dashboard_agent",
                "source_grounded": True,
                "validator": "independent-test-agent",
                "validator_type": "agent",
                "validated_at": "2026-07-26T12:00:00Z",
                "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": initial_source_sha256,
                "paper_statement_inventory_sha256": inventory_digest,
                "items": {
                    source_key: {
                        "coverage": "covered",
                        "review_rows": [],
                        "reason": "The source statement was independently reviewed.",
                        "source_evidence": "The exact source theorem is pinned.",
                        "statement_sha256": item["statement_sha256"],
                        "source_item_coverage_digest_schema": (
                            SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                        ),
                        "source_item_coverage_sha256": source_item_coverage_sha256(
                            item, NAMED_THEORETICAL_STATEMENTS
                        ),
                        "validator": "independent-test-agent",
                        "validated_at": "2026-07-26T12:00:00Z",
                    }
                },
            }
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(coverage_sidecar), encoding="utf-8"
            )

            initial_summary = review_dashboard.source_inventory_precheck_summary(folder)
            self.assertTrue(initial_summary["source_artifact_current"])
            self.assertEqual(initial_summary["unverified_reused_source_items"], [])

            # Change canonical bytes but leave the saved semantic item and
            # stale quote untouched. The aggregate semantic inventory is
            # intentionally unchanged; only byte-anchor validation detects it.
            source_path.write_text(
                "Preface.\nTheorem 1. A different source witness is required.\n",
                encoding="utf-8",
            )
            source_map["source_artifact_sha256"] = hashlib.sha256(
                source_path.read_bytes()
            ).hexdigest()
            map_path.write_text(json.dumps(source_map), encoding="utf-8")

            changed_summary = review_dashboard.source_inventory_precheck_summary(folder)

        self.assertFalse(changed_summary["source_artifact_current"])
        self.assertEqual(changed_summary["stale_source_items"], [])
        self.assertEqual(
            changed_summary["unverified_reused_source_items"], [source_key]
        )
        self.assertIn(
            source_key, changed_summary["semantic_reuse_source_anchor_errors"]
        )
        self.assertTrue(changed_summary["needs_attention"])

    def test_changed_anchor_is_revalidated_with_current_artifact_and_digest(self) -> None:
        """Navigation-only anchor movement must not bypass byte validation."""

        from tempfile import TemporaryDirectory

        source_key = "opaque_source_item"
        source_statement = "Theorem 1. Every checked input has a source witness."
        with TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "AnchorMovementReusePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_path = folder / "source.txt"
            source_path.write_text(
                "Preface.\n" + source_statement + "\n", encoding="utf-8"
            )
            source_sha256 = hashlib.sha256(source_path.read_bytes()).hexdigest()
            quote_sha256 = hashlib.sha256(source_statement.encode("utf-8")).hexdigest()
            source_map = {
                "source_curated": True,
                "source_inventory_kind": "curated_test",
                "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": source_sha256,
                "items": {
                    source_key: {
                        "title": "Theorem 1",
                        "statement": source_statement,
                        "source_kind": "theorem",
                        "claim_bearing": True,
                        "source_url": "https://example.invalid/paper",
                        "source_location": "source.txt:2-2",
                        "source_anchor_evidence": [
                            {
                                "path": "source.txt",
                                "line_start": 2,
                                "line_end": 2,
                                "quoted_text": source_statement,
                                "quoted_text_sha256": quote_sha256,
                            }
                        ],
                    }
                },
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(source_map), encoding="utf-8")
            inventory = review_dashboard.paper_statement_inventory(folder)
            item = inventory[source_key]
            coverage_sidecar = {
                "schema": 1,
                "paper": folder.name,
                "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                "audit_kind": "source_to_dashboard_agent",
                "source_grounded": True,
                "validator": "independent-test-agent",
                "validator_type": "agent",
                "validated_at": "2026-07-26T12:00:00Z",
                "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": source_sha256,
                "paper_statement_inventory_sha256": (
                    review_dashboard.paper_coverage_inventory_digest(
                        inventory,
                        mode=NAMED_THEORETICAL_STATEMENTS,
                        statement_map_payload=source_map,
                    )
                ),
                "items": {
                    source_key: {
                        "coverage": "covered",
                        "review_rows": [],
                        "reason": "The source statement was independently reviewed.",
                        "source_evidence": "The exact source theorem is pinned.",
                        "statement_sha256": item["statement_sha256"],
                        "source_item_coverage_digest_schema": (
                            SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                        ),
                        "source_item_coverage_sha256": source_item_coverage_sha256(
                            item, NAMED_THEORETICAL_STATEMENTS
                        ),
                        "validator": "independent-test-agent",
                        "validated_at": "2026-07-26T12:00:00Z",
                    }
                },
            }
            (audit / "paper_coverage_llm.json").write_text(
                json.dumps(coverage_sidecar), encoding="utf-8"
            )
            initial_summary = review_dashboard.source_inventory_precheck_summary(folder)
            self.assertEqual(initial_summary["unverified_reused_source_items"], [])

            # Locator/range metadata are intentionally outside the semantic
            # digest. The quote is kept unchanged, so this must be caught by
            # current byte validation rather than an aggregate-digest change.
            source_map["items"][source_key]["source_location"] = "source.txt:1-1"
            source_map["items"][source_key]["source_anchor_evidence"][0].update(
                {"line_start": 1, "line_end": 1}
            )
            map_path.write_text(json.dumps(source_map), encoding="utf-8")

            changed_summary = review_dashboard.source_inventory_precheck_summary(folder)

        self.assertTrue(changed_summary["source_artifact_current"])
        self.assertEqual(changed_summary["stale_source_items"], [])
        self.assertEqual(
            changed_summary["unverified_reused_source_items"], [source_key]
        )
        self.assertIn(
            source_key, changed_summary["semantic_reuse_source_anchor_errors"]
        )
        self.assertTrue(changed_summary["needs_attention"])


if __name__ == "__main__":
    unittest.main()
