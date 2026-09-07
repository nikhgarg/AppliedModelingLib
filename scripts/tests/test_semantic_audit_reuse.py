#!/usr/bin/env python3
"""Regression tests for fail-closed semantic sidecar reuse."""

from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard  # noqa: E402
from scripts import semantic_audit_reuse as REUSE  # noqa: E402
from scripts.lean_signature_manifest import (  # noqa: E402
    normalize_signature_manifest,
    semantic_dependency_manifest,
)
from scripts.semantic_audit_reuse import (  # noqa: E402
    LEGACY_V4_COVERAGE_PROMPT_VERSION,
    RowSnapshot,
    _reuse_pin_from_embedded,
    _statement_validator,
    migrate_legacy_v4_coverage,
    migrate_sidecars,
    migrate_statement_items,
    source_reuse_pin,
)
from scripts.source_coverage_scope import (  # noqa: E402
    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
)


MODEL_CONVENTION_ID = "FIXTURE-SOURCE-MODEL-01"


def manifest(
    *, result: str = "P", dependency_body: str = "stable imported body"
) -> dict[str, object]:
    value: dict[str, object] = {
        "schema": 2,
        "declaration_kind": "theorem",
        "conclusion_mode": "type_only",
        "atoms": [
            {
                "ref": "b/0",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {
                    "tag": "app",
                    "fn": {"tag": "const", "name": "LT.lt", "levels": []},
                    "arg": {"tag": "lit", "value": "0"},
                },
                "display": "0 < x",
            },
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {"tag": "proposition", "name": result},
                "display": result,
            },
        ],
    }
    value["semantic_dependency_graph"] = {
        "schema": 1,
        "root_declaration": "Fixture.endpoint",
        "complete": True,
        "nodes": [
            {
                "declaration": "Fixture.endpoint",
                "module_origin": "Fixture.Interface",
                "origin_class": "review_closure",
                "declaration_kind": "theorem",
                "canonical_identity": {
                    "tag": "local_theorem",
                    "type": {"tag": "proposition", "name": result},
                },
            },
            {
                "declaration": "Fixture.importedHelper",
                "module_origin": "Fixture.ImportedModel",
                "origin_class": "review_closure",
                "declaration_kind": "definition",
                "canonical_identity": {
                    "tag": "inlined_definition",
                    "type": {"tag": "sort", "level": {"tag": "zero"}},
                    "value": {"tag": "literal", "value": dependency_body},
                },
            },
        ],
        "edges": [
            {
                "source": "Fixture.endpoint",
                "target": "Fixture.importedHelper",
                "role": "type_dependency",
            }
        ],
        "failures": [],
    }
    value["elaborated_proposition_graph"] = {
        "schema": 1,
        "complete": True,
        "nodes": [
            {
                "path": "result",
                "kind": "constant",
                "canonical": {"tag": "proposition", "name": result},
            }
        ],
        "edges": [],
        "failures": [],
    }
    normalized = normalize_signature_manifest(value)
    assert normalized is not None
    normalized["semantic_dependency_module_identities"] = []
    normalized["semantic_dependency_environment_identities"] = [
        {"path": "lean-toolchain", "sha256": "e" * 64},
        {"path": "lake-manifest.json", "sha256": "f" * 64},
    ]
    dependency = semantic_dependency_manifest(normalized)
    assert dependency is not None
    normalized["semantic_dependency_manifest"] = dependency
    return normalized


def source_item(
    statement: str = "The endpoint holds.",
    *,
    quote: str | None = None,
    corrected: bool = False,
    approval_digest: str = "a" * 64,
    model_convention_ids: object | None = None,
    source_status: str = "",
    source_note: str = "",
) -> dict[str, object]:
    quote = quote if quote is not None else statement
    item: dict[str, object] = {
        "title": "Theorem 1",
        "statement": statement,
        "aliases": [],
        "source": "audit/paper_statement_map.json",
        "coverage_status": "",
        "protocol_role": "",
        "corrected_target": None,
        "source_kind": "theorem",
        "claim_bearing": True,
        "source_scope_classification": "",
        "user_approved_scope_exclusion": None,
        "scope_reason": "",
        "source_evidence": "",
        "source_artifact_path": "source.txt",
        "source_artifact_sha256": "b" * 64,
        "canonical_source_artifact_path": "source.txt",
        "canonical_source_artifact_sha256": "b" * 64,
        "source_anchor_evidence_required": True,
        "source_anchor_evidence": [
            {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": quote,
                "quoted_text_sha256": __import__("hashlib")
                .sha256(quote.encode("utf-8"))
                .hexdigest(),
            }
        ],
        "source_defect_ids": [],
        "support_lean_declarations": [],
        "spec_lean_declarations": [],
        "semantic_contract": None,
        "lean_declarations": [],
        "proof_lean_declarations": [],
        "source_location": "source.txt:1-1",
        "source_url": "https://example.invalid/paper",
        "source_note": source_note,
        "source_status": source_status,
        "statement_sha256": review_dashboard.statement_digest(statement),
    }
    if model_convention_ids is not None:
        item["model_convention_ids"] = copy.deepcopy(model_convention_ids)
    if corrected:
        target: dict[str, object] = {
            "schema": review_dashboard.CORRECTED_TARGET_SCHEMA,
            "statement": "The corrected endpoint holds.",
            "archival_source_locator": "source.txt:1-1",
            "archival_source_quote_sha256": __import__("hashlib")
            .sha256(quote.encode("utf-8"))
            .hexdigest(),
            "governing_defect_ids": ["source-defect-1"],
            "archival_equivalence_claimed": False,
            "approval": {
                "artifact_sha256": approval_digest,
            },
        }
        target["corrected_target_sha256"] = review_dashboard.corrected_target_digest(
            target
        )
        item.update(
            {
                "coverage_status": "corrected_source_statement",
                "corrected_target": target,
                "source_defect_ids": ["source-defect-1"],
            }
        )
    return item


def source_proof_fidelity_ledger(
    *, formal_meaning: str = "The finite carrier is explicit in the source-model target."
) -> dict[str, object]:
    return {
        "model_conventions": [
            {
                "id": MODEL_CONVENTION_ID,
                "source_locator": "source.txt:1-1",
                "classification": "explicit_formalization_convention",
                "formal_meaning": formal_meaning,
                "why_needed": "The archival statement leaves the finite carrier boundary implicit.",
                "checked_scope": "The reviewed interface exposes the finite carrier directly.",
            }
        ]
    }


def source_target(item: dict[str, object]) -> tuple[str, str]:
    return review_dashboard._source_item_coverage_statement(item)


def statement_entry(
    old_manifest: dict[str, object],
    item: dict[str, object],
    *,
    source_key: str,
    lean: str = "theorem exact_endpoint : P",
) -> dict[str, object]:
    statement, source_digest = source_target(item)
    manifest_atoms = old_manifest.get("atoms")
    assert isinstance(manifest_atoms, list)
    atoms = {
        atom["ref"]: review_dashboard.signature_manifest_atom_digest(atom)
        for atom in manifest_atoms
        if isinstance(atom, dict)
    }
    route: dict[str, object] = {
        "source_item": source_key,
        "source_statement_sha256": source_digest,
        "source_location": "source.txt:1-1",
        "route_kind": "direct",
    }
    if item.get("coverage_status") == "corrected_source_statement":
        target = item["corrected_target"]
        assert isinstance(target, dict)
        approval = target["approval"]
        assert isinstance(approval, dict)
        route.update(
            {
                "route_kind": "approved_corrected_target",
                "archival_statement_sha256": item["statement_sha256"],
                "archival_source_location": "source.txt:1-1",
                "corrected_target_sha256": target["corrected_target_sha256"],
                "governing_defect_ids": ["source-defect-1"],
                "archival_equivalence_claimed": False,
                "approval_artifact_sha256": approval["artifact_sha256"],
            }
        )
    return {
        "judgment": "matches",
        "lean_statement_sha256": review_dashboard.statement_digest(lean),
        "lean_signature_sha256": old_manifest["sha256"],
        "paper_statement_sha256": review_dashboard.statement_digest(statement),
        "tex_statement_sha256": review_dashboard.statement_digest(statement),
        "source_routes": [route],
        "source_obligations": [
            {
                "id": "source_conclusion",
                "kind": "conclusion",
                "statement": statement,
                "source_item": source_key,
                "source_statement_sha256": source_digest,
                "source_location": "source.txt:1-1",
            }
        ],
        "lean_obligations": [
            {
                "id": "lean_assumption",
                "kind": "assumption",
                "signature_ref": "b/0",
                "signature_atom_sha256": atoms["b/0"],
            },
            {
                "id": "lean_conclusion",
                "kind": "conclusion",
                "signature_ref": "result",
                "signature_atom_sha256": atoms["result"],
            },
        ],
    }


def source_map(key: str, item: dict[str, object]) -> dict[str, object]:
    """Build the minimum source-map snapshot needed by legacy-v4 migration."""

    return {
        "schema": 1,
        "source_coverage_mode": "named_theoretical_statements",
        "source_artifact_path": "source.txt",
        "source_artifact_sha256": "b" * 64,
        "items": {key: copy.deepcopy(item)},
    }


def cache_snapshot(row: RowSnapshot) -> dict[str, object]:
    """Freeze the old cache's independent row-signature field and manifest."""

    return {
        "schema": 20,
        "rows": [
            {
                "name": row.name,
                "lean_statement": row.lean_statement,
                "paper_statement": row.paper_statement,
                "agent_statement": row.tex_statement,
                "lean_signature_manifest": copy.deepcopy(row.manifest),
                "lean_signature_sha256": row.manifest["sha256"],
            }
        ],
    }


def legacy_v4_coverage(
    item: dict[str, object], *, source_key: str, review_row: str
) -> dict[str, object]:
    _statement, source_digest = source_target(item)
    return {
        "schema": 1,
        "paper": "FixturePaper",
        "prompt_version": LEGACY_V4_COVERAGE_PROMPT_VERSION,
        "audit_kind": "source_to_dashboard_agent",
        "source_grounded": True,
        "seed_scaffold": False,
        "validator": "fixture-independent-reviewer",
        "validator_type": "agent",
        "validated_at": "2026-07-27T00:00:00Z",
        "comment": "Legacy independent source-to-dashboard judgment.",
        "items": {
            source_key: {
                "coverage": "covered",
                "review_rows": [review_row],
                "reason": "The reviewed source endpoint and dashboard endpoint agree.",
                "source_evidence": "Theorem 1 in the pinned source artifact.",
                "dashboard_evidence": "The reviewed theorem row.",
                "statement_sha256": source_digest,
            }
        },
    }


class SemanticAuditReuseTests(unittest.TestCase):
    def setUp(self) -> None:
        self.legacy_manifest = manifest()
        # This simulates a prior manifest serializer.  Atom structures remain
        # byte-identical, but its aggregate digest is deliberately different.
        self.legacy_manifest["sha256"] = "c" * 64
        self.current_manifest = manifest()
        self.old_item = source_item()
        self.current_item = copy.deepcopy(self.old_item)
        self.lean = "theorem exact_endpoint : P"
        statement, _digest = source_target(self.old_item)
        self.old_row = RowSnapshot(
            name="old_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=statement,
            tex_statement=statement,
            manifest=self.legacy_manifest,
        )
        self.current_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=statement,
            tex_statement=statement,
            manifest=self.current_manifest,
        )

    def _legacy_v4_inputs(
        self,
        *,
        old_item: dict[str, object] | None = None,
        current_item: dict[str, object] | None = None,
        current_row: RowSnapshot | None = None,
        old_cache: dict[str, object] | None = None,
    ) -> tuple[dict[str, object], dict[str, object], dict[str, object], list[RowSnapshot], dict[str, object]]:
        """Return a renamed-but-identical v4 source/cache/current fixture."""

        old_item = copy.deepcopy(old_item or self.old_item)
        current_item = copy.deepcopy(current_item or self.current_item)
        _statement, target = source_target(old_item)
        old_row = RowSnapshot(
            name="legacy_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=target,
            tex_statement=target,
            manifest=copy.deepcopy(self.current_manifest),
            declared_signature_sha256=str(self.current_manifest["sha256"]),
        )
        if current_row is None:
            current_row = RowSnapshot(
                name="current_dashboard_navigation",
                lean_statement=self.lean,
                paper_statement=target,
                tex_statement=target,
                manifest=copy.deepcopy(self.current_manifest),
                declared_signature_sha256=str(self.current_manifest["sha256"]),
            )
        return (
            legacy_v4_coverage(
                old_item,
                source_key="legacy_source_navigation",
                review_row=old_row.name,
            ),
            source_map("current_source_navigation", current_item),
            source_map("legacy_source_navigation", old_item),
            [current_row],
            old_cache if old_cache is not None else cache_snapshot(old_row),
        )

    def _migrate_legacy_v4(
        self,
        *,
        opt_in: bool = True,
        old_item: dict[str, object] | None = None,
        current_item: dict[str, object] | None = None,
        current_row: RowSnapshot | None = None,
        old_cache: dict[str, object] | None = None,
        current_anchor_errors: dict[str, list[str]] | None = None,
    ) -> tuple[dict[str, object] | None, dict[str, object]]:
        legacy, current_map, previous_map, current_rows, previous_cache = (
            self._legacy_v4_inputs(
                old_item=old_item,
                current_item=current_item,
                current_row=current_row,
                old_cache=old_cache,
            )
        )
        return migrate_legacy_v4_coverage(
            legacy,
            legacy_v4_opt_in=opt_in,
            paper="FixturePaper",
            folder=ROOT,
            current_source_map=current_map,
            previous_source_map=previous_map,
            previous_review_cache=previous_cache,
            current_rows=current_rows,
            current_review_surface_sha256="e" * 64,
            current_anchor_errors=(
                current_anchor_errors if current_anchor_errors is not None else {}
            ),
        )

    def test_malformed_sidecar_keys_abort_both_outputs_atomically(self) -> None:
        cases = {
            "statement collision": (
                {"items": {"same": {}, " same": {}}},
                {"items": {"coverage": {}}},
            ),
            "statement nonstring": (
                {"items": {1: {}}},
                {"items": {"coverage": {}}},
            ),
            "coverage whitespace": (
                {"items": {"statement": {}}},
                {"items": {"coverage ": {}}},
            ),
        }
        for label, (statement_sidecar, coverage_sidecar) in cases.items():
            with self.subTest(case=label):
                original_statement = copy.deepcopy(statement_sidecar)
                original_coverage = copy.deepcopy(coverage_sidecar)
                statement, coverage, report = migrate_sidecars(
                    statement_sidecar,
                    coverage_sidecar,
                    current_rows=[],
                    current_inventory={},
                    current_mode="named_theoretical_statements",
                    current_anchor_errors={},
                    validate_statement=None,
                )
                self.assertEqual(statement, original_statement)
                self.assertEqual(coverage, original_coverage)
                self.assertTrue(report["global_error"])
                self.assertEqual(report["statement"], {})
                self.assertEqual(report["coverage"], {})

    def test_duplicate_current_row_names_are_permanently_ambiguous(self) -> None:
        duplicate_valid = RowSnapshot(
            name="duplicate-row",
            lean_statement=self.lean,
            paper_statement="P",
            tex_statement="P",
            manifest=self.current_manifest,
        )
        duplicate_invalid = RowSnapshot(
            name="duplicate-row",
            lean_statement=self.lean,
            paper_statement="P",
            tex_statement="P",
            manifest={"sha256": "not-a-digest"},
        )
        unique = RowSnapshot(
            name="unique-row",
            lean_statement=self.lean,
            paper_statement="P",
            tex_statement="P",
            manifest=self.current_manifest,
        )

        index = REUSE._current_signature_index(
            [duplicate_invalid, duplicate_valid, duplicate_valid, unique]
        )

        self.assertNotIn("duplicate-row", index)
        self.assertEqual(index, {"unique-row": self.current_manifest["sha256"]})

    def test_migrates_legacy_v4_coverage_only_with_content_verified_renames(self) -> None:
        output, report = self._migrate_legacy_v4()

        self.assertIsNotNone(output)
        assert output is not None
        self.assertEqual(report["accepted_item_count"], 1)
        self.assertEqual(report["rejected_item_count"], 0)
        self.assertEqual(
            output["prompt_version"],
            review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
        )
        migrated = output["items"]["current_source_navigation"]
        self.assertEqual(migrated["review_rows"], ["current_dashboard_navigation"])
        self.assertEqual(
            migrated["review_row_signature_sha256"],
            {"current_dashboard_navigation": self.current_manifest["sha256"]},
        )
        self.assertEqual(
            migrated["source_item_coverage_digest_schema"],
            SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        )
        metadata = migrated["semantic_reuse_v1"]
        assert isinstance(metadata, dict)
        self.assertRegex(
            str(metadata.get("review_validator_identity_sha256") or ""),
            r"^[0-9a-f]{64}$",
        )
        legacy_receipt = metadata["legacy_v4_coverage_migration_v1"]
        assert isinstance(legacy_receipt, dict)
        binding = legacy_receipt["review_rows"][0]
        assert isinstance(binding, dict)
        self.assertEqual(binding["legacy_review_row"], "legacy_dashboard_navigation")
        self.assertEqual(binding["current_review_row"], "current_dashboard_navigation")
        self.assertEqual(
            binding["old_lean_signature_sha256"], self.current_manifest["sha256"]
        )

    def test_legacy_v4_migration_requires_explicit_opt_in(self) -> None:
        output, report = self._migrate_legacy_v4(opt_in=False)

        self.assertIsNone(output)
        self.assertIn("explicit", str(report.get("global_error") or ""))

    def test_legacy_v4_migration_requires_both_historical_snapshots(self) -> None:
        legacy, current_map, previous_map, current_rows, previous_cache = (
            self._legacy_v4_inputs()
        )
        for missing_map, missing_cache, expected in (
            (None, previous_cache, "source-map snapshot"),
            (previous_map, None, "review-cache snapshot"),
        ):
            with self.subTest(expected=expected):
                output, report = migrate_legacy_v4_coverage(
                    legacy,
                    legacy_v4_opt_in=True,
                    paper="FixturePaper",
                    folder=ROOT,
                    current_source_map=current_map,
                    previous_source_map=missing_map,
                    previous_review_cache=missing_cache,
                    current_rows=current_rows,
                    current_review_surface_sha256="e" * 64,
                    current_anchor_errors={},
                )
                self.assertIsNone(output)
                self.assertIn(expected, str(report.get("global_error") or ""))

    def test_legacy_v4_migration_rejects_changed_source_identity(self) -> None:
        changed_current_item = source_item(quote="A changed anchored source quote.")
        output, report = self._migrate_legacy_v4(current_item=changed_current_item)

        self.assertIsNone(output)
        decision = report["items"]["legacy_source_navigation"]
        self.assertFalse(decision["accepted"])
        self.assertIn("source semantic/quote identity", decision["reason"])

    def test_legacy_v4_migration_rejects_unverified_current_source_anchor(self) -> None:
        output, report = self._migrate_legacy_v4(
            current_anchor_errors={"current_source_navigation": ["anchor hash mismatch"]}
        )

        self.assertIsNone(output)
        decision = report["items"]["legacy_source_navigation"]
        self.assertFalse(decision["accepted"])
        self.assertIn("byte-verified", decision["reason"])

    def test_legacy_v4_migration_requires_fresh_corrected_target_pins(self) -> None:
        corrected_item = source_item(
            statement="The archival endpoint holds.", corrected=True
        )
        output, report = self._migrate_legacy_v4(
            old_item=corrected_item,
            current_item=copy.deepcopy(corrected_item),
        )

        self.assertIsNone(output)
        decision = report["items"]["legacy_source_navigation"]
        self.assertFalse(decision["accepted"])
        self.assertIn("corrected source item", decision["reason"])

    def test_legacy_v4_migration_allows_declaration_name_change(self) -> None:
        _statement, target = source_target(self.current_item)
        renamed_current_row = RowSnapshot(
            name="current_dashboard_navigation",
            lean_statement="theorem renamed_endpoint : P",
            paper_statement=target,
            tex_statement=target,
            manifest=copy.deepcopy(self.current_manifest),
            declared_signature_sha256=str(self.current_manifest["sha256"]),
        )
        output, report = self._migrate_legacy_v4(current_row=renamed_current_row)

        self.assertIsNotNone(output)
        self.assertEqual(report["accepted_item_count"], 1)

    def test_legacy_v4_migration_rejects_changed_lean_manifest_structure(self) -> None:
        _statement, target = source_target(self.current_item)
        changed_manifest = manifest(result="Q")
        changed_current_row = RowSnapshot(
            name="current_dashboard_navigation",
            lean_statement="theorem renamed_endpoint : Q",
            paper_statement=target,
            tex_statement=target,
            manifest=changed_manifest,
            declared_signature_sha256=str(changed_manifest["sha256"]),
        )
        output, report = self._migrate_legacy_v4(current_row=changed_current_row)

        self.assertIsNone(output)
        decision = report["items"]["legacy_source_navigation"]
        self.assertFalse(decision["accepted"])
        self.assertIn("semantic Lean row identity", decision["reason"])

    def test_legacy_v4_migration_rejects_unverified_current_row_signature(self) -> None:
        _statement, target = source_target(self.current_item)
        unsigned_current_row = RowSnapshot(
            name="current_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=target,
            tex_statement=target,
            manifest=copy.deepcopy(self.current_manifest),
        )
        output, report = self._migrate_legacy_v4(current_row=unsigned_current_row)

        self.assertIsNone(output)
        decision = report["items"]["legacy_source_navigation"]
        self.assertFalse(decision["accepted"])
        self.assertIn("declared Lean signature", decision["reason"])

    def test_legacy_v4_migration_rejects_unverified_old_row_signature(self) -> None:
        legacy, _current_map, _previous_map, _current_rows, old_cache = (
            self._legacy_v4_inputs()
        )
        rows = old_cache["rows"]
        assert isinstance(rows, list)
        row = rows[0]
        assert isinstance(row, dict)
        row["lean_signature_sha256"] = "f" * 64
        # Rebuild only the remaining inputs so the stale cache is the sole
        # changed identity.
        _legacy, current_map, previous_map, current_rows, _old_cache = (
            self._legacy_v4_inputs(old_cache=old_cache)
        )
        output, report = migrate_legacy_v4_coverage(
            legacy,
            legacy_v4_opt_in=True,
            paper="FixturePaper",
            folder=ROOT,
            current_source_map=current_map,
            previous_source_map=previous_map,
            previous_review_cache=old_cache,
            current_rows=current_rows,
            current_review_surface_sha256="e" * 64,
            current_anchor_errors={},
        )

        self.assertIsNone(output)
        self.assertIn("signature does not match", str(report.get("global_error") or ""))

    def test_reuse_validator_versions_direct_expression_gate(self) -> None:
        definition_item = copy.deepcopy(self.current_item)
        definition_item["source_kind"] = "definition"
        definition_entry = statement_entry(
            self.current_manifest,
            definition_item,
            source_key="semantic_source_item",
        )
        theorem_entry = statement_entry(
            self.current_manifest,
            self.current_item,
            source_key="semantic_source_item",
        )
        formula_item = copy.deepcopy(self.current_item)
        formula_item["source_kind"] = "formula"
        formula_entry = statement_entry(
            self.current_manifest,
            formula_item,
            source_key="semantic_source_item",
        )
        inventory = {"semantic_source_item": definition_item}

        with mock.patch.object(
            review_dashboard,
            "semantic_obligation_ledger_error",
            return_value="blocked by test gate",
        ) as validator:
            self.assertIn(
                "blocked by test gate",
                _statement_validator(definition_entry, self.current_row, inventory),
            )
            self.assertTrue(
                validator.call_args.kwargs[
                    "require_source_definition_semantics_review"
                ]
            )

            theorem_inventory = {
                "semantic_source_item": copy.deepcopy(self.current_item)
            }
            self.assertIn(
                "blocked by test gate",
                _statement_validator(theorem_entry, self.current_row, theorem_inventory),
            )
            self.assertFalse(
                validator.call_args.kwargs[
                    "require_source_definition_semantics_review"
                ]
            )

            formula_inventory = {"semantic_source_item": formula_item}
            self.assertIn(
                "blocked by test gate",
                _statement_validator(
                    formula_entry,
                    self.current_row,
                    formula_inventory,
                ),
            )
            self.assertFalse(
                validator.call_args.kwargs[
                    "require_source_definition_semantics_review"
                ]
            )
            self.assertIn(
                "blocked by test gate",
                _statement_validator(
                    formula_entry,
                    self.current_row,
                    formula_inventory,
                    include_direct_expressions=True,
                ),
            )
            self.assertTrue(
                validator.call_args.kwargs[
                    "require_source_definition_semantics_review"
                ]
            )

    def test_reuse_validator_preserves_raw_source_target_contract(self) -> None:
        """Reuse validates the literal source target, not map-summary navigation."""

        entry = statement_entry(
            self.current_manifest,
            self.current_item,
            source_key="semantic_source_item",
        )
        entry.update(
            {
                "prompt_version": (
                    review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION
                ),
                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
            }
        )
        with (
            mock.patch.object(
                review_dashboard,
                "semantic_obligation_ledger_error",
                return_value="",
            ),
            mock.patch.object(
                review_dashboard,
                "source_route_pin_error",
                return_value="",
            ) as route_validator,
        ):
            self.assertEqual(
                _statement_validator(
                    entry,
                    self.current_row,
                    {"semantic_source_item": self.current_item},
                ),
                "",
            )
        self.assertTrue(
            route_validator.call_args.kwargs["require_verbatim_source_inputs"]
        )

    def test_migrates_serializer_refresh_only_after_full_content_identity(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        output, decisions, bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertTrue(decisions["old_statement_navigation"]["accepted"])
        migrated = output["old_statement_navigation"]
        self.assertEqual(
            migrated["lean_signature_sha256"], self.current_manifest["sha256"]
        )
        self.assertEqual(
            migrated["source_routes"][0]["source_item"], "new_source_navigation"
        )
        self.assertEqual(
            migrated["source_obligations"][0]["source_item"],
            "new_source_navigation",
        )
        self.assertIn("semantic_reuse_v1", migrated)
        self.assertEqual(
            bindings["old_statement_navigation"].current_row_name,
            "renamed_dashboard_navigation",
        )

    def test_statement_reuse_ignores_proof_body_and_unrelated_module_diagnostics(
        self,
    ) -> None:
        """Closing `sorry` or editing another theorem does not reopen this item."""

        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        unchanged_semantics = copy.deepcopy(self.current_manifest)
        # These whole-module/proof diagnostics deliberately change. The shared
        # per-row semantic dependency digest does not include them.
        unchanged_semantics["review_module_olean_sha256"] = "d" * 64
        unchanged_semantics["theorem_proof_body_sha256"] = "e" * 64
        current_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=unchanged_semantics,
        )

        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertTrue(decisions["old_statement_navigation"]["accepted"])

    def test_imported_definition_body_change_reopens_statement_and_coverage(
        self,
    ) -> None:
        """Unchanged interface text/type cannot hide reachable model drift."""

        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        changed_manifest = manifest(dependency_body="changed imported body")
        self.assertEqual(
            changed_manifest["sha256"], self.current_manifest["sha256"]
        )
        self.assertNotEqual(
            changed_manifest["semantic_dependency_manifest"]
            ["semantic_dependency_sha256"],
            self.current_manifest["semantic_dependency_manifest"]
            ["semantic_dependency_sha256"],
        )
        changed_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=changed_manifest,
        )
        _target, target_digest = source_target(self.old_item)
        statement_sidecar = {"items": {"old_statement_navigation": entry}}
        coverage_sidecar = {
            "items": {
                "old_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["old_dashboard_navigation"],
                    "review_row_signature_sha256": {
                        "old_dashboard_navigation": self.legacy_manifest["sha256"]
                    },
                }
            }
        }

        _statements, _coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[changed_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_statement=None,
        )

        self.assertFalse(report["statement"]["old_statement_navigation"]["accepted"])
        self.assertIn(
            "transitive elaborated semantic dependency",
            report["statement"]["old_statement_navigation"]["reason"],
        )
        self.assertFalse(report["coverage"]["old_source_navigation"]["accepted"])
        self.assertIn(
            "accepted statement item",
            report["coverage"]["old_source_navigation"]["reason"],
        )

    def test_missing_transitive_dependency_manifest_fails_closed(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        incomplete = copy.deepcopy(self.current_manifest)
        incomplete.pop("semantic_dependency_manifest")
        current_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=incomplete,
        )

        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertFalse(decisions["old_statement_navigation"]["accepted"])
        self.assertIn(
            "does not retain its generated semantic dependency manifest",
            decisions["old_statement_navigation"]["reason"],
        )

    def test_migrates_explicit_canonical_model_convention_pins(self) -> None:
        old_item = source_item(
            model_convention_ids=[MODEL_CONVENTION_ID],
            source_status="source theorem under documented model convention",
        )
        current_item = copy.deepcopy(old_item)
        ledger = source_proof_fidelity_ledger()
        entry = statement_entry(
            self.legacy_manifest, old_item, source_key="old_source_navigation"
        )

        output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_proof_fidelity=ledger,
            previous_inventory={"old_source_navigation": old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            previous_source_proof_fidelity=ledger,
            validate_entry=None,
        )

        self.assertTrue(decisions["old_statement_navigation"]["accepted"])
        metadata = output["old_statement_navigation"]["semantic_reuse_v1"]
        assert isinstance(metadata, dict)
        route_pins = metadata["source_routes"]
        assert isinstance(route_pins, list) and len(route_pins) == 1
        convention_pins = route_pins[0]["source_model_convention_pins"]
        assert isinstance(convention_pins, dict)
        self.assertEqual(
            convention_pins["model_convention_ids"], [MODEL_CONVENTION_ID]
        )
        digests = convention_pins["record_sha256_by_id"]
        assert isinstance(digests, dict)
        self.assertRegex(str(digests[MODEL_CONVENTION_ID]), r"^[0-9a-f]{64}$")

    def test_rejects_changed_canonical_model_convention_record(self) -> None:
        old_item = source_item(
            model_convention_ids=[MODEL_CONVENTION_ID],
            source_status="source theorem under documented model convention",
        )
        current_item = copy.deepcopy(old_item)
        entry = statement_entry(
            self.legacy_manifest, old_item, source_key="old_source_navigation"
        )

        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_proof_fidelity=source_proof_fidelity_ledger(
                formal_meaning="The source-model carrier now has a different formal meaning."
            ),
            previous_inventory={"old_source_navigation": old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            previous_source_proof_fidelity=source_proof_fidelity_ledger(),
            validate_entry=None,
        )

        self.assertFalse(decisions["old_statement_navigation"]["accepted"])
        self.assertIn(
            "source semantic/quote identity",
            decisions["old_statement_navigation"]["reason"],
        )

    def test_textual_convention_wording_does_not_create_dependency(self) -> None:
        old_item = source_item(
            source_note="This convention wording is descriptive prose only."
        )
        current_item = copy.deepcopy(old_item)
        entry = statement_entry(
            self.legacy_manifest, old_item, source_key="old_source_navigation"
        )

        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_proof_fidelity=source_proof_fidelity_ledger(),
            previous_inventory={"old_source_navigation": old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            previous_source_proof_fidelity=source_proof_fidelity_ledger(),
            validate_entry=None,
        )

        self.assertTrue(decisions["old_statement_navigation"]["accepted"])
        self.assertEqual(REUSE._model_convention_ids(old_item), ([], ""))
        ordinary = source_item(source_note="This note uses different wording.")
        convention_word = source_item(
            source_note="This convention wording is descriptive prose only."
        )
        self.assertEqual(
            REUSE._model_convention_ids(ordinary),
            REUSE._model_convention_ids(convention_word),
        )

        structured = source_item(
            source_status="documented_source_model_convention"
        )
        ids, error = REUSE._model_convention_ids(structured)
        self.assertIsNone(ids)
        self.assertIn("requires nonempty model_convention_ids", error)

    def test_explicit_model_convention_ids_remain_fail_closed(self) -> None:
        self.assertEqual(
            REUSE._model_convention_ids(
                source_item(model_convention_ids=[MODEL_CONVENTION_ID])
            ),
            ([MODEL_CONVENTION_ID], ""),
        )
        ids, error = REUSE._model_convention_ids(
            source_item(model_convention_ids=[])
        )
        self.assertIsNone(ids)
        self.assertIn("nonempty list of unique strings", error)

    def test_rejects_unknown_or_ambiguous_model_convention_ids(self) -> None:
        unknown_item = source_item(model_convention_ids=["UNKNOWN-CONVENTION"])
        pin, error = source_reuse_pin(
            unknown_item,
            "named_theoretical_statements",
            source_proof_fidelity=source_proof_fidelity_ledger(),
        )
        self.assertIsNone(pin)
        self.assertIn("unknown canonical", error)

        duplicate_ledger = source_proof_fidelity_ledger()
        conventions = duplicate_ledger["model_conventions"]
        assert isinstance(conventions, list)
        conventions.append(copy.deepcopy(conventions[0]))
        item = source_item(model_convention_ids=[MODEL_CONVENTION_ID])
        pin, error = source_reuse_pin(
            item,
            "named_theoretical_statements",
            source_proof_fidelity=duplicate_ledger,
        )
        self.assertIsNone(pin)
        self.assertIn("duplicates id", error)

    def test_coverage_reuses_only_through_accepted_raw_statement_binding(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        target, target_digest = source_target(self.old_item)
        statement_sidecar = {"items": {"old_statement_navigation": entry}}
        coverage_sidecar = {
            "items": {
                "old_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["unrelated_old_row_name"],
                    "review_row_signature_sha256": {
                        "unrelated_old_row_name": self.legacy_manifest["sha256"]
                    },
                }
            }
        }
        migrated_statement, migrated_coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_coverage_inventory={
                "new_source_navigation": self.current_item
            },
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_map={
                "source_artifact_path": "fixture-source.txt",
                "source_artifact_sha256": "b" * 64,
            },
            current_review_surface_sha256="a" * 64,
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_statement=None,
        )

        self.assertTrue(report["statement"]["old_statement_navigation"]["accepted"])
        self.assertTrue(report["coverage"]["old_source_navigation"]["accepted"])
        coverage = migrated_coverage["items"]["new_source_navigation"]
        self.assertEqual(coverage["statement_sha256"], target_digest)
        self.assertEqual(coverage["review_rows"], ["renamed_dashboard_navigation"])
        self.assertEqual(
            coverage["review_row_signature_sha256"],
            {"renamed_dashboard_navigation": self.current_manifest["sha256"]},
        )
        self.assertIn(
            "semantic_reuse_v1",
            migrated_statement["items"]["old_statement_navigation"],
        )
        self.assertTrue(report["aggregate_coverage_receipt_refreshed"])

    def test_current_source_pin_is_computed_once_for_all_reuse_lanes(self) -> None:
        """Statement routes and coverage share one exact current-item identity."""

        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        _target, target_digest = source_target(self.old_item)
        statement_sidecar = {"items": {"old_statement_navigation": entry}}
        coverage_sidecar = {
            "items": {
                "old_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["old_dashboard_navigation"],
                    "review_row_signature_sha256": {
                        "old_dashboard_navigation": self.legacy_manifest["sha256"]
                    },
                }
            }
        }
        pinned_statement, pinned_coverage, first_report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_statement=None,
        )
        self.assertTrue(first_report["statement"]["old_statement_navigation"]["accepted"])
        self.assertTrue(first_report["coverage"]["old_source_navigation"]["accepted"])

        with mock.patch.object(
            REUSE, "source_reuse_pin", wraps=REUSE.source_reuse_pin
        ) as source_pin:
            _statement, _coverage, report = migrate_sidecars(
                pinned_statement,
                pinned_coverage,
                current_rows=[self.current_row],
                current_inventory={"new_source_navigation": self.current_item},
                current_mode="named_theoretical_statements",
                current_anchor_errors={},
                validate_statement=None,
            )

        self.assertTrue(report["statement"]["old_statement_navigation"]["accepted"])
        self.assertTrue(report["coverage"]["new_source_navigation"]["accepted"])
        self.assertEqual(source_pin.call_count, 1)

    def test_component_statement_inventory_computes_each_source_pin_once(
        self,
    ) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        _target, target_digest = source_target(self.old_item)
        statement_sidecar = {"items": {"old_statement_navigation": entry}}
        coverage_sidecar = {
            "items": {
                "old_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["old_dashboard_navigation"],
                    "review_row_signature_sha256": {
                        "old_dashboard_navigation": self.legacy_manifest["sha256"]
                    },
                }
            }
        }
        pinned_statement, pinned_coverage, first_report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_statement=None,
        )
        self.assertTrue(first_report["statement"]["old_statement_navigation"]["accepted"])

        component = source_item("A separately routed source component holds.")
        component["source_component_of"] = "new_source_navigation"
        statement_inventory = {
            "new_source_navigation": self.current_item,
            "component-content-address": component,
        }
        with mock.patch.object(
            REUSE, "source_reuse_pin", wraps=REUSE.source_reuse_pin
        ) as source_pin:
            _statement, _coverage, report = migrate_sidecars(
                pinned_statement,
                pinned_coverage,
                current_rows=[self.current_row],
                current_inventory={"new_source_navigation": self.current_item},
                current_statement_inventory=statement_inventory,
                current_mode="named_theoretical_statements",
                current_anchor_errors={},
                validate_statement=None,
            )

        self.assertTrue(report["statement"]["old_statement_navigation"]["accepted"])
        self.assertTrue(report["coverage"]["new_source_navigation"]["accepted"])
        self.assertEqual(source_pin.call_count, len(statement_inventory))

    def test_coverage_duplicate_signatures_use_verified_navigation_only(
        self,
    ) -> None:
        source_pin, source_error = source_reuse_pin(
            self.current_item, "named_theoretical_statements"
        )
        self.assertEqual(source_error, "")
        self.assertIsNotNone(source_pin)
        assert source_pin is not None
        _target, target_digest = source_target(self.current_item)
        shared_signature = self.current_manifest["sha256"]
        entry = {
            "coverage": "covered",
            "statement_sha256": target_digest,
            "source_item_coverage_sha256": source_pin[
                "source_item_semantic_sha256"
            ],
            "review_rows": ["row-a", "row-b"],
            "review_row_signature_sha256": {
                "row-a": shared_signature,
                "row-b": shared_signature,
            },
            "semantic_reuse_v1": {
                "schema": REUSE.ENTRY_REUSE_SCHEMA,
                REUSE.FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                    REUSE.formalization_review_protocol_digest()
                ),
                "source_item": source_pin,
                "source_coverage_mode": "named_theoretical_statements",
            },
        }
        binding_a = REUSE.StatementBinding(
            old_signature_sha256=shared_signature,
            current_row_name="current-row-a",
            raw_lean_sha256="1" * 64,
            manifest_structure_sha256="2" * 64,
            semantic_dependency_sha256="3" * 64,
        )
        binding_b = REUSE.StatementBinding(
            old_signature_sha256=shared_signature,
            current_row_name="current-row-b",
            raw_lean_sha256="4" * 64,
            manifest_structure_sha256="5" * 64,
            semantic_dependency_sha256="6" * 64,
        )

        output, decisions = REUSE.migrate_coverage_items(
            {"source-navigation": entry},
            current_inventory={"source-navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            statement_bindings={"row-a": binding_a, "row-b": binding_b},
        )

        self.assertTrue(decisions["source-navigation"]["accepted"])
        self.assertEqual(
            output["source-navigation"]["review_rows"],
            ["current-row-a", "current-row-b"],
        )

        renamed_entry = copy.deepcopy(entry)
        renamed_entry["review_rows"] = ["renamed-row"]
        renamed_entry["review_row_signature_sha256"] = {
            "renamed-row": shared_signature
        }
        _output, renamed_decisions = REUSE.migrate_coverage_items(
            {"source-navigation": renamed_entry},
            current_inventory={"source-navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            statement_bindings={"row-a": binding_a, "row-b": binding_b},
        )
        self.assertFalse(renamed_decisions["source-navigation"]["accepted"])
        self.assertIn(
            "does not identify one accepted statement item",
            renamed_decisions["source-navigation"]["reason"],
        )

    def test_bootstrap_user_approved_scope_exclusion_has_exact_zero_row_surface(
        self,
    ) -> None:
        item = copy.deepcopy(self.current_item)
        item.update(
            {
                "coverage_status": review_dashboard.USER_APPROVED_SCOPE_EXCLUSION,
                "source_kind": "prose_assertion",
                "inventory_role": "deep_only",
                "user_approved_scope_exclusion": {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                    "approval_reference": "Standing user instruction for this fixture.",
                    "approved_at": "2026-08-25",
                    "reason": "The unnumbered prose assertion remains visible but is outside the selected named-theory surface.",
                    "source_locator": "source.txt:1-1",
                    "source_evidence": "The pinned fixture sentence is the excluded unnumbered prose assertion.",
                    "source_anchor_quote_sha256": item["source_anchor_evidence"][0][
                        "quoted_text_sha256"
                    ],
                },
            }
        )
        _statement, target_digest = source_target(item)
        entry = {
            "coverage": review_dashboard.USER_APPROVED_SCOPE_EXCLUSION,
            "statement_sha256": target_digest,
            "review_rows": [],
            "review_row_signature_sha256": {},
            "support_declarations": [],
        }

        output, decisions = REUSE.migrate_coverage_items(
            {"scope-item": entry},
            current_inventory={"scope-item": item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            statement_bindings={},
            bootstrap_current=True,
        )

        self.assertTrue(decisions["scope-item"]["accepted"])
        self.assertEqual(output["scope-item"]["review_rows"], [])
        self.assertEqual(output["scope-item"]["review_row_signature_sha256"], {})
        self.assertIn(REUSE.REUSE_FIELD, output["scope-item"])

    def test_statement_navigation_disambiguates_but_never_overrides_drift(
        self,
    ) -> None:
        statement, _target = source_target(self.current_item)
        stable_row = RowSnapshot(
            name="stable-endpoint",
            lean_statement=self.lean,
            paper_statement=statement,
            tex_statement=statement,
            manifest=self.current_manifest,
        )
        entry = statement_entry(
            self.current_manifest,
            self.current_item,
            source_key="source-navigation",
            lean=self.lean,
        )
        bootstrapped, decisions, _bindings = migrate_statement_items(
            {"stable-endpoint": entry},
            current_rows=[stable_row],
            current_inventory={"source-navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            bootstrap_current=True,
            validate_entry=lambda _entry, _row, _inventory: "",
        )
        self.assertTrue(decisions["stable-endpoint"]["accepted"])

        renamed_duplicate = RowSnapshot(
            name="renamed-duplicate",
            lean_statement=self.lean,
            paper_statement=statement,
            tex_statement=statement,
            manifest=self.current_manifest,
        )
        _output, direct_decisions, _bindings = migrate_statement_items(
            bootstrapped,
            current_rows=[stable_row, renamed_duplicate],
            current_inventory={"source-navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            validate_entry=None,
        )
        self.assertTrue(direct_decisions["stable-endpoint"]["accepted"])
        self.assertEqual(
            direct_decisions["stable-endpoint"]["current_row"], "stable-endpoint"
        )

        drifted_exact = RowSnapshot(
            name="stable-endpoint",
            lean_statement=self.lean,
            paper_statement="A different paper-facing statement.",
            tex_statement=statement,
            manifest=self.current_manifest,
        )
        _output, drift_decisions, _bindings = migrate_statement_items(
            bootstrapped,
            current_rows=[drifted_exact, renamed_duplicate],
            current_inventory={"source-navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            validate_entry=None,
        )
        self.assertFalse(drift_decisions["stable-endpoint"]["accepted"])
        self.assertIn(
            "identity is missing",
            drift_decisions["stable-endpoint"]["reason"],
        )

    def test_component_parent_key_is_navigation_only(self) -> None:
        component = source_item("A semantically identified component clause.")
        component["source_component_of"] = "old-parent-navigation"
        renamed = copy.deepcopy(component)
        renamed["source_component_of"] = "new-parent-navigation"

        self.assertEqual(
            REUSE.source_item_coverage_sha256(
                component, "named_theoretical_statements"
            ),
            REUSE.source_item_coverage_sha256(
                renamed, "named_theoretical_statements"
            ),
        )
        old_pin, old_error = source_reuse_pin(
            component, "named_theoretical_statements"
        )
        new_pin, new_error = source_reuse_pin(
            renamed, "named_theoretical_statements"
        )
        self.assertEqual((old_error, new_error), ("", ""))
        self.assertEqual(old_pin, new_pin)

    def test_parent_partition_change_reopens_parent_reuse(self) -> None:
        parent = copy.deepcopy(self.current_item)
        parent[review_dashboard.SOURCE_DEFINITION_PARTITION_FIELD] = {
            "schema": 1,
            "complete": True,
            "semantic_relation": "jointly_equivalent_to_source_definition",
        }
        entry = statement_entry(
            self.current_manifest, parent, source_key="parent-navigation"
        )
        _target, target_digest = source_target(parent)
        statement_sidecar = {"items": {"current_statement_navigation": entry}}
        coverage_sidecar = {
            "items": {
                "parent-navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["current_navigation_only"],
                    "review_row_signature_sha256": {
                        "current_navigation_only": self.current_manifest["sha256"]
                    },
                }
            }
        }
        pinned_statement, pinned_coverage, first_report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"parent-navigation": parent},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            bootstrap_current=True,
            validate_statement=lambda _entry, _row, _inventory: "",
        )
        self.assertTrue(first_report["statement"]["current_statement_navigation"]["accepted"])

        changed_parent = copy.deepcopy(parent)
        changed_parent[review_dashboard.SOURCE_DEFINITION_PARTITION_FIELD][
            "complete"
        ] = False
        _statement, _coverage, second_report = migrate_sidecars(
            pinned_statement,
            pinned_coverage,
            current_rows=[self.current_row],
            current_inventory={"parent-navigation": changed_parent},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            validate_statement=None,
        )
        self.assertFalse(
            second_report["statement"]["current_statement_navigation"]["accepted"]
        )
        self.assertFalse(second_report["coverage"]["parent-navigation"]["accepted"])

    def test_historical_inventory_projection_preserves_partition_and_alias(
        self,
    ) -> None:
        partition = {"schema": 1, "complete": True}
        alias = {"schema": 1, "canonical_source_item": "canonical-item"}
        payload = {
            "items": {
                "source-navigation": {
                    "statement": "The endpoint holds.",
                    "source_location": "source.txt:1-1",
                    "source_definition_partition": partition,
                    "source_presentation_alias": alias,
                }
            }
        }

        inventory = REUSE.inventory_from_source_map(ROOT, payload)

        self.assertEqual(
            inventory["source-navigation"]["source_definition_partition"],
            partition,
        )
        self.assertEqual(
            inventory["source-navigation"]["source_presentation_alias"], alias
        )

    def test_inventory_projection_preserves_raw_semantic_context(self) -> None:
        context = [
            {
                "semantic_role": "source_model",
                "source_anchor_evidence": [
                    {
                        "quoted_text": "The source fixes the shared model.",
                        "quoted_text_sha256": __import__("hashlib")
                        .sha256(b"The source fixes the shared model.")
                        .hexdigest(),
                    }
                ],
            }
        ]
        payload = {
            "items": {
                "source-navigation": {
                    "statement": "The endpoint holds.",
                    "source_location": "source.txt:1-1",
                    "semantic_context_requirements": context,
                }
            }
        }

        inventory = REUSE.inventory_from_source_map(ROOT, payload)

        self.assertEqual(
            inventory["source-navigation"]["semantic_context_requirements"],
            context,
        )

    def test_validator_identity_drift_reopens_only_pinned_reuse(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        _target, target_digest = source_target(self.old_item)
        statement_sidecar = {"items": {"old_statement_navigation": entry}}
        coverage_sidecar = {
            "items": {
                "old_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["old_dashboard_navigation"],
                    "review_row_signature_sha256": {
                        "old_dashboard_navigation": self.legacy_manifest["sha256"]
                    },
                }
            }
        }
        validator = "1" * 64
        pinned_statement, pinned_coverage, first_report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            statement_validator_identities={"old_statement_navigation": validator},
            coverage_validator_identities={"old_source_navigation": validator},
            validate_statement=None,
        )
        self.assertTrue(first_report["statement"]["old_statement_navigation"]["accepted"])
        self.assertTrue(first_report["coverage"]["old_source_navigation"]["accepted"])

        _same_statement, _same_coverage, same = migrate_sidecars(
            pinned_statement,
            pinned_coverage,
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            statement_validator_identities={"old_statement_navigation": validator},
            coverage_validator_identities={"new_source_navigation": validator},
            validate_statement=None,
        )
        self.assertTrue(same["statement"]["old_statement_navigation"]["accepted"])
        self.assertTrue(same["coverage"]["new_source_navigation"]["accepted"])

        _changed_statement, _changed_coverage, changed = migrate_sidecars(
            pinned_statement,
            pinned_coverage,
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            statement_validator_identities={"old_statement_navigation": "2" * 64},
            coverage_validator_identities={"new_source_navigation": "2" * 64},
            validate_statement=None,
        )
        self.assertFalse(changed["statement"]["old_statement_navigation"]["accepted"])
        self.assertFalse(changed["coverage"]["new_source_navigation"]["accepted"])
        self.assertIn(
            "validator identity",
            changed["statement"]["old_statement_navigation"]["reason"],
        )
        self.assertIn(
            "validator identity",
            changed["coverage"]["new_source_navigation"]["reason"],
        )

    def test_validator_identity_inherits_current_sidecar_envelope(self) -> None:
        payload = {
            "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
            "validator": "independent fixture reviewer",
            "validator_type": "agent",
            "validated_at": "2026-07-31T00:00:00Z",
            "items": {"row": {"judgment": "matches"}},
        }
        identities, errors = REUSE.review_validator_identities(
            payload,
            expected_prompt_version=review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
        )
        self.assertEqual(errors, {})
        self.assertRegex(identities["row"], r"^[0-9a-f]{64}$")

        payload["validator"] = ""
        _identities, missing = REUSE.review_validator_identities(
            payload,
            expected_prompt_version=review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
        )
        self.assertIn("validator", missing["row"])

    def test_entry_local_pins_allow_later_reuse_without_historical_files(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        first, first_decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )
        self.assertTrue(first_decisions["old_statement_navigation"]["accepted"])

        renamed_lean = "theorem renamed_exact_endpoint : P"
        renamed_row = RowSnapshot(
            name="new_dashboard_navigation",
            lean_statement=renamed_lean,
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=copy.deepcopy(self.current_manifest),
        )
        second, second_decisions, second_bindings = migrate_statement_items(
            first,
            current_rows=[renamed_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            validate_entry=None,
        )

        self.assertTrue(second_decisions["old_statement_navigation"]["accepted"])
        migrated = second["old_statement_navigation"]
        self.assertEqual(
            migrated["lean_statement_sha256"],
            review_dashboard.statement_digest(renamed_lean),
        )
        self.assertEqual(
            migrated["semantic_reuse_v1"]["raw_lean_statement_sha256"],
            renamed_row.raw_lean_sha256,
        )
        self.assertEqual(
            second_bindings["old_statement_navigation"].current_row_name,
            "new_dashboard_navigation",
        )

    def test_entry_local_semantic_reuse_rejects_rename_collision(self) -> None:
        """Two name-only variants cannot both inherit one judgment."""

        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        first, first_decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )
        self.assertTrue(first_decisions["old_statement_navigation"]["accepted"])

        duplicate = RowSnapshot(
            name="colliding_dashboard_navigation",
            lean_statement="theorem another_exact_endpoint : P",
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=copy.deepcopy(self.current_manifest),
        )
        _second, decisions, bindings = migrate_statement_items(
            first,
            current_rows=[self.current_row, duplicate],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            validate_entry=None,
        )

        decision = decisions["old_statement_navigation"]
        self.assertFalse(decision["accepted"])
        self.assertIn("ambiguous", decision["reason"])
        self.assertEqual(bindings, {})

    def test_exact_tex_pin_resolves_otherwise_identical_semantic_rows(self) -> None:
        """Reviewed TeX semantics participates before ambiguity is declared."""

        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        first, first_decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )
        self.assertTrue(first_decisions["old_statement_navigation"]["accepted"])

        different_tex = RowSnapshot(
            name="misleading_old_dashboard_navigation",
            lean_statement="theorem another_exact_endpoint : P",
            paper_statement=self.current_row.paper_statement,
            tex_statement="A different mathematical rendering.",
            manifest=copy.deepcopy(self.current_manifest),
        )
        _second, decisions, bindings = migrate_statement_items(
            first,
            current_rows=[different_tex, self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            validate_entry=None,
        )

        self.assertTrue(decisions["old_statement_navigation"]["accepted"])
        self.assertEqual(
            bindings["old_statement_navigation"].current_row_name,
            self.current_row.name,
        )

    def test_entry_local_pin_binds_paper_and_tex_statement_digests(self) -> None:
        """Mutable top-level text pins cannot steer semantic candidate lookup."""

        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        first, first_decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )
        self.assertTrue(first_decisions["old_statement_navigation"]["accepted"])
        pinned = first["old_statement_navigation"]
        routes = pinned["source_routes"]

        for field, expected in (
            ("paper_statement_sha256", "paper statement pin"),
            ("tex_statement_sha256", "Lean-to-TeX statement pin"),
        ):
            with self.subTest(field=field):
                tampered = copy.deepcopy(pinned)
                tampered[field] = "f" * 64
                pin, error = _reuse_pin_from_embedded(tampered, routes)
                self.assertIsNone(pin)
                self.assertIn(expected, error)

    def test_opt_in_bootstrap_records_pins_only_after_current_validation(self) -> None:
        target, target_digest = source_target(self.current_item)
        statement_sidecar = {
            "items": {
                "current_statement_navigation": statement_entry(
                    self.current_manifest,
                    self.current_item,
                    source_key="current_source_navigation",
                )
            }
        }
        coverage_sidecar = {
            "items": {
                "current_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["current_navigation_only"],
                    "review_row_signature_sha256": {
                        "current_navigation_only": self.current_manifest["sha256"]
                    },
                }
            }
        }
        current_source_map = {
            "source_artifact_path": "fixture-source.txt",
            "source_artifact_sha256": "b" * 64,
        }
        _statement, coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"current_source_navigation": self.current_item},
            current_coverage_inventory={
                "current_source_navigation": self.current_item
            },
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_map=current_source_map,
            current_review_surface_sha256="a" * 64,
            bootstrap_current=True,
            validate_statement=lambda _entry, _row, _inventory: "",
        )

        self.assertTrue(report["statement"]["current_statement_navigation"]["accepted"])
        self.assertTrue(report["coverage"]["current_source_navigation"]["accepted"])
        self.assertTrue(
            report["coverage"]["current_source_navigation"]["bootstrap_current"]
        )
        self.assertIn(
            "semantic_reuse_v1",
            coverage["items"]["current_source_navigation"],
        )
        self.assertTrue(report["aggregate_coverage_receipt_refreshed"])
        self.assertEqual(
            coverage["paper_statement_inventory_sha256"],
            review_dashboard.paper_coverage_inventory_digest(
                {"current_source_navigation": self.current_item},
                mode="named_theoretical_statements",
                statement_map_payload=current_source_map,
            ),
        )
        self.assertEqual(coverage["review_surface_sha256"], "a" * 64)
        self.assertEqual(coverage["source_artifact_path"], "fixture-source.txt")

        _statement, _coverage, rejected = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"current_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            bootstrap_current=True,
            validate_statement=None,
        )
        self.assertFalse(
            rejected["statement"]["current_statement_navigation"]["accepted"]
        )
        self.assertIn(
            "full statement validator",
            rejected["statement"]["current_statement_navigation"]["reason"],
        )

    def test_bootstrap_component_rows_pin_entry_local_statement_without_cross_binding(
        self,
    ) -> None:
        """A shared parent display cannot replace or conflate component targets."""

        parent_statement = "The parent definition contains both clauses."
        entries: dict[str, dict[str, object]] = {}
        rows: list[RowSnapshot] = []
        inventory: dict[str, dict[str, object]] = {}
        component_statement_by_row: dict[str, str] = {}
        for index, component_statement in enumerate(
            (
                "The first semantic component holds.",
                "The second semantic component holds.",
            ),
            start=1,
        ):
            source_key = f"component-content-{index}"
            row_name = f"component-surface-{index}"
            lean = f"abbrev component_surface_{index} : P := by exact proof"
            component = source_item(component_statement)
            component["source_component_of"] = "shared-parent-navigation"
            anchors = component["source_anchor_evidence"]
            assert isinstance(anchors, list) and isinstance(anchors[0], dict)
            anchor_sha256 = str(anchors[0]["quoted_text_sha256"])
            component["source_component_anchor_sha256"] = anchor_sha256
            inventory[source_key] = component

            entry = statement_entry(
                self.current_manifest,
                component,
                source_key=source_key,
                lean=lean,
            )
            routes = entry["source_routes"]
            assert isinstance(routes, list) and isinstance(routes[0], dict)
            routes[0].update(
                {
                    "route_kind": "source_component",
                    "semantic_relation": "equivalent_source_component",
                    "source_component_anchor_sha256": anchor_sha256,
                }
            )
            entries[row_name] = entry
            component_statement_by_row[row_name] = component_statement
            rows.append(
                RowSnapshot(
                    name=row_name,
                    lean_statement=lean,
                    paper_statement=parent_statement,
                    tex_statement=component_statement,
                    manifest=copy.deepcopy(self.current_manifest),
                )
            )

        validator = mock.Mock(return_value="")
        bootstrapped, decisions, _bindings = migrate_statement_items(
            entries,
            current_rows=rows,
            current_inventory=inventory,
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            bootstrap_current=True,
            validate_entry=validator,
        )

        self.assertEqual(validator.call_count, 2)
        parent_digest = review_dashboard.statement_digest(parent_statement)
        names = list(entries)
        lean_by_row = {row.name: row.lean_statement for row in rows}
        for name in names:
            with self.subTest(name=name):
                self.assertTrue(decisions[name]["accepted"])
                result = bootstrapped[name]
                metadata = result["semantic_reuse_v1"]
                self.assertEqual(
                    metadata["paper_statement_sha256"],
                    result["paper_statement_sha256"],
                )
                self.assertNotEqual(metadata["paper_statement_sha256"], parent_digest)
                pin, error = _reuse_pin_from_embedded(
                    result, result["source_routes"]
                )
                self.assertIsNotNone(pin)
                self.assertEqual(error, "")
                normalized_judgment = copy.deepcopy(result)
                normalized_judgment["source_route_error"] = ""
                normalized_judgment["source_route_validation_performed"] = True
                self.assertFalse(
                    review_dashboard._llm_statement_judgment_is_stale(
                        normalized_judgment,
                        signature_sha256=str(result["lean_signature_sha256"]),
                        lean_statement=lean_by_row[name],
                        paper_statement=parent_statement,
                        agent_statement=component_statement_by_row[name],
                    )
                )

        renamed_rows = [
            RowSnapshot(
                name=f"renamed-{index}",
                lean_statement=(
                    f"abbrev renamed_component_surface_{index} : P := by exact proof"
                ),
                paper_statement=parent_statement,
                tex_statement=row.tex_statement,
                manifest=copy.deepcopy(row.manifest),
            )
            for index, row in enumerate(rows, start=1)
        ]
        reused, reuse_decisions, _reuse_bindings = migrate_statement_items(
            bootstrapped,
            current_rows=renamed_rows,
            current_inventory=inventory,
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            validate_entry=validator,
        )
        for name in names:
            with self.subTest(second_pass=name):
                self.assertTrue(reuse_decisions[name]["accepted"])
                metadata = reused[name]["semantic_reuse_v1"]
                self.assertEqual(
                    metadata["paper_statement_sha256"],
                    reused[name]["paper_statement_sha256"],
                )
                self.assertNotEqual(
                    metadata["paper_statement_sha256"], parent_digest
                )
                self.assertTrue(
                    reuse_decisions[name]["current_row"].startswith("renamed-")
                )

        aggregate_navigation = copy.deepcopy(bootstrapped[names[0]])
        aggregate_navigation["source_routes"].append(
            copy.deepcopy(bootstrapped[names[1]]["source_routes"][0])
        )
        aggregate_navigation["source_route_error"] = ""
        aggregate_navigation["source_route_validation_performed"] = True
        self.assertEqual(
            review_dashboard._validated_unique_source_component_target_sha256(
                aggregate_navigation
            ),
            aggregate_navigation["paper_statement_sha256"],
        )
        aggregate_navigation["source_routes"].append(
            copy.deepcopy(aggregate_navigation["source_routes"][0])
        )
        self.assertEqual(
            review_dashboard._validated_unique_source_component_target_sha256(
                aggregate_navigation
            ),
            "",
        )

        first_loaded = copy.deepcopy(bootstrapped[names[0]])
        first_loaded["source_route_error"] = ""
        self.assertTrue(
            review_dashboard._llm_statement_judgment_is_stale(
                first_loaded,
                signature_sha256=str(first_loaded["lean_signature_sha256"]),
                lean_statement=lean_by_row[names[0]],
                paper_statement=parent_statement,
                agent_statement=component_statement_by_row[names[0]],
            )
        )
        first_loaded["source_route_validation_performed"] = True
        resolved_key, resolved, ambiguous = (
            review_dashboard._current_semantic_statement_judgment(
                signature_sha256=str(first_loaded["lean_signature_sha256"]),
                lean_statement=lean_by_row[names[0]],
                paper_statement=parent_statement,
                agent_statement=component_statement_by_row[names[0]],
                judgments={"renamed-storage-navigation": first_loaded},
            )
        )
        self.assertEqual(resolved_key, "renamed-storage-navigation")
        self.assertIs(resolved, first_loaded)
        self.assertFalse(ambiguous)

        first = copy.deepcopy(bootstrapped[names[0]])
        first_metadata = copy.deepcopy(first["semantic_reuse_v1"])
        second_metadata = bootstrapped[names[1]]["semantic_reuse_v1"]
        paper_cross_binding = copy.deepcopy(first_metadata)
        paper_cross_binding["paper_statement_sha256"] = second_metadata[
            "paper_statement_sha256"
        ]
        first["semantic_reuse_v1"] = paper_cross_binding
        pin, error = _reuse_pin_from_embedded(first, first["source_routes"])
        self.assertIsNone(pin)
        self.assertIn("paper statement pin", error)

        # Even with the first entry's exact text/Lean pins, the second
        # component's route identity cannot certify the first route.
        route_cross_binding = copy.deepcopy(first_metadata)
        route_cross_binding["source_routes"] = copy.deepcopy(
            second_metadata["source_routes"]
        )
        first["semantic_reuse_v1"] = route_cross_binding
        pin, error = _reuse_pin_from_embedded(first, first["source_routes"])
        self.assertIsNone(pin)
        self.assertIn("source route semantic identity", error)

    def test_bootstrap_ordinary_route_retains_dashboard_paper_statement_pin(self) -> None:
        entry = statement_entry(
            self.current_manifest,
            self.current_item,
            source_key="ordinary-source",
        )
        entry["paper_statement_sha256"] = "f" * 64
        output, decisions, _bindings = migrate_statement_items(
            {"ordinary-row": entry},
            current_rows=[
                RowSnapshot(
                    name="ordinary-row",
                    lean_statement=self.lean,
                    paper_statement=self.current_row.paper_statement,
                    tex_statement=self.current_row.tex_statement,
                    manifest=copy.deepcopy(self.current_manifest),
                )
            ],
            current_inventory={"ordinary-source": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            bootstrap_current=True,
            validate_entry=lambda _entry, _row, _inventory: "",
        )

        self.assertTrue(decisions["ordinary-row"]["accepted"])
        self.assertEqual(
            output["ordinary-row"]["semantic_reuse_v1"][
                "paper_statement_sha256"
            ],
            review_dashboard.statement_digest(self.current_row.paper_statement),
        )

    def test_partial_migration_does_not_refresh_aggregate_coverage_receipt(self) -> None:
        _target, target_digest = source_target(self.current_item)
        statement_sidecar = {
            "items": {
                "current_statement_navigation": statement_entry(
                    self.current_manifest,
                    self.current_item,
                    source_key="current_source_navigation",
                )
            }
        }
        coverage_sidecar = {
            "paper_statement_inventory_sha256": "c" * 64,
            "review_surface_sha256": "d" * 64,
            "items": {
                "current_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["current_navigation_only"],
                    "review_row_signature_sha256": {
                        "current_navigation_only": self.current_manifest["sha256"]
                    },
                }
            },
        }
        second_item = source_item("A second current source result.")

        _statement, coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={
                "current_source_navigation": self.current_item,
                "second_current_source": second_item,
            },
            current_coverage_inventory={
                "current_source_navigation": self.current_item,
                "second_current_source": second_item,
            },
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_map={
                "source_artifact_path": "fixture-source.txt",
                "source_artifact_sha256": "b" * 64,
            },
            current_review_surface_sha256="a" * 64,
            bootstrap_current=True,
            validate_statement=lambda _entry, _row, _inventory: "",
        )

        self.assertFalse(report["aggregate_coverage_receipt_refreshed"])
        self.assertEqual(coverage["paper_statement_inventory_sha256"], "c" * 64)
        self.assertEqual(coverage["review_surface_sha256"], "d" * 64)

    def test_authenticated_canonical_exclusion_is_removed_atomically(self) -> None:
        excluded_item = source_item("An unnumbered deep-paper observation.")
        _selected_statement, selected_digest = source_target(self.current_item)
        _excluded_statement, excluded_digest = source_target(excluded_item)
        statement_sidecar = {
            "items": {
                "old_statement_navigation": statement_entry(
                    self.legacy_manifest,
                    self.old_item,
                    source_key="old_selected_source",
                )
            }
        }
        coverage_sidecar = {
            "items": {
                "old_selected_source": {
                    "coverage": "covered",
                    "statement_sha256": selected_digest,
                    "review_rows": ["old_dashboard_navigation"],
                    "review_row_signature_sha256": {
                        "old_dashboard_navigation": self.legacy_manifest["sha256"]
                    },
                },
                "old_excluded_source": {
                    "coverage": "covered",
                    "statement_sha256": excluded_digest,
                    "review_rows": ["old_excluded_row"],
                    "review_row_signature_sha256": {
                        "old_excluded_row": self.legacy_manifest["sha256"]
                    },
                },
            }
        }
        source_map = {
            "source_artifact_path": "fixture-source.txt",
            "source_artifact_sha256": "b" * 64,
        }

        _statement, coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={
                "current_selected_source": self.current_item,
                "current_excluded_source": excluded_item,
            },
            current_coverage_inventory={
                "current_selected_source": self.current_item,
            },
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_map=source_map,
            current_review_surface_sha256="a" * 64,
            previous_inventory={
                "old_selected_source": self.old_item,
                "old_excluded_source": excluded_item,
            },
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_statement=None,
        )

        exclusion = report["coverage"]["old_excluded_source"]
        self.assertTrue(exclusion["accepted"])
        self.assertTrue(exclusion["semantic_exclusion"])
        self.assertEqual(
            exclusion["disposition"], REUSE.COVERAGE_SEMANTIC_EXCLUSION
        )
        self.assertEqual(exclusion["current_source_item"], "current_excluded_source")
        self.assertEqual(
            set(coverage["items"]), {"current_selected_source"}
        )
        self.assertEqual(report["authenticated_coverage_exclusion_count"], 1)
        self.assertTrue(report["aggregate_coverage_receipt_refreshed"])
        self.assertEqual(
            coverage["paper_statement_inventory_sha256"],
            review_dashboard.paper_coverage_inventory_digest(
                {"current_selected_source": self.current_item},
                mode="named_theoretical_statements",
                statement_map_payload=source_map,
            ),
        )

    def test_unauthenticated_canonical_exclusions_remain_fail_closed(self) -> None:
        excluded_item = source_item("An unnumbered deep-paper observation.")
        changed_excluded = source_item("A changed deep-paper observation.")
        _selected_statement, selected_digest = source_target(self.current_item)
        _excluded_statement, excluded_digest = source_target(excluded_item)

        def run_case(
            *,
            current_excluded_items: dict[str, dict[str, object]],
            prior_has_excluded_item: bool,
        ) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
            statement_sidecar = {
                "items": {
                    "old_statement_navigation": statement_entry(
                        self.legacy_manifest,
                        self.old_item,
                        source_key="old_selected_source",
                    )
                }
            }
            excluded_entry = {
                "coverage": "covered",
                "statement_sha256": excluded_digest,
                "review_rows": ["old_excluded_row"],
                "review_row_signature_sha256": {
                    "old_excluded_row": self.legacy_manifest["sha256"]
                },
            }
            coverage_sidecar = {
                "items": {
                    "old_selected_source": {
                        "coverage": "covered",
                        "statement_sha256": selected_digest,
                        "review_rows": ["old_dashboard_navigation"],
                        "review_row_signature_sha256": {
                            "old_dashboard_navigation": self.legacy_manifest["sha256"]
                        },
                    },
                    "old_excluded_source": excluded_entry,
                }
            }
            previous_inventory = {"old_selected_source": self.old_item}
            if prior_has_excluded_item:
                previous_inventory["old_excluded_source"] = excluded_item
            _statement, coverage, report = migrate_sidecars(
                statement_sidecar,
                coverage_sidecar,
                current_rows=[self.current_row],
                current_inventory={
                    "current_selected_source": self.current_item,
                    **current_excluded_items,
                },
                current_coverage_inventory={
                    "current_selected_source": self.current_item,
                },
                current_mode="named_theoretical_statements",
                current_anchor_errors={},
                current_source_map={
                    "source_artifact_path": "fixture-source.txt",
                    "source_artifact_sha256": "b" * 64,
                },
                current_review_surface_sha256="a" * 64,
                previous_inventory=previous_inventory,
                previous_mode="named_theoretical_statements",
                previous_rows=[self.old_row],
                bootstrap_current=True,
                validate_statement=None,
            )
            return coverage_sidecar, coverage, report

        cases = {
            "missing authenticated pin": (
                {"old_excluded_source": excluded_item},
                False,
            ),
            "missing current identity": ({"current_changed": changed_excluded}, True),
            "ambiguous current identity": (
                {
                    "current_excluded_one": excluded_item,
                    "current_excluded_two": copy.deepcopy(excluded_item),
                },
                True,
            ),
        }
        for label, (current_items, has_prior) in cases.items():
            with self.subTest(case=label):
                original, coverage, report = run_case(
                    current_excluded_items=current_items,
                    prior_has_excluded_item=has_prior,
                )
                decision = report["coverage"]["old_excluded_source"]
                self.assertFalse(decision["accepted"])
                self.assertEqual(
                    coverage["items"]["old_excluded_source"],
                    original["items"]["old_excluded_source"],
                )
                self.assertEqual(report["authenticated_coverage_exclusion_count"], 0)
                self.assertFalse(report["aggregate_coverage_receipt_refreshed"])

    def test_excluded_source_items_do_not_block_aggregate_coverage_refresh(self) -> None:
        support_item = source_item("A distinct statement row holds.")
        selected_item = copy.deepcopy(self.current_item)
        excluded_duplicate = copy.deepcopy(selected_item)
        statement, _statement_digest = source_target(support_item)
        old_support_row = RowSnapshot(
            name="old_support_row",
            lean_statement=self.lean,
            paper_statement=statement,
            tex_statement=statement,
            manifest=self.legacy_manifest,
        )
        current_support_row = RowSnapshot(
            name="current_support_row",
            lean_statement=self.lean,
            paper_statement=statement,
            tex_statement=statement,
            manifest=self.current_manifest,
        )
        _target, selected_digest = source_target(selected_item)
        statement_sidecar = {
            "items": {
                "old_statement_navigation": statement_entry(
                    self.legacy_manifest,
                    support_item,
                    source_key="old_support_source",
                )
            }
        }
        coverage_sidecar = {
            "items": {
                "old_selected_source": {
                    "coverage": "covered",
                    "statement_sha256": selected_digest,
                    "review_rows": ["old_support_row"],
                    "review_row_signature_sha256": {
                        "old_support_row": self.legacy_manifest["sha256"]
                    },
                }
            }
        }
        source_map = {
            "source_artifact_path": "fixture-source.txt",
            "source_artifact_sha256": "b" * 64,
        }

        _statement, coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[current_support_row],
            current_inventory={
                "current_support_source": support_item,
                "current_selected_source": selected_item,
                # This semantically identical item is outside normal coverage.
                "excluded_deep_source": excluded_duplicate,
            },
            current_coverage_inventory={
                "current_selected_source": selected_item,
            },
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_map=source_map,
            current_review_surface_sha256="a" * 64,
            previous_inventory={
                "old_support_source": support_item,
                "old_selected_source": selected_item,
            },
            previous_mode="named_theoretical_statements",
            previous_rows=[old_support_row],
            validate_statement=None,
        )

        self.assertTrue(report["statement"]["old_statement_navigation"]["accepted"])
        self.assertTrue(report["coverage"]["old_selected_source"]["accepted"])
        self.assertTrue(report["aggregate_coverage_receipt_refreshed"])
        self.assertEqual(
            coverage["paper_statement_inventory_sha256"],
            review_dashboard.paper_coverage_inventory_digest(
                {"current_selected_source": selected_item},
                mode="named_theoretical_statements",
                statement_map_payload=source_map,
            ),
        )

    def test_selected_coverage_inventory_projection_mismatch_fails_closed(self) -> None:
        _target, target_digest = source_target(self.current_item)
        statement_sidecar = {
            "items": {
                "current_statement_navigation": statement_entry(
                    self.current_manifest,
                    self.current_item,
                    source_key="current_source_navigation",
                )
            }
        }
        coverage_sidecar = {
            "items": {
                "current_source_navigation": {
                    "coverage": "covered",
                    "statement_sha256": target_digest,
                    "review_rows": ["renamed_dashboard_navigation"],
                    "review_row_signature_sha256": {
                        "renamed_dashboard_navigation": self.current_manifest["sha256"]
                    },
                }
            }
        }
        mismatched = copy.deepcopy(self.current_item)
        mismatched["source_note"] = "A different selected-inventory payload."

        statement, coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[self.current_row],
            current_inventory={"current_source_navigation": self.current_item},
            current_coverage_inventory={"current_source_navigation": mismatched},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            current_source_map={
                "source_artifact_path": "fixture-source.txt",
                "source_artifact_sha256": "b" * 64,
            },
            current_review_surface_sha256="a" * 64,
            bootstrap_current=True,
            validate_statement=lambda _entry, _row, _inventory: "",
        )

        self.assertIn("not an exact projection", report["global_error"])
        self.assertEqual(statement, statement_sidecar)
        self.assertEqual(coverage, coverage_sidecar)

    def test_canonical_coverage_selector_projection_is_source_inventory_bound(self) -> None:
        deep_item = source_item("An excluded deep-paper observation.")
        full_inventory = {
            "selected_source": self.current_item,
            "deep_source": deep_item,
        }
        canonical_full = copy.deepcopy(full_inventory)
        canonical_selected = {"selected_source": canonical_full["selected_source"]}
        with mock.patch.object(
            review_dashboard, "paper_source_map_structural_errors", return_value=[]
        ), mock.patch.object(
            review_dashboard,
            "paper_coverage_inventory",
            return_value=(
                canonical_full,
                canonical_selected,
                "named_theoretical_statements",
                "",
            ),
        ):
            projected, error = REUSE.canonical_coverage_inventory_projection(
                ROOT,
                current_inventory=full_inventory,
                current_mode="named_theoretical_statements",
            )

        self.assertEqual(error, "")
        self.assertEqual(set(projected), {"selected_source"})
        self.assertIs(projected["selected_source"], self.current_item)

        changed_canonical = copy.deepcopy(canonical_full)
        changed_canonical["selected_source"] = source_item(
            "A semantically changed selected result."
        )
        with mock.patch.object(
            review_dashboard, "paper_source_map_structural_errors", return_value=[]
        ), mock.patch.object(
            review_dashboard,
            "paper_coverage_inventory",
            return_value=(
                changed_canonical,
                {"selected_source": changed_canonical["selected_source"]},
                "named_theoretical_statements",
                "",
            ),
        ):
            projected, error = REUSE.canonical_coverage_inventory_projection(
                ROOT,
                current_inventory=full_inventory,
                current_mode="named_theoretical_statements",
            )

        self.assertEqual(projected, {})
        self.assertIn("semantic coverage target changed", error)

    def test_canonical_coverage_projection_rejects_structural_error_before_selection(
        self,
    ) -> None:
        selector = mock.Mock()
        with mock.patch.object(
            review_dashboard,
            "paper_source_map_structural_errors",
            return_value=["prose-definition reconciliation is malformed"],
        ), mock.patch.object(
            review_dashboard, "paper_coverage_inventory", selector
        ):
            projected, error = REUSE.canonical_coverage_inventory_projection(
                ROOT,
                current_inventory={"selected_source": self.current_item},
                current_mode="named_theoretical_statements",
            )

        self.assertEqual(projected, {})
        self.assertIn("before selection or exclusion pruning", error)
        selector.assert_not_called()

    def test_validated_empty_canonical_coverage_refreshes_atomically(self) -> None:
        source_map = {
            "source_artifact_path": "fixture-source.txt",
            "source_artifact_sha256": "b" * 64,
        }

        def run(validated: bool) -> tuple[dict[str, object], dict[str, object]]:
            _statement, coverage, report = migrate_sidecars(
                {"items": {}},
                {"items": {}, "paper_statement_inventory_sha256": "c" * 64},
                current_rows=[],
                current_inventory={},
                current_coverage_inventory={},
                current_mode="named_theoretical_statements",
                current_anchor_errors={},
                current_source_map=source_map,
                canonical_coverage_projection_validated=validated,
                current_review_surface_sha256="a" * 64,
            )
            return coverage, report

        unvalidated_coverage, unvalidated_report = run(False)
        self.assertFalse(unvalidated_report["aggregate_coverage_receipt_refreshed"])
        self.assertEqual(
            unvalidated_coverage["paper_statement_inventory_sha256"], "c" * 64
        )

        coverage, report = run(True)
        self.assertTrue(report["aggregate_coverage_receipt_refreshed"])
        self.assertEqual(coverage["items"], {})
        self.assertEqual(
            coverage["paper_statement_inventory_sha256"],
            review_dashboard.paper_coverage_inventory_digest(
                {},
                mode="named_theoretical_statements",
                statement_map_payload=source_map,
            ),
        )

    def test_rejects_changed_anchor_quote_even_when_names_and_statement_match(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        changed = source_item(quote="A changed anchored quote.")
        output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": changed},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertFalse(decisions["old_statement_navigation"]["accepted"])
        self.assertIn("source semantic/quote identity", decisions["old_statement_navigation"]["reason"])
        self.assertEqual(output["old_statement_navigation"], entry)

    def test_rejects_ambiguous_source_identity_instead_of_using_route_name(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={
                # The old route name deliberately coincides with one candidate.
                # A name-based fallback would select it; content identity is
                # duplicated, so the helper must reject.
                "old_source_navigation": copy.deepcopy(self.current_item),
                "different_navigation": copy.deepcopy(self.current_item),
            },
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertFalse(decisions["old_statement_navigation"]["accepted"])
        self.assertIn("missing or ambiguous", decisions["old_statement_navigation"]["reason"])

    def test_legacy_pin_allows_name_only_raw_lean_change(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        changed_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement="theorem renamed_exact_endpoint : P",
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=self.current_manifest,
        )
        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[changed_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertTrue(decisions["old_statement_navigation"]["accepted"])

    def test_allows_whitespace_only_raw_lean_change_after_semantic_match(self) -> None:
        """Raw pretty-printing is trace evidence, not semantic identity."""

        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        changed_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            # ``statement_digest`` normalizes this to the old text, while the
            # retained exact-byte trace below still records the new spelling.
            lean_statement="theorem   exact_endpoint : P",
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=self.current_manifest,
        )
        output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[changed_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertTrue(decisions["old_statement_navigation"]["accepted"])
        metadata = output["old_statement_navigation"]["semantic_reuse_v1"]
        self.assertEqual(
            metadata["raw_lean_statement_sha256"],
            changed_row.raw_lean_sha256,
        )

    def test_rejects_changed_atom_structure_despite_raw_statement_coincidence(self) -> None:
        entry = statement_entry(
            self.legacy_manifest, self.old_item, source_key="old_source_navigation"
        )
        changed_manifest = manifest(result="Q")
        changed_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=self.current_row.paper_statement,
            tex_statement=self.current_row.tex_statement,
            manifest=changed_manifest,
        )
        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[changed_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )

        self.assertFalse(decisions["old_statement_navigation"]["accepted"])
        self.assertIn("atom/ref/role structure", decisions["old_statement_navigation"]["reason"])

    def test_rejects_changed_corrected_target_approval_pin(self) -> None:
        old_item = source_item(
            statement="The archival endpoint holds.", corrected=True, approval_digest="a" * 64
        )
        current_item = source_item(
            statement="The archival endpoint holds.", corrected=True, approval_digest="d" * 64
        )
        corrected_statement, _digest = source_target(old_item)
        old_row = RowSnapshot(
            name="old_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=corrected_statement,
            tex_statement=corrected_statement,
            manifest=self.legacy_manifest,
        )
        current_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=corrected_statement,
            tex_statement=corrected_statement,
            manifest=self.current_manifest,
        )
        entry = statement_entry(
            self.legacy_manifest, old_item, source_key="old_source_navigation"
        )
        _output, decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[current_row],
            current_inventory={"new_source_navigation": current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[old_row],
            validate_entry=None,
        )

        self.assertFalse(decisions["old_statement_navigation"]["accepted"])
        self.assertIn("source semantic/quote identity", decisions["old_statement_navigation"]["reason"])

    def test_rejects_stale_corrected_target_coverage_pin(self) -> None:
        old_item = source_item(
            statement="The archival endpoint holds.", corrected=True, approval_digest="a" * 64
        )
        corrected_statement, corrected_digest = source_target(old_item)
        old_row = RowSnapshot(
            name="old_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=corrected_statement,
            tex_statement=corrected_statement,
            manifest=self.legacy_manifest,
        )
        current_row = RowSnapshot(
            name="renamed_dashboard_navigation",
            lean_statement=self.lean,
            paper_statement=corrected_statement,
            tex_statement=corrected_statement,
            manifest=self.current_manifest,
        )
        target = old_item["corrected_target"]
        assert isinstance(target, dict)
        approval = target["approval"]
        assert isinstance(approval, dict)
        statement_sidecar = {
            "items": {
                "old_statement_navigation": statement_entry(
                    self.legacy_manifest, old_item, source_key="old_source_navigation"
                )
            }
        }
        coverage_sidecar = {
            "items": {
                "old_source_navigation": {
                    "coverage": "covered_corrected_target",
                    "target_kind": "approved_corrected_target",
                    "statement_sha256": corrected_digest,
                    "archival_statement_sha256": old_item["statement_sha256"],
                    "corrected_target_sha256": target["corrected_target_sha256"],
                    "governing_defect_ids": ["source-defect-1"],
                    "archival_equivalence_claimed": False,
                    # This differs from the prior source target.  The reuse
                    # helper must reject it rather than overwrite the value.
                    "approval_artifact_sha256": "f" * 64,
                    "review_rows": ["unrelated_old_row_name"],
                    "review_row_signature_sha256": {
                        "unrelated_old_row_name": self.legacy_manifest["sha256"]
                    },
                }
            }
        }
        _statement, _coverage, report = migrate_sidecars(
            statement_sidecar,
            coverage_sidecar,
            current_rows=[current_row],
            current_inventory={"new_source_navigation": old_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[old_row],
            validate_statement=None,
        )

        self.assertTrue(report["statement"]["old_statement_navigation"]["accepted"])
        self.assertFalse(report["coverage"]["old_source_navigation"]["accepted"])
        self.assertIn(
            "approval_artifact_sha256",
            report["coverage"]["old_source_navigation"]["reason"],
        )

    def test_entry_local_reuse_rejects_protocol_only_drift(self) -> None:
        entry = statement_entry(
            self.legacy_manifest,
            self.old_item,
            source_key="old_source_navigation",
        )
        first, first_decisions, _bindings = migrate_statement_items(
            {"old_statement_navigation": entry},
            current_rows=[self.current_row],
            current_inventory={"new_source_navigation": self.current_item},
            current_mode="named_theoretical_statements",
            current_anchor_errors={},
            previous_inventory={"old_source_navigation": self.old_item},
            previous_mode="named_theoretical_statements",
            previous_rows=[self.old_row],
            validate_entry=None,
        )
        self.assertTrue(first_decisions["old_statement_navigation"]["accepted"])
        metadata = first["old_statement_navigation"]["semantic_reuse_v1"]
        self.assertRegex(
            str(metadata.get("formalization_review_protocol_sha256") or ""),
            r"^[0-9a-f]{64}$",
        )

        with mock.patch.object(
            REUSE,
            "formalization_protocol_receipt_matches",
            return_value=False,
        ):
            _second, second_decisions, _second_bindings = migrate_statement_items(
                first,
                current_rows=[self.current_row],
                current_inventory={"new_source_navigation": self.current_item},
                current_mode="named_theoretical_statements",
                current_anchor_errors={},
                validate_entry=None,
            )

        self.assertFalse(second_decisions["old_statement_navigation"]["accepted"])
        self.assertIn(
            "formalization protocol pin",
            second_decisions["old_statement_navigation"]["reason"],
        )


if __name__ == "__main__":
    unittest.main()
