#!/usr/bin/env python3
"""Focused tests for current manual source-record complement materialization."""

from __future__ import annotations

import copy
import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_current_revalidation as CURRENT  # noqa: E402
from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import audit_conclusion_provenance as PROVENANCE  # noqa: E402
from scripts import audit_repository as REPO  # noqa: E402
from scripts import formalization_protocol as PROTOCOL  # noqa: E402
from scripts import source_record_manual_complement as COMPLEMENT  # noqa: E402
from scripts import source_record_record_closure_completion as CLOSURE  # noqa: E402
from scripts import source_record_target_disposition as TARGET  # noqa: E402
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


PAPER = "FixturePaper"
PROMPT = CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION


def digest(char: str) -> str:
    return char * 64


def association(
    marker: str, *, nested: bool = False
) -> dict[str, object]:
    """Build a generated-schema-2 association without a name-based lookup."""

    signature = {
        "qualified_declaration": "Fixture.PaperInterface.endpoint",
        "elaborated_signature_sha256": digest(marker),
    }
    source_semantic = digest(chr(ord(marker) + 1))
    result: dict[str, object] = {
        "schema": 2,
        "reviewed_elaborated_signature_identity": signature,
    }
    if nested:
        result["source_item_semantic_sha256"] = [source_semantic]
    else:
        result["source_item_identities"] = [
            {"source_semantic_sha256": source_semantic}
        ]
    result["semantic_association_sha256"] = TARGET.semantic_association_record_digest(
        [source_semantic], signature
    )
    return result


def corrected_association_fixture() -> tuple[dict[str, object], dict[str, object], dict[str, str]]:
    """Return one current source-map item and its schema-2 raw association."""

    target: dict[str, object] = {
        "archival_equivalence_claimed": False,
        "governing_defect_ids": ["fixture-corrected-target"],
        "corrected_statement": "Fixture corrected source statement",
    }
    target["corrected_target_sha256"] = TARGET.corrected_target_record_digest(target)
    source_item: dict[str, object] = {
        "source_location": "source.txt:1-2",
        "coverage_status": "corrected_source_statement",
        "corrected_target": target,
    }
    source_semantic = TARGET.source_item_coverage_sha256(source_item, "")
    signature = {
        "qualified_declaration": "Fixture.PaperInterface.endpoint",
        "elaborated_signature_sha256": digest("a"),
    }
    source_key = "fixture_corrected_source"
    result: dict[str, object] = {
        "schema": 2,
        "source_item_identities": [
            {
                "source_key": source_key,
                "source_location": "source.txt:1-2",
                "source_map_item_sha256": TARGET.source_map_item_record_digest(source_item),
                "source_semantic_sha256": source_semantic,
            }
        ],
        "reviewed_elaborated_signature_identity": signature,
    }
    result["semantic_association_sha256"] = TARGET.semantic_association_record_digest(
        [source_semantic], signature
    )
    return result, source_item, {
        source_semantic: str(target["corrected_target_sha256"])
    }


def raw_item(key: str, *, semantic_tag: str) -> dict[str, object]:
    return {
        "judgment_key": key,
        "kind": "boundary_input",
        "expanded_input_type": "P",
        "expanded_lean_surface": {
            "input_type": "P",
            "result_type": semantic_tag,
        },
        "semantic_obligation_tag": semantic_tag,
        # This presentation-only spelling must not participate in historical
        # reuse. The complement has no historical matching route at all.
        "reviewed_declaration_identity": {
            "qualified_declaration": f"Fixture.PaperInterface.{key}",
            "declaration_sha256": digest("a"),
        },
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": "Fixture.PaperInterface.endpoint",
                "elaborated_signature_sha256": digest("b"),
            }
        ],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": digest("c"),
        "source_record_item_context_sha256": digest("d"),
        "source_record_item_sha256": digest("e"),
    }


def raw_audit(*items: dict[str, object]) -> dict[str, object]:
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "boundary_input_items": list(items),
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    stamp_source_record_audit_receipts(payload)
    return payload


def closure_candidate_raw_audit(
    *,
    ambiguous_parent: bool = False,
    aggregate_only_fields: bool = False,
    explicit_parent_route_field: bool = False,
) -> dict[str, object]:
    """Build a small direct-parent record closure with current item receipts."""

    declaration = "Fixture.PaperInterface.direct_model"
    declaration_identity = {
        "qualified_declaration": declaration,
        "declaration_sha256": digest("a"),
    }
    signature = {
        "qualified_declaration": declaration,
        "elaborated_signature_sha256": digest("b"),
    }
    source_semantic = digest("c")
    association: dict[str, object] = {
        "schema": 2,
        "association_origin": "explicit_source_map_direct_route",
        "role": "direct_source_route",
        "reviewed_declaration_identity": declaration_identity,
        "reviewed_elaborated_signature_identity": signature,
        "source_item_identities": [
            {
                "source_key": "fixture_source_model",
                "source_location": "source.txt:1-4",
                "source_map_item_sha256": digest("d"),
                "source_semantic_sha256": source_semantic,
            }
        ],
    }
    association["semantic_association_sha256"] = TARGET.semantic_association_record_digest(
        [source_semantic], signature
    )
    root = "Fixture.DirectSourceModel"
    field_specs = [
        (f"{root}.kernel", "Fixture.Kernel", digest("e"), digest("f")),
        (
            f"{root}.kernel_isMarkov",
            "Fixture.IsMarkov",
            digest("a"),
            digest("b"),
        ),
    ]
    fields: list[dict[str, object]] = []
    components: list[dict[str, object]] = []
    for slot, (key, field_type, structural_sha, component_sha) in enumerate(field_specs):
        item = raw_item(key, semantic_tag=f"field-{slot}")
        item.update(
            {
                "structure": root,
                "nested_structures": [],
                "type": field_type,
                "structural_type_sha256": structural_sha,
            }
        )
        if aggregate_only_fields:
            # Match generated recursive children that can only be bound by
            # their complete raw-audit/closure receipt, never by a reusable
            # narrow item digest.
            item["source_record_item_reuse_eligibility"] = {
                "eligible": False,
                "blockers": [
                    "no source-content semantic identity",
                    "no exact current elaborated review-route signature",
                ],
            }
            for field in (
                "reviewed_elaborated_signature_identities",
                "source_record_item_digest_schema",
                "source_record_item_semantic_id",
                "source_record_item_context_sha256",
                "source_record_item_sha256",
            ):
                item.pop(field)
        if explicit_parent_route_field and slot == 0:
            item[TARGET.RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD] = {
                "schema": 1,
                "inheritance_mode": "explicit_parent_route_and_field_scope",
                "source_item": "fixture_source_model",
                "source_locator": "source.txt:1-4",
                "convention_id": "fixture-convention",
                "convention_sha256": digest("9"),
                "permitted_classifications": ["approved_source_convention"],
                "field_scope_sha256": digest("8"),
            }
        fields.append(item)
        components.append(
            {
                "judgment_key": f"theorem-realization::field::{component_sha}",
                "source_judgment_key": key,
                "source_component_section": "recursive_field_items",
                "source_claim_component_sha256": component_sha,
                "structural_type_sha256": structural_sha,
            }
        )
    semantic_key = "semantic-model::fixture-direct-model"
    semantic = raw_item(semantic_key, semantic_tag="direct-model")
    semantic.update(
        {
            "kind": "semantic_model_comparison",
            "reviewed_declaration_identity": declaration_identity,
            "reviewed_elaborated_signature_identities": [signature],
            "source_statement_association": association,
            "record_input_bindings": [
                {"record_roots": [root], "binder_names": ["model"]}
            ],
            "dimensions": [{"id": "joint_law_and_state_evolution"}],
        }
    )
    semantic_items = [semantic]
    if ambiguous_parent:
        second = copy.deepcopy(semantic)
        second["judgment_key"] = "semantic-model::fixture-direct-model-other"
        second_identity = {
            "qualified_declaration": "Fixture.PaperInterface.other_direct_model",
            "declaration_sha256": digest("e"),
        }
        second_signature = {
            "qualified_declaration": "Fixture.PaperInterface.other_direct_model",
            "elaborated_signature_sha256": digest("f"),
        }
        second_association = copy.deepcopy(association)
        second_association["reviewed_declaration_identity"] = second_identity
        second_association["reviewed_elaborated_signature_identity"] = second_signature
        second_association["semantic_association_sha256"] = (
            TARGET.semantic_association_record_digest([source_semantic], second_signature)
        )
        second["reviewed_declaration_identity"] = second_identity
        second["reviewed_elaborated_signature_identities"] = [second_signature]
        second["source_statement_association"] = second_association
        semantic_items.append(second)
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "boundary_input_items": [],
        "semantic_model_items": semantic_items,
        "recursive_field_items": fields,
        "theorem_realization_component_items": components,
        "expected_field_judgment_keys": [spec[0] for spec in field_specs],
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    stamp_source_record_audit_receipts(payload)
    return payload


class ManualComplementTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        (self.paper_dir / "audit").mkdir(parents=True)
        self.raw = raw_audit(
            raw_item("current_overlay : P", semantic_tag="overlay"),
            raw_item("current_manual_a : P", semantic_tag="manual-a"),
            raw_item("current_manual_b : P", semantic_tag="manual-b"),
        )
        # Most tests exercise queue construction with intentionally
        # noncanonical in-memory fixtures. Preserve that focus while allowing
        # the public APIs to finalize real fallback calls below.
        self._real_fallback_finalization = (
            COMPLEMENT._finalize_manual_complement_write
        )

        def finalize_fixture_return(
            runtime: object | None,
            raw_audit: object,
            *,
            paper: str,
            paper_dir: Path,
        ) -> None:
            if runtime is not None:
                self._real_fallback_finalization(
                    runtime,
                    raw_audit,
                    paper=paper,
                    paper_dir=paper_dir,
                )

        self._fixture_return_finalization = patch.object(
            COMPLEMENT,
            "_finalize_manual_complement_write",
            side_effect=finalize_fixture_return,
        )
        self._fixture_return_finalization.start()
        self.addCleanup(self._fixture_return_finalization.stop)

    def test_raw_group_loader_forwards_paper_directory_to_current_gate(self) -> None:
        """Manual materialization cannot bypass a paper-local structural replay."""

        with patch.object(CURRENT, "_raw_audit_error", return_value="") as gate:
            groups = COMPLEMENT._raw_groups(
                self.raw, paper=PAPER, paper_dir=self.paper_dir
            )
        self.assertEqual(set(groups), set(CURRENT.generated_judgment_items(self.raw)))
        gate.assert_called_once_with(self.raw, paper=PAPER, paper_dir=self.paper_dir)

    def _overlays(self, *keys: str) -> dict[str, dict[str, dict[str, object]]]:
        return {
            "differential": {
                key: {"classification": "validated_source_assumption"}
                for key in keys
            },
            "semantic_rebind": {},
        }

    def _complete(self, template: dict[str, object]) -> dict[str, object]:
        completed = copy.deepcopy(template)
        completed.pop("non_evidence_scaffold")
        completed.pop("must_not_be_written_to_repository_sidecar")
        completed["reviewed_current_semantics"] = True
        completed["reviewer"] = "Fixture current semantic reviewer"
        completed["validated_at"] = "2026-07-28T00:00:00Z"
        records = completed["manual_current_groups"]
        assert isinstance(records, dict)
        for index, record in enumerate(records.values()):
            assert isinstance(record, dict)
            record["reviewed_current_semantics"] = True
            record["reviewer"] = "Fixture current semantic reviewer"
            record["validated_at"] = "2026-07-28T00:00:00Z"
            record["review_notes"] = "Reviewed against this current complete descriptor."
            record["response"] = {
                "classification": "validated_source_assumption",
                "reason": f"current manual review {index}",
                "source_location": "source.txt:1-2",
            }
        return completed

    def _template(self, raw: dict[str, object]) -> dict[str, object]:
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            return COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )

    def _canonical_strict_runtime_fixture(
        self,
        raw: dict[str, object],
        paper_dir: Path,
    ) -> tuple[object, type[object], type[object]]:
        """Build fakes for the one exact closeout transaction under test.

        ``build_paper_closeout_evidence_context`` owns the expensive external
        identity helper in production.  The fake therefore carries only the
        opaque result of that one transaction; the test asserts that later
        strict coverage and overlay replays use it rather than issuing another
        transaction or accepting serializable data.
        """

        identity_context = object()
        status_payload: dict[str, object] = {"status": "formalized"}
        statement_map: dict[str, object] = {"items": {}}

        class FakeEvidenceContext:
            administrative_projection_rebind_error = ""
            administrative_projection_rebind = None

            def __init__(self) -> None:
                self.source_record_identity_context = identity_context

        class FakeRunContext:
            issued_by_builder = True

            @classmethod
            def from_exact_evidence_context(
                cls,
                paper_id: str,
                folder: Path,
                *,
                evidence_context: object,
            ) -> "FakeRunContext":
                return cls(paper_id, folder, evidence_context=evidence_context)

            def __init__(
                self,
                paper_id: str,
                folder: Path,
                *,
                evidence_context: object,
            ) -> None:
                self.paper_id = paper_id
                self.folder = folder.resolve()
                self.evidence_context = evidence_context
                self.build_input_provider = None

            def current_source_record_audit(self) -> tuple[dict[str, object], str]:
                return raw, ""

            def exact_json_payload(self, path: Path) -> dict[str, object]:
                return status_payload if path.name == "status.json" else statement_map

            def paper_declaration_index(self) -> dict[str, list[object]]:
                return {}

            def current_strict_source_spec_correspondence_receipts(self) -> tuple[()]:
                return ()

            def current_strict_source_spec_correspondence_scope_keys(
                self,
            ) -> tuple[str, ...]:
                return ("strict-root",)

        return identity_context, FakeEvidenceContext, FakeRunContext

    def test_busy_authenticated_overlay_refuses_template_without_writing(self) -> None:
        """A transient identity gate cannot create a false all-manual worklist."""

        raw_path = self.paper_dir / "audit" / "source_record_audit.json"
        raw_path.write_text(
            json.dumps(self.raw, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        output_path = self.paper_dir / "audit" / "busy-template.json"
        stderr = io.StringIO()
        with (
            patch.object(
                COMPLEMENT,
                "_authenticated_overlay_items",
                side_effect=COMPLEMENT.SourceRecordManualComplementError(
                    "authenticated semantic_rebind overlay loader raised "
                    "SourceRecordSemanticRebindIdentityDeferred: "
                    "source-record identity revalidation deferred"
                ),
            ),
            patch.object(
                sys,
                "argv",
                [
                    "source_record_manual_complement.py",
                    "--root",
                    str(self.root),
                    "--paper",
                    PAPER,
                    "--write-template",
                    str(output_path),
                ],
            ),
            contextlib.redirect_stderr(stderr),
        ):
            result = COMPLEMENT.main()

        self.assertEqual(result, 1)
        self.assertFalse(output_path.exists())
        self.assertIn("identity revalidation deferred", stderr.getvalue())

    def test_template_uses_every_current_raw_group_not_historical_bucket_count(self) -> None:
        # The old selected-review artifact could have any number of historical
        # descriptor buckets. Only the loader's actual current output is
        # relevant to the manual complement.
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays("current_overlay : P"),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                self.raw, paper=PAPER, paper_dir=self.paper_dir
            )
        records = template["manual_current_groups"]
        assert isinstance(records, dict)
        self.assertEqual(
            set(records), {"current_manual_a : P", "current_manual_b : P"}
        )
        self.assertEqual(
            template["authenticated_overlay_current_keys"],
            {
                "differential": ["current_overlay : P"],
                "semantic_rebind": [],
            },
        )

    def test_schema2_rebind_omits_only_its_exact_current_groups(self) -> None:
        overlays = self._overlays()
        overlays["semantic_rebind"] = {
            "current_overlay : P": {
                "classification": "validated_source_assumption"
            }
        }
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=overlays,
        ):
            template = COMPLEMENT.manual_current_complement_template(
                self.raw, paper=PAPER, paper_dir=self.paper_dir
            )
        records = template["manual_current_groups"]
        assert isinstance(records, dict)
        self.assertEqual(
            set(records), {"current_manual_a : P", "current_manual_b : P"}
        )
        self.assertEqual(
            template["authenticated_overlay_current_keys"]["semantic_rebind"],
            ["current_overlay : P"],
        )

    def test_effective_overlay_rejects_cross_lane_duplicate(self) -> None:
        """A manual queue cannot silently select a response by lane order."""

        overlays = self._overlays()
        key = "current_overlay : P"
        overlays["differential"][key] = {"classification": "differential"}
        overlays["semantic_rebind"][key] = {"classification": "rebind"}

        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError,
            "authenticated overlay lanes overlap",
        ):
            COMPLEMENT._effective_overlay_items(overlays)

    def test_new_authenticated_lane_is_included_without_lane_policy(self) -> None:
        overlays = self._overlays()
        overlays["fixture_extra"] = {
            "current_overlay : P": {"classification": "fixture_extra"}
        }
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=overlays,
        ):
            template = COMPLEMENT.manual_current_complement_template(
                self.raw, paper=PAPER, paper_dir=self.paper_dir
            )
        records = template["manual_current_groups"]
        assert isinstance(records, dict)
        self.assertEqual(
            set(records), {"current_manual_a : P", "current_manual_b : P"}
        )
        self.assertEqual(
            template["authenticated_overlay_current_keys"]["fixture_extra"],
            ["current_overlay : P"],
        )

    def test_stale_fresh_template_cannot_guide_a_current_queue(self) -> None:
        stale_template = self._template(self.raw)
        current_raw = raw_audit(
            raw_item("current_overlay : P", semantic_tag="overlay-revised"),
            raw_item("current_manual_a : P", semantic_tag="manual-a"),
            raw_item("current_manual_b : P", semantic_tag="manual-b"),
        )
        self.assertNotEqual(
            stale_template["current_source_record_audit_sha256"],
            current_raw["source_record_audit_sha256"],
        )
        self.assertEqual(
            COMPLEMENT.current_manual_complement_queue_error(
                stale_template,
                current_raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
            ),
            "manual-complement template is not bound to the current raw digest",
        )

    def test_fresh_template_cannot_hide_a_new_exact_schema2_overlay(self) -> None:
        stale_template = self._template(self.raw)
        current_overlays = self._overlays()
        current_overlays["semantic_rebind"] = {
            "current_overlay : P": {
                "classification": "validated_source_assumption"
            }
        }
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=current_overlays,
        ):
            self.assertEqual(
                COMPLEMENT.current_manual_complement_queue_error(
                    stale_template,
                    self.raw,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                ),
                "manual-complement template does not equal the live current queue",
            )

    def test_strict_full_spec_runtime_coverage_removes_only_complete_raw_groups(
        self,
    ) -> None:
        """A strict receipt cannot erase an unrelated member sharing a key."""

        component_key = "strict component : P"
        semantic_key = "strict semantic parent"
        mixed_key = "strict route with extra member"
        manual_key = "ordinary formula-or-field group"
        component_item = raw_item(component_key, semantic_tag="strict-component")
        mixed_component_item = raw_item(mixed_key, semantic_tag="mixed-component")
        raw = raw_audit(
            component_item,
            mixed_component_item,
            raw_item(manual_key, semantic_tag="ordinary"),
        )
        raw["semantic_model_items"] = [
            raw_item(semantic_key, semantic_tag="strict-semantic"),
            raw_item(mixed_key, semantic_tag="extra-semantic-member"),
        ]
        raw["theorem_realization_component_items"] = [
            {
                "source_claim_component_role": "material",
                "source_judgment_key": component_key,
                "source_component_section": "boundary_input_items",
                "source_record_item_sha256": component_item[
                    "source_record_item_sha256"
                ],
            },
            {
                "source_claim_component_role": "material",
                "source_judgment_key": mixed_key,
                "source_component_section": "boundary_input_items",
                "source_record_item_sha256": mixed_component_item[
                    "source_record_item_sha256"
                ],
            },
        ]
        stamp_source_record_audit_receipts(raw)
        coverage = COMPLEMENT._StrictV11FullSpecRuntimeCoverage(
            component_judgment_keys=frozenset({component_key, mixed_key}),
            semantic_model_judgment_keys=frozenset({semantic_key, mixed_key}),
        )

        with (
            patch.object(
                COMPLEMENT,
                "_authenticated_overlay_items",
                return_value=self._overlays(),
            ),
            patch.object(
                COMPLEMENT,
                "_strict_v11_full_spec_runtime_coverage",
                return_value=coverage,
            ),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            completed = self._complete(template)
            stale_coverage_error = COMPLEMENT._template_error(
                completed,
                raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
                strict_full_spec_coverage=(
                    COMPLEMENT._StrictV11FullSpecRuntimeCoverage()
                ),
            )

        records = template["manual_current_groups"]
        assert isinstance(records, dict)
        self.assertEqual(set(records), {mixed_key, manual_key})
        self.assertEqual(
            template[COMPLEMENT.STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD],
            {
                "component_judgment_keys": [component_key],
                "semantic_model_judgment_keys": [semantic_key],
            },
        )
        # The underlying generated ledger remains whole; strict runtime
        # coverage changes only the manual-complement queue.
        self.assertEqual(
            template["generated_judgment_keys_sha256"],
            CURRENT.generated_judgment_keys_sha256(raw),
        )
        self.assertEqual(
            template["generated_judgment_surface_sha256"],
            CURRENT.generated_judgment_surface_sha256(raw),
        )
        self.assertIn("stale strict full-Spec runtime coverage ledger", stale_coverage_error)

    def test_strict_full_spec_runtime_coverage_rejects_unknown_raw_group_key(self) -> None:
        coverage = COMPLEMENT._StrictV11FullSpecRuntimeCoverage(
            component_judgment_keys=frozenset({"not a current generated group"})
        )
        with (
            patch.object(
                COMPLEMENT,
                "_authenticated_overlay_items",
                return_value=self._overlays(),
            ),
            patch.object(
                COMPLEMENT,
                "_strict_v11_full_spec_runtime_coverage",
                return_value=coverage,
            ),
        ):
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "strict full-Spec runtime coverage contains keys absent",
            ):
                COMPLEMENT.manual_current_complement_template(
                    self.raw, paper=PAPER, paper_dir=self.paper_dir
                )

    def test_strict_component_mirror_join_requires_unique_association_and_type(
        self,
    ) -> None:
        """A digestless mirror may join once, never cover a duplicate member."""

        strict_key = "strict mirror source-record key"
        association_digest = digest("a")
        structural_type = digest("b")
        strict_item = raw_item(strict_key, semantic_tag="strict-mirror")
        strict_item["source_contract_association"] = {
            "association_sha256": association_digest
        }
        strict_item["structural_type_sha256"] = structural_type
        ordinary = raw_item("ordinary remaining group", semantic_tag="ordinary")
        raw = raw_audit(strict_item, ordinary)
        raw["theorem_realization_component_items"] = [
            {
                "source_claim_component_role": "material",
                "source_judgment_key": strict_key,
                # This is intentionally a different generator section and
                # has no item digest, as with a canonical nonreusable mirror.
                "source_component_section": "theorem_facing_input_items",
                "source_contract_association": {
                    "association_sha256": association_digest
                },
                "source_claim_component_structural_type_sha256": structural_type,
            }
        ]
        stamp_source_record_audit_receipts(raw)
        coverage = COMPLEMENT._StrictV11FullSpecRuntimeCoverage(
            component_judgment_keys=frozenset({strict_key})
        )
        with (
            patch.object(
                COMPLEMENT,
                "_authenticated_overlay_items",
                return_value=self._overlays(),
            ),
            patch.object(
                COMPLEMENT,
                "_strict_v11_full_spec_runtime_coverage",
                return_value=coverage,
            ),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
        records = template["manual_current_groups"]
        assert isinstance(records, dict)
        self.assertEqual(set(records), {"ordinary remaining group"})

        duplicate_raw = copy.deepcopy(raw)
        duplicate_item = copy.deepcopy(strict_item)
        duplicate_raw["boundary_input_items"] = [
            strict_item,
            duplicate_item,
            ordinary,
        ]
        stamp_source_record_audit_receipts(duplicate_raw)
        with (
            patch.object(
                COMPLEMENT,
                "_authenticated_overlay_items",
                return_value=self._overlays(),
            ),
            patch.object(
                COMPLEMENT,
                "_strict_v11_full_spec_runtime_coverage",
                return_value=coverage,
            ),
        ):
            duplicate_template = COMPLEMENT.manual_current_complement_template(
                duplicate_raw, paper=PAPER, paper_dir=self.paper_dir
            )
        duplicate_records = duplicate_template["manual_current_groups"]
        assert isinstance(duplicate_records, dict)
        self.assertIn(strict_key, duplicate_records)
        self.assertEqual(
            duplicate_template[
                COMPLEMENT.STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD
            ]["component_judgment_keys"],
            [],
        )

    def test_runtime_coverage_keeps_valid_subset_despite_unrelated_contract_findings(
        self,
    ) -> None:
        """Receipt minting is best-effort; selectors remain the only credit path."""

        raw = raw_audit(raw_item("strict component", semantic_tag="component"))
        raw["semantic_model_items"] = [
            raw_item("strict semantic", semantic_tag="semantic")
        ]
        stamp_source_record_audit_receipts(raw)
        strict_papers = self.root / "strict-papers"
        paper_dir = strict_papers / PAPER
        paper_dir.mkdir(parents=True)
        status_payload: dict[str, object] = {"status": "formalized"}
        statement_map: dict[str, object] = {"items": {}}

        class FakeEvidenceContext:
            administrative_projection_rebind_error = ""
            administrative_projection_rebind = None

        class FakeRunContext:
            @classmethod
            def from_exact_evidence_context(
                cls,
                paper_id: str,
                folder: Path,
                *,
                evidence_context: object,
            ) -> "FakeRunContext":
                """Model the production factory without minting real evidence."""

                return cls(
                    paper_id,
                    folder,
                    evidence_context=evidence_context,
                )

            def __init__(
                self,
                paper_id: str,
                folder: Path,
                *,
                evidence_context: object | None = None,
            ) -> None:
                self.paper_id = paper_id
                self.folder = folder.resolve()
                self.evidence_context = evidence_context
                self.build_input_provider = None

            def current_source_record_audit(self) -> tuple[dict[str, object], str]:
                return raw, ""

            def exact_json_payload(self, path: Path) -> dict[str, object]:
                return status_payload if path.name == "status.json" else statement_map

            def paper_declaration_index(self) -> dict[str, list[object]]:
                return {}

            def current_strict_source_spec_correspondence_receipts(self) -> tuple[()]:
                return ()

            def current_strict_source_spec_correspondence_scope_keys(self) -> tuple[str, ...]:
                return ("strict-root",)

        unrelated = [
            REPO.Finding(
                "ERROR",
                paper_dir / "audit" / "paper_statement_map.json",
                "unrelated non-strict formula contract finding",
            )
        ]
        evidence = FakeEvidenceContext()
        common_patches = (
            patch.object(REPO, "PAPERS", strict_papers),
            patch.object(
                REPO,
                "build_paper_closeout_evidence_context",
                return_value=evidence,
            ),
            patch.object(REPO, "PaperCloseoutRunContext", FakeRunContext),
            patch.object(
                REPO,
                "paper_statement_map_semantic_contract_findings",
                return_value=unrelated,
            ),
            patch.object(
                REPO,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ),
        )
        with common_patches[0], common_patches[1], common_patches[2], common_patches[3], common_patches[4], patch.object(
            PROVENANCE,
            "current_strict_transparent_spec_full_surface_source_record_judgment_keys",
            return_value=frozenset({"strict component"}),
        ), patch.object(
            PROVENANCE,
            "current_strict_transparent_spec_semantic_parent_judgment_keys",
            return_value=frozenset({"strict semantic"}),
        ):
            coverage = REPO.current_strict_v11_full_spec_source_record_coverage(
                PAPER, paper_dir, raw
            )
        self.assertEqual(coverage.component_judgment_keys, {"strict component"})
        self.assertEqual(coverage.semantic_model_judgment_keys, {"strict semantic"})

        # The aggregate receipt alone binds the generated semantic surface;
        # it is not authorization to project this transaction's strict
        # coverage onto a caller-mutated raw object.
        caller_mutated = copy.deepcopy(raw)
        caller_mutated["unchecked_runtime_mutation"] = True
        self.assertEqual(
            caller_mutated["source_record_audit_sha256"],
            raw["source_record_audit_sha256"],
        )
        with common_patches[0], common_patches[1], common_patches[2], common_patches[3], common_patches[4], patch.object(
            PROVENANCE,
            "current_strict_transparent_spec_full_surface_source_record_judgment_keys",
            return_value=frozenset({"strict component"}),
        ), patch.object(
            PROVENANCE,
            "current_strict_transparent_spec_semantic_parent_judgment_keys",
            return_value=frozenset({"strict semantic"}),
        ):
            caller_mutated_coverage = (
                REPO.current_strict_v11_full_spec_source_record_coverage(
                    PAPER, paper_dir, caller_mutated
                )
            )
        self.assertEqual(
            caller_mutated_coverage,
            REPO.StrictV11FullSpecSourceRecordCoverage(),
        )

        with common_patches[0], common_patches[1], common_patches[2], common_patches[3], common_patches[4], patch.object(
            PROVENANCE,
            "current_strict_transparent_spec_full_surface_source_record_judgment_keys",
            return_value=frozenset(),
        ), patch.object(
            PROVENANCE,
            "current_strict_transparent_spec_semantic_parent_judgment_keys",
            return_value=frozenset(),
        ):
            missing_receipt_coverage = (
                REPO.current_strict_v11_full_spec_source_record_coverage(
                    PAPER, paper_dir, raw
                )
            )
        self.assertEqual(
            missing_receipt_coverage,
            REPO.StrictV11FullSpecSourceRecordCoverage(),
        )

    def test_canonical_runtime_shares_one_identity_transaction_through_materialization(
        self,
    ) -> None:
        """A live strict runtime is reused without becoming an artifact field."""

        raw = raw_audit(raw_item("runtime manual : P", semantic_tag="runtime"))
        raw["theorem_realization_component_items"] = []
        stamp_source_record_audit_receipts(raw)
        strict_papers = self.root / "strict-runtime-papers"
        paper_dir = strict_papers / PAPER
        (paper_dir / "audit").mkdir(parents=True)
        identity_context, FakeEvidenceContext, FakeRunContext = (
            self._canonical_strict_runtime_fixture(raw, paper_dir)
        )
        evidence_context = FakeEvidenceContext()

        with (
            patch.object(REPO, "PAPERS", strict_papers),
            patch.object(
                REPO,
                "build_paper_closeout_evidence_context",
                return_value=evidence_context,
            ) as identity_transaction,
            patch.object(REPO, "exact_evidence_run_context", return_value=True),
            patch.object(REPO, "PaperCloseoutRunContext", FakeRunContext),
            patch.object(
                REPO,
                "paper_statement_map_semantic_contract_findings",
                return_value=[],
            ),
            patch.object(
                REPO,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ) as direct_finalization,
            patch.object(
                PROVENANCE,
                "current_strict_transparent_spec_full_surface_source_record_judgment_keys",
                return_value=frozenset(),
            ),
            patch.object(
                PROVENANCE,
                "current_strict_transparent_spec_semantic_parent_judgment_keys",
                return_value=frozenset(),
            ),
            patch.object(
                COMPLEMENT,
                "_authenticated_overlay_items",
                return_value=self._overlays(),
            ) as overlays,
        ):
            runtime = REPO.prepare_current_strict_v11_full_spec_source_record_runtime(
                PAPER,
                paper_dir,
                raw,
            )
            self.assertIsNotNone(runtime)
            template = COMPLEMENT.manual_current_complement_template(
                raw,
                paper=PAPER,
                paper_dir=paper_dir,
                runtime=runtime,
            )
            result = COMPLEMENT.materialize_manual_current_complement(
                raw,
                self._complete(template),
                paper=PAPER,
                paper_dir=paper_dir,
                output_sidecar_path=paper_dir
                / "audit"
                / "source_record_match_llm.json",
                runtime=runtime,
            )

        # The closeout builder is where production runs the external identity
        # helper. Strict coverage, the template overlay replay, and both
        # materialization overlay replays must all consume the same capability.
        self.assertEqual(identity_transaction.call_count, 1)
        self.assertEqual(overlays.call_count, 3)
        self.assertEqual(direct_finalization.call_count, 2)
        for call in overlays.call_args_list:
            self.assertIs(
                call.kwargs["source_record_identity_context"], identity_context
            )

        # The capability is strictly in-memory queue plumbing. The existing
        # template and ordinary evidence schemas cannot serialize it.
        self.assertNotIn("runtime", template)
        self.assertNotIn("source_record_identity_context", template)
        self.assertNotIn("runtime", result)
        self.assertNotIn("source_record_identity_context", result)
        json.dumps(template, sort_keys=True)
        json.dumps(result, sort_keys=True)

    def test_cli_defers_runtime_finalization_to_one_write_boundary(self) -> None:
        """CLI output performs one final check after all queue work is complete."""

        raw_path = self.paper_dir / "audit" / "source_record_audit.json"
        raw_path.write_text(
            json.dumps(self.raw, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        runtime = object()
        template_path = self.paper_dir / "audit" / "fresh-template.json"
        with (
            patch.object(
                COMPLEMENT,
                "_prepare_manual_complement_runtime",
                return_value=runtime,
            ),
            patch.object(
                COMPLEMENT,
                "_manual_current_complement_template",
                return_value={"manual_current_groups": {}},
            ) as template_builder,
            patch.object(
                COMPLEMENT,
                "_finalize_manual_complement_write",
            ) as finalization,
            patch.object(
                sys,
                "argv",
                [
                    "source_record_manual_complement.py",
                    "--root",
                    str(self.root),
                    "--paper",
                    PAPER,
                    "--write-template",
                    str(template_path),
                ],
            ),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            self.assertEqual(COMPLEMENT.main(), 0)
        self.assertIs(
            template_builder.call_args.kwargs["_write_boundary_deferral"],
            COMPLEMENT._MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL,
        )
        self.assertEqual(finalization.call_args.args, (runtime, self.raw))
        self.assertEqual(
            finalization.call_args.kwargs,
            {"paper": PAPER, "paper_dir": self.paper_dir},
        )

        completed_path = self.paper_dir / "audit" / "completed-template.json"
        completed_path.write_text("{}\n", encoding="utf-8")
        sidecar_path = self.paper_dir / "audit" / "source_record_match_llm.json"
        with (
            patch.object(
                COMPLEMENT,
                "_prepare_manual_complement_runtime",
                return_value=runtime,
            ),
            patch.object(
                COMPLEMENT,
                "_materialize_manual_current_complement",
                return_value={"items": {}},
            ) as materializer,
            patch.object(
                COMPLEMENT,
                "_finalize_manual_complement_write",
            ) as finalization,
            patch.object(
                sys,
                "argv",
                [
                    "source_record_manual_complement.py",
                    "--root",
                    str(self.root),
                    "--paper",
                    PAPER,
                    "--completed-template",
                    str(completed_path),
                    "--out",
                    str(sidecar_path),
                    "--write",
                ],
            ),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            self.assertEqual(COMPLEMENT.main(), 0)
        self.assertIs(
            materializer.call_args.kwargs["_write_boundary_deferral"],
            COMPLEMENT._MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL,
        )
        self.assertEqual(finalization.call_args.args, (runtime, self.raw))
        self.assertEqual(
            finalization.call_args.kwargs,
            {"paper": PAPER, "paper_dir": self.paper_dir},
        )

    def test_combined_fresh_assembly_materializes_in_one_runtime_transaction(self) -> None:
        """The fast CLI path shares one strict runtime through its final write."""

        raw = copy.deepcopy(self.raw)
        raw["theorem_realization_component_items"] = []
        raw_path = self.paper_dir / "audit" / "source_record_audit.json"
        raw_path.write_text(
            json.dumps(raw, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        fresh_path = self.paper_dir / "audit" / "fresh-template.json"
        fragment_path = self.paper_dir / "audit" / "current-fragment.json"
        fresh_path.write_text("{}\n", encoding="utf-8")
        fragment_path.write_text("{}\n", encoding="utf-8")
        sidecar_path = self.paper_dir / "audit" / "source_record_match_llm.json"
        runtime = object()
        completed = {"manual_current_groups": {}}
        result = {"items": {}}

        with (
            patch.object(
                REPO,
                "prepare_current_strict_v11_full_spec_source_record_runtime",
                return_value=runtime,
            ) as strict_runtime_factory,
            patch.object(COMPLEMENT, "_fresh_template_error", return_value=""),
            patch.object(
                COMPLEMENT,
                "current_manual_complement_queue_error",
                return_value="",
            ) as queue_check,
            patch.object(
                COMPLEMENT,
                "assemble_fresh_manual_current_complement_template",
                return_value=completed,
            ) as assembler,
            patch.object(
                COMPLEMENT,
                "_materialize_manual_current_complement",
                return_value=result,
            ) as materializer,
            patch.object(
                COMPLEMENT,
                "_finalize_manual_complement_write",
            ) as finalization,
            patch.object(
                sys,
                "argv",
                [
                    "source_record_manual_complement.py",
                    "--root",
                    str(self.root),
                    "--paper",
                    PAPER,
                    "--assemble-fresh-template-and-materialize",
                    str(fresh_path),
                    "--review-fragment",
                    str(fragment_path),
                    "--completed-reviewer",
                    "Fixture reviewer",
                    "--completed-at",
                    "2026-08-15T00:00:00Z",
                    "--completed-review-notes",
                    "Reviewed against current descriptors and pins.",
                    "--out",
                    str(sidecar_path),
                    "--write",
                ],
            ),
            contextlib.redirect_stdout(io.StringIO()),
        ):
            self.assertEqual(COMPLEMENT.main(), 0)

        # The strict-runtime factory is the builder transaction. It runs once,
        # then every later stage receives the same opaque capability.
        strict_runtime_factory.assert_called_once_with(PAPER, self.paper_dir, raw)
        self.assertIs(queue_check.call_args.kwargs["runtime"], runtime)
        self.assertEqual(assembler.call_args.args[0], {})
        self.assertEqual(assembler.call_args.args[1], [{}])
        self.assertIs(materializer.call_args.kwargs["runtime"], runtime)
        self.assertIs(
            materializer.call_args.kwargs["_write_boundary_deferral"],
            COMPLEMENT._MANUAL_COMPLEMENT_WRITE_BOUNDARY_DEFERRAL,
        )
        self.assertEqual(finalization.call_count, 1)
        self.assertEqual(finalization.call_args.args, (runtime, raw))
        self.assertEqual(
            finalization.call_args.kwargs,
            {"paper": PAPER, "paper_dir": self.paper_dir},
        )
        self.assertEqual(json.loads(sidecar_path.read_text(encoding="utf-8")), result)

    def test_combined_fresh_assembly_refuses_noncanonical_or_stale_input(self) -> None:
        """The shortcut cannot turn arbitrary output or stale queue data into evidence."""

        fresh_path = self.paper_dir / "audit" / "fresh-template.json"
        fragment_path = self.paper_dir / "audit" / "current-fragment.json"
        other_output = self.paper_dir / "audit" / "other-output.json"
        runtime = object()
        base_argv = [
            "source_record_manual_complement.py",
            "--root",
            str(self.root),
            "--paper",
            PAPER,
            "--assemble-fresh-template-and-materialize",
            str(fresh_path),
            "--review-fragment",
            str(fragment_path),
            "--completed-reviewer",
            "Fixture reviewer",
            "--completed-at",
            "2026-08-15T00:00:00Z",
            "--completed-review-notes",
            "Reviewed against current descriptors and pins.",
        ]
        with (
            patch.object(COMPLEMENT, "_prepare_manual_complement_runtime") as factory,
            patch.object(sys, "argv", [*base_argv, "--out", str(other_output)]),
            contextlib.redirect_stderr(io.StringIO()) as stderr,
        ):
            self.assertEqual(COMPLEMENT.main(), 1)
        self.assertIn("canonical ordinary source-record sidecar", stderr.getvalue())
        factory.assert_not_called()

        raw_path = self.paper_dir / "audit" / "source_record_audit.json"
        raw_path.write_text(
            json.dumps(self.raw, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        fresh_path.write_text("{}\n", encoding="utf-8")
        fragment_path.write_text("{}\n", encoding="utf-8")
        canonical_path = self.paper_dir / "audit" / "source_record_match_llm.json"
        with (
            patch.object(
                COMPLEMENT,
                "_prepare_manual_complement_runtime",
                return_value=runtime,
            ),
            patch.object(COMPLEMENT, "_fresh_template_error", return_value=""),
            patch.object(
                COMPLEMENT,
                "current_manual_complement_queue_error",
                return_value="stale current descriptor/pin receipt",
            ),
            patch.object(
                COMPLEMENT,
                "_materialize_manual_current_complement",
            ) as materializer,
            patch.object(
                COMPLEMENT,
                "_write_current_manual_complement_output",
            ) as writer,
            patch.object(
                sys,
                "argv",
                [*base_argv, "--out", str(canonical_path), "--write"],
            ),
            contextlib.redirect_stderr(io.StringIO()) as stderr,
        ):
            self.assertEqual(COMPLEMENT.main(), 1)
        self.assertIn("stale current descriptor/pin receipt", stderr.getvalue())
        materializer.assert_not_called()
        writer.assert_not_called()

    def test_fallback_write_finalization_requires_current_raw_map_and_watch(self) -> None:
        """A runtime miss cannot turn the CLI's final gate into a no-op."""

        identity_context = object()
        with (
            patch.object(
                COMPLEMENT,
                "_finalize_manual_complement_write",
                self._real_fallback_finalization,
            ),
            patch.object(
                EVIDENCE,
                "prepare_current_source_record_identity_context",
                return_value=identity_context,
            ) as prepare,
            patch.object(
                EVIDENCE,
                "current_source_record_identity_context_error",
                return_value="source-record identity revalidation deferred: producer busy",
            ) as revalidate,
        ):
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "fallback currentness changed or could not be finalized",
            ):
                COMPLEMENT._finalize_manual_complement_write(
                    None,
                    self.raw,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                )
        prepare.assert_called_once_with(self.paper_dir, PAPER, self.raw)
        revalidate.assert_called_once_with(
            identity_context,
            paper_dir=self.paper_dir,
            paper=PAPER,
            current_raw_audit=self.raw,
        )

    def test_public_fallback_return_requires_current_raw_map_and_watch(self) -> None:
        """Direct materialization cannot turn a missing runtime into a no-op."""

        with patch.object(
            COMPLEMENT,
            "_finalize_manual_complement_write",
            self._real_fallback_finalization,
        ), patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ), patch.object(
            EVIDENCE,
            "prepare_current_source_record_identity_context",
            return_value=object(),
        ), patch.object(
            EVIDENCE,
            "current_source_record_identity_context_error",
            return_value="source-record identity revalidation deferred: producer busy",
        ):
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "fallback currentness changed or could not be finalized",
            ):
                COMPLEMENT.manual_current_complement_template(
                    self.raw,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                )

    def test_public_materializers_do_not_offer_finalization_opt_out(self) -> None:
        """Only the CLI's private helper may defer the write-boundary check."""

        with self.assertRaises(TypeError):
            COMPLEMENT.manual_current_complement_template(
                self.raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
                finalize_runtime=False,
            )
        with self.assertRaises(TypeError):
            COMPLEMENT.materialize_manual_current_complement(
                self.raw,
                {},
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir / "audit" / "output.json",
                finalize_runtime=False,
            )

    def test_strict_runtime_rejects_forged_stale_and_cross_paper_reuse(self) -> None:
        """A runtime capability cannot be replayed for another raw or paper."""

        raw = raw_audit(raw_item("runtime guard : P", semantic_tag="runtime"))
        raw["theorem_realization_component_items"] = []
        stamp_source_record_audit_receipts(raw)

        class DuckTypedCloseout:
            issued_by_builder = True

            def current_source_record_audit(self) -> tuple[dict[str, object], str]:
                return raw, ""

        forged_binding = REPO._CurrentStrictV11FullSpecRuntimeIssuerBinding()
        forged = REPO.CurrentStrictV11FullSpecSourceRecordRuntime(
            paper_id=PAPER,
            folder=self.paper_dir.resolve(),
            raw_payload_canonical_sha256=REPO._canonical_payload_sha256(raw),
            coverage=REPO.StrictV11FullSpecSourceRecordCoverage(
                component_judgment_keys=frozenset({"unearned strict coverage"})
            ),
            _closeout_context=DuckTypedCloseout(),
            _source_record_identity_context=object(),
            _issuer_binding=forged_binding,
        )
        forged_binding.runtime = forged
        forged_binding.closeout_context = forged._closeout_context
        self.assertFalse(forged.issued_by_factory)
        self.assertIsNone(
            REPO.current_strict_v11_full_spec_source_record_runtime_coverage(
                forged, PAPER, self.paper_dir, raw
            )
        )
        self.assertIsNone(
            REPO.current_strict_v11_full_spec_source_record_runtime_identity_context(
                forged, PAPER, self.paper_dir, raw
            )
        )

        strict_papers = self.root / "strict-runtime-guards"
        paper_dir = strict_papers / PAPER
        paper_dir.mkdir(parents=True)
        _identity_context, FakeEvidenceContext, FakeRunContext = (
            self._canonical_strict_runtime_fixture(raw, paper_dir)
        )

        with (
            patch.object(REPO, "PAPERS", strict_papers),
            patch.object(
                REPO,
                "build_paper_closeout_evidence_context",
                return_value=FakeEvidenceContext(),
            ),
            patch.object(REPO, "exact_evidence_run_context", return_value=True),
            patch.object(REPO, "PaperCloseoutRunContext", FakeRunContext),
            patch.object(
                REPO,
                "paper_statement_map_semantic_contract_findings",
                return_value=[],
            ),
            patch.object(
                REPO,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ),
            patch.object(
                PROVENANCE,
                "current_strict_transparent_spec_full_surface_source_record_judgment_keys",
                return_value=frozenset(),
            ),
            patch.object(
                PROVENANCE,
                "current_strict_transparent_spec_semantic_parent_judgment_keys",
                return_value=frozenset(),
            ),
        ):
            runtime = REPO.prepare_current_strict_v11_full_spec_source_record_runtime(
                PAPER,
                paper_dir,
                raw,
            )
            self.assertIsNotNone(runtime)
            archived_dir = self.root / "archived" / PAPER
            archived_dir.mkdir(parents=True)
            self.assertIsNone(
                REPO.prepare_current_strict_v11_full_spec_source_record_runtime(
                    PAPER,
                    archived_dir,
                    raw,
                )
            )
            self.assertIsNone(
                REPO.current_strict_v11_full_spec_source_record_runtime_identity_context(
                    object(), PAPER, paper_dir, raw
                )
            )
            self.assertIsNone(
                REPO.current_strict_v11_full_spec_source_record_runtime_identity_context(
                    runtime, "OtherPaper", paper_dir, raw
                )
            )
            stale = copy.deepcopy(raw)
            stale["unchecked_runtime_mutation"] = True
            self.assertIsNone(
                REPO.current_strict_v11_full_spec_source_record_runtime_coverage(
                    runtime, PAPER, paper_dir, stale
                )
            )
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "does not match the canonical current raw audit",
            ):
                COMPLEMENT.manual_current_complement_template(
                    raw,
                    paper=PAPER,
                    paper_dir=paper_dir,
                    runtime=object(),
                )

    def test_materialization_rejects_semantic_response_the_gate_would_reject(self) -> None:
        """A completed template cannot bypass the shared semantic evidence gate."""

        semantic = raw_item(
            "semantic-model::parameterized-law", semantic_tag="parameterized-law"
        )
        semantic.update(
            {
                "kind": "semantic_model_comparison",
                "dimensions": [
                    {
                        "id": "joint_law_and_state_evolution",
                        "detected_from_expanded_surface": True,
                        "requires_checked_bridge_when_detected": True,
                        "requires_distribution_parameterization_analysis_when_detected": True,
                    }
                ],
            }
        )
        raw = raw_audit()
        raw["semantic_model_items"] = [semantic]
        stamp_source_record_audit_receipts(raw)

        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            completed = self._complete(template)
            records = completed["manual_current_groups"]
            assert isinstance(records, dict)
            response = records["semantic-model::parameterized-law"]["response"]
            assert isinstance(response, dict)
            response["classification"] = "semantic_model_review"
            response["semantic_model_dimensions"] = {
                "joint_law_and_state_evolution": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.txt:1-2",
                    "semantic_comparison": "The source and Lean carrier use the same law.",
                    "lean_evidence": "A checked construction exposes the current law.",
                    "lean_bridge": "A checked bridge derives the current joint law.",
                }
            }
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "distribution_parameterization_analysis",
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    raw,
                    completed,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )

    def test_unique_direct_parent_closure_reduces_template_and_materializes_fields(
        self,
    ) -> None:
        raw = closure_candidate_raw_audit()
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            candidates = template["record_field_closure_completion_candidates"]
            self.assertIsInstance(candidates, list)
            self.assertEqual(len(candidates), 1)
            records = template["manual_current_groups"]
            assert isinstance(records, dict)
            self.assertEqual(set(records), {"semantic-model::fixture-direct-model"})
            parent = records["semantic-model::fixture-direct-model"]
            assert isinstance(parent, dict)
            requirements = parent["required_record_field_closure_attestations"]
            self.assertIsInstance(requirements, list)
            self.assertEqual(len(requirements), 1)

            completed = self._complete(template)
            parent = completed["manual_current_groups"][
                "semantic-model::fixture-direct-model"
            ]
            assert isinstance(parent, dict)
            response = parent["response"]
            assert isinstance(response, dict)
            response["classification"] = "semantic_model_review"
            candidate = candidates[0]
            assert isinstance(candidate, dict)
            response["semantic_model_dimensions"] = {
                "joint_law_and_state_evolution": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.txt:1-4",
                    "semantic_comparison": (
                        "The source model specifies the kernel and its Markov "
                        "property as one joint record closure."
                    ),
                    "lean_evidence": (
                        "The generated closure enumerates both component-bound "
                        "record fields."
                    ),
                }
            }
            response[CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD] = [
                {
                    "schema": CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_SCHEMA,
                    "closure_sha256": candidate["closure_sha256"],
                    "verdict": CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_VERDICT,
                    "source_location": "source.txt:1-4",
                    "closure_semantics": (
                        "The direct source model covers every generated field in "
                        "this kernel closure, not only the record root."
                    ),
                    "lean_evidence": (
                        "The parent declaration, signature, record binding, and "
                        "component identities are pinned in the closure descriptor."
                    ),
                }
            ]
            result = COMPLEMENT.materialize_manual_current_complement(
                raw,
                completed,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir
                / "audit"
                / "source_record_match_llm.json",
            )

        items = result["items"]
        assert isinstance(items, dict)
        self.assertEqual(len(items), 3)
        for field_key in (
            "Fixture.DirectSourceModel.kernel",
            "Fixture.DirectSourceModel.kernel_isMarkov",
        ):
            receipt = items[field_key][
                CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD
            ]
            assert isinstance(receipt, dict)
            self.assertEqual(receipt["closure_sha256"], candidate["closure_sha256"])
            self.assertNotIn("source_claim_semantic_contract", items[field_key])
        metadata = result["manual_current_complement"]
        assert isinstance(metadata, dict)
        self.assertEqual(metadata["record_field_closure_completion_count"], 1)
        self.assertEqual(metadata["record_field_closure_completion_field_count"], 2)

    def test_closure_materialization_allows_aggregate_only_children_with_exact_receipts(
        self,
    ) -> None:
        raw = closure_candidate_raw_audit(aggregate_only_fields=True)
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            candidates = template["record_field_closure_completion_candidates"]
            self.assertIsInstance(candidates, list)
            self.assertEqual(len(candidates), 1)
            completed = self._complete(template)
            parent = completed["manual_current_groups"][
                "semantic-model::fixture-direct-model"
            ]
            assert isinstance(parent, dict)
            response = parent["response"]
            assert isinstance(response, dict)
            response["classification"] = "semantic_model_review"
            candidate = candidates[0]
            assert isinstance(candidate, dict)
            response["semantic_model_dimensions"] = {
                "joint_law_and_state_evolution": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.txt:1-4",
                    "semantic_comparison": "The direct source model covers this record closure.",
                    "lean_evidence": "The generated field components are complete.",
                }
            }
            response[CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD] = [
                {
                    "schema": CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_SCHEMA,
                    "closure_sha256": candidate["closure_sha256"],
                    "verdict": CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_VERDICT,
                    "source_location": "source.txt:1-4",
                    "closure_semantics": "The direct source model covers every generated record field.",
                    "lean_evidence": "The current closure binds each component and structural type.",
                }
            ]
            result = COMPLEMENT.materialize_manual_current_complement(
                raw,
                completed,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir
                / "audit"
                / "source_record_match_llm.json",
            )

        items = result["items"]
        assert isinstance(items, dict)
        for field_key in (
            "Fixture.DirectSourceModel.kernel",
            "Fixture.DirectSourceModel.kernel_isMarkov",
        ):
            field_response = items[field_key]
            self.assertEqual(
                field_response["source_record_audit_sha256"],
                raw["source_record_audit_sha256"],
            )
            receipt = field_response[
                CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD
            ]
            assert isinstance(receipt, dict)
            self.assertEqual(receipt["closure_sha256"], candidate["closure_sha256"])
            self.assertNotIn("source_record_item_digest_schema", field_response)
            self.assertNotIn("source_record_item_sha256s", field_response)
            self.assertNotIn("source_record_item_sha256", field_response)

    def test_closure_compression_preserves_explicit_parent_route_classification_boundary(
        self,
    ) -> None:
        raw = closure_candidate_raw_audit(explicit_parent_route_field=True)
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )

        # One explicitly routed child makes the whole closure ineligible for
        # compression. Both children therefore remain ordinary review groups;
        # no synthesized semantic-model response can overwrite the generated
        # field route's permitted classification.
        self.assertEqual(
            template["record_field_closure_completion_candidates"], []
        )
        records = template["manual_current_groups"]
        assert isinstance(records, dict)
        self.assertIn("semantic-model::fixture-direct-model", records)
        self.assertIn("Fixture.DirectSourceModel.kernel", records)
        self.assertIn("Fixture.DirectSourceModel.kernel_isMarkov", records)

    def test_explicit_parent_classification_is_complete_before_materialization(
        self,
    ) -> None:
        raw = closure_candidate_raw_audit(explicit_parent_route_field=True)
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            completed = self._complete(template)
        entry = completed["manual_current_groups"]["Fixture.DirectSourceModel.kernel"]
        response = entry["response"]
        response["classification"] = "approved_source_convention"
        self.assertIn(
            "lacks its exact convention id/hash",
            COMPLEMENT._completed_review_entry_error(
                entry, label="explicit parent fixture"
            ),
        )
        response["model_convention_ids"] = ["fixture-convention"]
        response["model_convention_sha256_by_id"] = {
            "fixture-convention": digest("9")
        }
        self.assertEqual(
            COMPLEMENT._completed_review_entry_error(
                entry, label="explicit parent fixture"
            ),
            "",
        )

    def test_closure_template_rejects_missing_attestation_and_ambiguous_parent(self) -> None:
        raw = closure_candidate_raw_audit()
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            completed = self._complete(template)
            parent = completed["manual_current_groups"][
                "semantic-model::fixture-direct-model"
            ]
            assert isinstance(parent, dict)
            response = parent["response"]
            assert isinstance(response, dict)
            response["semantic_model_dimensions"] = {
                "joint_law_and_state_evolution": {
                    "verdict": "matches_source_model",
                    "source_location": "source.txt:1-4",
                    "semantic_comparison": "Current source model review.",
                    "lean_evidence": "Current generated model surface.",
                }
            }
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "closure attestation",
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    raw,
                    completed,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )

            ambiguous = closure_candidate_raw_audit(ambiguous_parent=True)
            ambiguous_template = COMPLEMENT.manual_current_complement_template(
                ambiguous, paper=PAPER, paper_dir=self.paper_dir
            )
        records = ambiguous_template["manual_current_groups"]
        assert isinstance(records, dict)
        self.assertEqual(len(ambiguous_template["record_field_closure_completion_candidates"]), 0)
        self.assertIn("Fixture.DirectSourceModel.kernel", records)
        self.assertIn("Fixture.DirectSourceModel.kernel_isMarkov", records)

    def test_closure_candidates_fail_closed_for_changed_signature_or_closure(self) -> None:
        changed_signature = closure_candidate_raw_audit()
        semantic_items = changed_signature["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(semantic_items[0], dict)
        semantic_items[0]["reviewed_elaborated_signature_identities"] = [
            {
                "qualified_declaration": "Fixture.PaperInterface.direct_model",
                "elaborated_signature_sha256": digest("e"),
            }
        ]
        stamp_source_record_audit_receipts(changed_signature)
        self.assertEqual(
            CLOSURE.current_record_field_closure_completion_candidates(
                changed_signature
            ),
            (),
        )

        incomplete_closure = closure_candidate_raw_audit()
        fields = incomplete_closure["recursive_field_items"]
        assert isinstance(fields, list) and isinstance(fields[0], dict)
        fields[0]["nested_structures"] = ["Fixture.UnemittedNestedRecord"]
        stamp_source_record_audit_receipts(incomplete_closure)
        self.assertEqual(
            CLOSURE.current_record_field_closure_completion_candidates(
                incomplete_closure
            ),
            (),
        )

    def test_materialization_binds_manual_responses_to_current_receipts(self) -> None:
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays("current_overlay : P"),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                self.raw, paper=PAPER, paper_dir=self.paper_dir
            )
            result = COMPLEMENT.materialize_manual_current_complement(
                self.raw,
                self._complete(template),
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir
                / "audit"
                / "source_record_match_llm.json",
            )
        self.assertEqual(
            set(result["items"]), {"current_manual_a : P", "current_manual_b : P"}
        )
        self.assertNotIn("current_overlay : P", result["items"])
        self.assertEqual(
            result[PROTOCOL.FORMALIZATION_REVIEW_PROTOCOL_FIELD],
            PROTOCOL.formalization_review_protocol_digest(),
        )
        self.assertTrue(
            PROTOCOL.formalization_judgment_review_protocol_is_current(
                {
                    PROTOCOL.FORMALIZATION_COVERAGE_PROTOCOL_FIELD:
                        PROTOCOL.formalization_coverage_protocol_digest()
                },
                result,
            )
        )
        for item in result["items"].values():
            self.assertEqual(item["source_record_audit_sha256"], self.raw["source_record_audit_sha256"])
            self.assertEqual(item["source_record_item_digest_schema"], 5)
            self.assertEqual(len(item["source_record_item_sha256s"]), 1)
            self.assertNotIn("current_selected_semantic_revalidation_item", item)

    def test_manual_response_cannot_serialize_scoped_rebind_provenance(self) -> None:
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                self.raw, paper=PAPER, paper_dir=self.paper_dir
            )
            completed = self._complete(template)
            records = completed["manual_current_groups"]
            assert isinstance(records, dict)
            response = records["current_overlay : P"]["response"]
            assert isinstance(response, dict)
            response["source_record_scoped_receipt_rebind"] = {"forged": True}
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "generated/overlay transport fields",
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    self.raw,
                    completed,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )

    def test_refuses_stale_descriptor_or_changed_overlay_complement(self) -> None:
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays("current_overlay : P"),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                self.raw, paper=PAPER, paper_dir=self.paper_dir
            )
            completed = self._complete(template)
            records = completed["manual_current_groups"]
            assert isinstance(records, dict)
            records["current_manual_a : P"][
                "current_group_semantic_descriptor_sha256"
            ] = digest("0")
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError, "mismatched semantic descriptor"
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    self.raw,
                    completed,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )

        completed = self._complete(template)
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays("current_overlay : P", "current_manual_a : P"),
        ):
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError, "stale authenticated-overlay ledger"
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    self.raw,
                    completed,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )

    def test_materializer_injects_raw_derived_top_level_pin(self) -> None:
        item = raw_item("current_manual : P", semantic_tag="manual")
        source_association = association("c")
        item["source_contract_association"] = source_association
        raw = raw_audit(item)
        with patch.object(COMPLEMENT, "_authenticated_overlay_items", return_value=self._overlays()):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            completed = self._complete(template)
            result = COMPLEMENT.materialize_manual_current_complement(
                raw,
                completed,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir
                / "audit"
                / "source_record_match_llm.json",
            )
        response = result["items"]["current_manual : P"]
        assert isinstance(response, dict)
        self.assertEqual(
            response["semantic_association_sha256"],
            source_association["semantic_association_sha256"],
        )

        tampered = self._complete(template)
        records = tampered["manual_current_groups"]
        assert isinstance(records, dict)
        manual_response = records["current_manual : P"]["response"]
        assert isinstance(manual_response, dict)
        manual_response["semantic_association_sha256"] = source_association[
            "semantic_association_sha256"
        ]
        with patch.object(COMPLEMENT, "_authenticated_overlay_items", return_value=self._overlays()):
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "reviewer-supplied semantic_association_sha256",
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    raw,
                    tampered,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )

    def test_completed_template_rebind_is_key_and_fqn_independent(self) -> None:
        # The declaration/FQN changes with the key in this fixture. The raw
        # group's canonical descriptor intentionally omits that navigation
        # surface, so the crosswalk must not use it to select a response.
        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="same"))
        fresh_raw = raw_audit(raw_item("renamed endpoint : P", semantic_tag="same"))
        prior_template = self._template(prior_raw)
        completed_prior = self._complete(prior_template)
        prior_records = completed_prior["manual_current_groups"]
        assert isinstance(prior_records, dict)
        prior_response = prior_records["prior endpoint : P"]["response"]
        assert isinstance(prior_response, dict)
        # These are deliberately old/generated credentials. The rebind must
        # remove them at every nesting depth and let materialization derive the
        # fresh equivalents from the current raw members.
        prior_response.update(
            {
                "semantic_association_sha256": digest("f"),
                "source_record_item_sha256": digest("e"),
                "source_contract_association": {"forged": True},
                "semantic_model_dimensions": {
                    "carrier_and_domain": {
                        "semantic_association_sha256": digest("d"),
                        "nested": {
                            "corrected_target_sha256_by_source_semantic_sha256": {
                                digest("c"): digest("b")
                            },
                            "source_record_scoped_receipt_rebind": {"forged": True},
                            "raw_evidence_projection": {"forged": True},
                            "generated_response_pin": {"forged": True},
                        },
                    }
                },
            }
        )
        fresh_template = self._template(fresh_raw)
        fresh_records = fresh_template["manual_current_groups"]
        assert isinstance(fresh_records, dict)
        self.assertEqual(
            COMPLEMENT._canonical_digest(
                prior_records["prior endpoint : P"][
                    "current_group_semantic_descriptor"
                ]
            ),
            COMPLEMENT._canonical_digest(
                fresh_records["renamed endpoint : P"][
                    "current_group_semantic_descriptor"
                ]
            ),
        )
        self.assertEqual(
            prior_records["prior endpoint : P"]["current_item_pins"],
            fresh_records["renamed endpoint : P"]["current_item_pins"],
        )

        rebound = COMPLEMENT.rebind_completed_manual_current_complement_template(
            fresh_template, completed_prior, paper=PAPER
        )
        rebound_records = rebound["manual_current_groups"]
        assert isinstance(rebound_records, dict)
        self.assertEqual(set(rebound_records), {"renamed endpoint : P"})
        self.assertEqual(
            rebound["current_source_record_audit_sha256"],
            fresh_template["current_source_record_audit_sha256"],
        )
        self.assertEqual(
            rebound_records["renamed endpoint : P"][
                "current_group_semantic_descriptor"
            ],
            fresh_records["renamed endpoint : P"]["current_group_semantic_descriptor"],
        )
        self.assertEqual(
            rebound_records["renamed endpoint : P"]["current_item_pins"],
            fresh_records["renamed endpoint : P"]["current_item_pins"],
        )
        response = rebound_records["renamed endpoint : P"]["response"]
        assert isinstance(response, dict)
        self.assertNotIn("semantic_association_sha256", response)
        self.assertNotIn("source_record_item_sha256", response)
        self.assertNotIn("source_contract_association", response)
        dimensions = response["semantic_model_dimensions"]
        assert isinstance(dimensions, dict)
        dimension = dimensions["carrier_and_domain"]
        assert isinstance(dimension, dict)
        self.assertNotIn("semantic_association_sha256", dimension)
        nested = dimension["nested"]
        assert isinstance(nested, dict)
        self.assertNotIn(
            "corrected_target_sha256_by_source_semantic_sha256", nested
        )
        self.assertNotIn("source_record_scoped_receipt_rebind", nested)
        self.assertNotIn("raw_evidence_projection", nested)
        self.assertNotIn("generated_response_pin", nested)

        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            materialized = COMPLEMENT.materialize_manual_current_complement(
                fresh_raw,
                rebound,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir
                / "audit"
                / "source_record_match_llm.json",
            )
        item = materialized["items"]["renamed endpoint : P"]
        assert isinstance(item, dict)
        self.assertEqual(
            item["source_record_audit_sha256"],
            fresh_raw["source_record_audit_sha256"],
        )
        self.assertEqual(item["source_record_item_sha256"], digest("e"))

    def test_completed_prior_without_runtime_queue_ledger_can_rebind(self) -> None:
        """A v2 completed prior has no authority to set a v3 queue ledger."""

        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="same"))
        fresh_raw = raw_audit(raw_item("fresh endpoint : P", semantic_tag="same"))
        completed_prior = self._complete(self._template(prior_raw))
        completed_prior["policy_version"] = (
            "source-record-v10-manual-current-complement-v2"
        )
        completed_prior.pop(COMPLEMENT.STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD)
        fresh_template = self._template(fresh_raw)

        rebound = COMPLEMENT.rebind_completed_manual_current_complement_template(
            fresh_template,
            completed_prior,
            paper=PAPER,
        )

        self.assertEqual(
            rebound[COMPLEMENT.STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD],
            fresh_template[COMPLEMENT.STRICT_V11_FULL_SPEC_RUNTIME_COVERAGE_FIELD],
        )

    def test_completed_template_rebind_refuses_duplicate_match_classes(self) -> None:
        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="same"))
        completed_prior = self._complete(self._template(prior_raw))
        duplicate_fresh_raw = raw_audit(
            raw_item("fresh endpoint one : P", semantic_tag="same"),
            raw_item("fresh endpoint two : P", semantic_tag="same"),
        )
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError,
            "ambiguous duplicate descriptor/current-item-pin",
        ):
            COMPLEMENT.rebind_completed_manual_current_complement_template(
                self._template(duplicate_fresh_raw), completed_prior, paper=PAPER
            )

        duplicate_prior_raw = raw_audit(
            raw_item("prior endpoint one : P", semantic_tag="same"),
            raw_item("prior endpoint two : P", semantic_tag="same"),
        )
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError,
            "ambiguous duplicate descriptor/current-item-pin",
        ):
            COMPLEMENT.rebind_completed_manual_current_complement_template(
                self._template(prior_raw),
                self._complete(self._template(duplicate_prior_raw)),
                paper=PAPER,
            )

    def test_completed_template_rebind_refuses_descriptor_or_pin_change(self) -> None:
        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="same"))
        completed_prior = self._complete(self._template(prior_raw))

        changed_descriptor_raw = raw_audit(
            raw_item("fresh endpoint : P", semantic_tag="changed")
        )
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError,
            "no exact descriptor/ordered-current-item-pin match",
        ):
            COMPLEMENT.rebind_completed_manual_current_complement_template(
                self._template(changed_descriptor_raw), completed_prior, paper=PAPER
            )

        changed_pin = raw_item("fresh endpoint : P", semantic_tag="same")
        changed_pin["source_record_item_sha256"] = digest("f")
        changed_pin_raw = raw_audit(changed_pin)
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError,
            "no exact descriptor/ordered-current-item-pin match",
        ):
            COMPLEMENT.rebind_completed_manual_current_complement_template(
                self._template(changed_pin_raw), completed_prior, paper=PAPER
            )

    def test_completed_template_rebind_consumes_fresh_subset_and_reports_surplus(self) -> None:
        # This models KR's transition from a 72-group completed template to a
        # 28-group manual complement once authenticated overlays supply the
        # other 44.  Those surplus prior reviews must remain absent from the
        # result rather than becoming unscoped evidence.
        prior_raw = raw_audit(
            *[
                raw_item(f"prior shared {index} : P", semantic_tag=f"shared-{index}")
                for index in range(28)
            ],
            *[
                raw_item(f"prior surplus {index} : P", semantic_tag=f"surplus-{index}")
                for index in range(28, 72)
            ],
        )
        fresh_raw = raw_audit(
            *[
                raw_item(f"fresh renamed {index} : P", semantic_tag=f"shared-{index}")
                for index in range(28)
            ]
        )
        rebound, summary = COMPLEMENT._rebind_completed_manual_current_complement_template(
            self._template(fresh_raw),
            self._complete(self._template(prior_raw)),
            paper=PAPER,
        )
        self.assertEqual(
            summary,
            {
                "fresh_group_count": 28,
                "matched_prior_group_count": 28,
                "ignored_prior_group_count": 44,
            },
        )
        rebound_groups = rebound["manual_current_groups"]
        assert isinstance(rebound_groups, dict)
        self.assertEqual(len(rebound_groups), 28)
        self.assertEqual(
            set(rebound_groups),
            {f"fresh renamed {index} : P" for index in range(28)},
        )
        self.assertFalse(
            any("prior surplus" in key for key in rebound_groups),
            "surplus prior groups must never be serialized into the fresh evidence template",
        )

    def test_review_seed_retains_unmatched_groups_as_non_evidence(self) -> None:
        # This is the partial-overlap case: 66 historic reviews can be reused
        # without keys/FQNs, while 61 current groups must still receive a new
        # current review. The six remaining historic groups are surplus, not
        # evidence for any current group.
        prior_raw = raw_audit(
            *[
                raw_item(f"prior shared {index} : P", semantic_tag=f"shared-{index}")
                for index in range(66)
            ],
            *[
                raw_item(f"prior surplus {index} : P", semantic_tag=f"surplus-{index}")
                for index in range(66, 72)
            ],
        )
        fresh_raw = raw_audit(
            *[
                raw_item(f"fresh renamed {index} : P", semantic_tag=f"shared-{index}")
                for index in range(66)
            ],
            *[
                raw_item(f"fresh unreviewed {index} : P", semantic_tag=f"new-{index}")
                for index in range(61)
            ],
        )
        completed_prior = self._complete(self._template(prior_raw))
        prior_groups = completed_prior["manual_current_groups"]
        assert isinstance(prior_groups, dict)
        prior_response = prior_groups["prior shared 0 : P"]["response"]
        assert isinstance(prior_response, dict)
        # A seed may transfer reviewer-authored content only. It must discard
        # any stale/generated transport credential before a future current
        # materialization reconstructs it from the fresh raw audit.
        prior_response["semantic_association_sha256"] = digest("f")
        prior_response["source_record_audit_sha256"] = digest("e")

        seeded, summary = COMPLEMENT._seed_completed_manual_current_complement_template(
            self._template(fresh_raw), completed_prior, paper=PAPER
        )
        self.assertEqual(
            summary,
            {
                "fresh_group_count": 127,
                "completed_prior_group_count": 72,
                "seeded_group_count": 66,
                "unresolved_group_count": 61,
                "surplus_prior_group_count": 6,
            },
        )
        self.assertTrue(seeded["non_evidence_scaffold"])
        self.assertTrue(seeded["must_not_be_written_to_repository_sidecar"])
        self.assertFalse(seeded["reviewed_current_semantics"])
        self.assertEqual(
            seeded["review_seed"],
            {
                "schema": COMPLEMENT.SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_SCHEMA,
                "policy_version": (
                    COMPLEMENT.SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_POLICY_VERSION
                ),
                "match_relation": (
                    COMPLEMENT.SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_SEED_MATCH_RELATION
                ),
                **summary,
            },
        )
        seeded_groups = seeded["manual_current_groups"]
        assert isinstance(seeded_groups, dict)
        self.assertEqual(len(seeded_groups), 127)
        for index in range(66):
            entry = seeded_groups[f"fresh renamed {index} : P"]
            assert isinstance(entry, dict)
            self.assertTrue(entry["reviewed_current_semantics"])
            self.assertEqual(
                entry["review_seed_status"],
                "seeded_exact_descriptor_and_ordered_current_item_pins",
            )
            response = entry["response"]
            assert isinstance(response, dict)
            self.assertEqual(response["classification"], "validated_source_assumption")
        seeded_response = seeded_groups["fresh renamed 0 : P"]["response"]
        assert isinstance(seeded_response, dict)
        self.assertNotIn("semantic_association_sha256", seeded_response)
        self.assertNotIn("source_record_audit_sha256", seeded_response)
        for index in range(61):
            entry = seeded_groups[f"fresh unreviewed {index} : P"]
            assert isinstance(entry, dict)
            self.assertFalse(entry["reviewed_current_semantics"])
            self.assertEqual(entry["reviewer"], "")
            self.assertEqual(entry["validated_at"], "")
            self.assertEqual(entry["review_notes"], "")
            self.assertEqual(entry["response"], {})
            self.assertEqual(
                entry["review_seed_status"],
                "unreviewed_no_unique_completed_prior_match",
            )
        self.assertFalse(
            any("prior surplus" in key for key in seeded_groups),
            "unmatched prior records must never be copied into the fresh template",
        )

        # The untouched seeded artifact is non-evidence. Even if someone
        # removes its top-level scaffold prematurely, each unresolved group
        # blocks materialization until it is explicitly reviewed.
        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError, "still marked non-evidence"
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    fresh_raw,
                    seeded,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )
            prematurely_completed = copy.deepcopy(seeded)
            prematurely_completed.pop("non_evidence_scaffold")
            prematurely_completed.pop("must_not_be_written_to_repository_sidecar")
            prematurely_completed["reviewed_current_semantics"] = True
            prematurely_completed["reviewer"] = "Fixture current semantic reviewer"
            prematurely_completed["validated_at"] = "2026-07-28T00:00:00Z"
            with self.assertRaisesRegex(
                COMPLEMENT.SourceRecordManualComplementError,
                "must explicitly mark current semantics reviewed",
            ):
                COMPLEMENT.materialize_manual_current_complement(
                    fresh_raw,
                    prematurely_completed,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.paper_dir
                    / "audit"
                    / "source_record_match_llm.json",
                )

    def test_review_fragments_complete_seed_without_key_matching(self) -> None:
        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="shared"))
        fresh_raw = raw_audit(
            raw_item("fresh renamed endpoint : P", semantic_tag="shared"),
            raw_item("fresh first review : P", semantic_tag="first"),
            raw_item("fresh second review : P", semantic_tag="second"),
        )
        seeded = COMPLEMENT.seed_completed_manual_current_complement_template(
            self._template(fresh_raw),
            self._complete(self._template(prior_raw)),
            paper=PAPER,
        )
        groups = seeded["manual_current_groups"]
        assert isinstance(groups, dict)

        def fragment_entry(key: str) -> dict[str, object]:
            source = copy.deepcopy(groups[key])
            assert isinstance(source, dict)
            source.pop("review_seed_status", None)
            source.update(
                {
                    "reviewed_current_semantics": True,
                    "reviewer": "Independent fixture reviewer",
                    "validated_at": "2026-07-28T00:00:00Z",
                    "review_notes": "Reviewed from the complete current descriptor and pins.",
                    "response": {
                        "classification": "validated_source_assumption",
                        "source_target_disposition": "literal_source_match",
                        "reason": "Current source premise reviewed independently.",
                        "source_location": "source.txt:1-2",
                        "validator_type": "manual_semantic_v10",
                    },
                }
            )
            return source

        fragment = {
            "schema": COMPLEMENT.SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_SCHEMA,
            "artifact_kind": COMPLEMENT.SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_KIND,
            "paper": PAPER,
            "current_source_record_audit_sha256": seeded[
                "current_source_record_audit_sha256"
            ],
            "entries": {
                # These deliberately differ from the fresh storage addresses.
                "fragment storage address one": fragment_entry("fresh first review : P"),
                "fragment storage address two": fragment_entry("fresh second review : P"),
            },
        }
        completed = COMPLEMENT.assemble_seeded_manual_current_complement_template(
            seeded,
            [fragment],
            paper=PAPER,
            reviewer="Fixture composition reviewer",
            validated_at="2026-07-28T00:05:00Z",
            review_notes="All current review fragments were assembled by exact facts.",
        )
        self.assertNotIn("non_evidence_scaffold", completed)
        self.assertNotIn("must_not_be_written_to_repository_sidecar", completed)
        self.assertNotIn("review_seed", completed)
        completed_groups = completed["manual_current_groups"]
        assert isinstance(completed_groups, dict)
        self.assertEqual(set(completed_groups), set(groups))
        for entry in completed_groups.values():
            assert isinstance(entry, dict)
            self.assertTrue(entry["reviewed_current_semantics"])
            self.assertNotIn("review_seed_status", entry)
        self.assertEqual(
            completed_groups["fresh first review : P"]["response"]["reason"],
            "Current source premise reviewed independently.",
        )

        incomplete = copy.deepcopy(fragment)
        incomplete["entries"].pop("fragment storage address two")
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError,
            "leave current semantic groups unreviewed",
        ):
            COMPLEMENT.assemble_seeded_manual_current_complement_template(
                seeded,
                [incomplete],
                paper=PAPER,
                reviewer="Fixture composition reviewer",
                validated_at="2026-07-28T00:05:00Z",
                review_notes="All current review fragments were assembled by exact facts.",
            )

    def test_review_fragments_complete_fresh_template_without_key_matching(self) -> None:
        fresh_raw = raw_audit(
            raw_item("fresh first review : P", semantic_tag="first"),
            raw_item("fresh second review : P", semantic_tag="second"),
        )
        fresh = self._template(fresh_raw)
        groups = fresh["manual_current_groups"]
        assert isinstance(groups, dict)

        def fragment_entry(key: str) -> dict[str, object]:
            source = copy.deepcopy(groups[key])
            assert isinstance(source, dict)
            source.update(
                {
                    "reviewed_current_semantics": True,
                    "reviewer": "Independent fixture reviewer",
                    "validated_at": "2026-07-28T00:00:00Z",
                    "review_notes": "Reviewed from the complete current descriptor and pins.",
                    "response": {
                        "classification": "validated_source_assumption",
                        "source_target_disposition": "literal_source_match",
                        "reason": "Current source premise reviewed independently.",
                        "source_location": "source.txt:1-2",
                        "validator_type": "manual_semantic_v10",
                    },
                }
            )
            return source

        fragment = {
            "schema": COMPLEMENT.SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_SCHEMA,
            "artifact_kind": COMPLEMENT.SOURCE_RECORD_MANUAL_COMPLEMENT_REVIEW_FRAGMENT_KIND,
            "paper": PAPER,
            "current_source_record_audit_sha256": fresh[
                "current_source_record_audit_sha256"
            ],
            "entries": {
                # Storage addresses deliberately do not match template keys.
                "fragment storage address one": fragment_entry("fresh first review : P"),
                "fragment storage address two": fragment_entry("fresh second review : P"),
            },
        }
        completed = COMPLEMENT.assemble_fresh_manual_current_complement_template(
            fresh,
            [fragment],
            paper=PAPER,
            reviewer="Fixture composition reviewer",
            validated_at="2026-07-28T00:05:00Z",
            review_notes="All current review fragments were assembled by exact facts.",
        )
        self.assertNotIn("non_evidence_scaffold", completed)
        self.assertNotIn("must_not_be_written_to_repository_sidecar", completed)
        self.assertNotIn("review_seed", completed)
        completed_groups = completed["manual_current_groups"]
        assert isinstance(completed_groups, dict)
        self.assertEqual(set(completed_groups), set(groups))
        self.assertEqual(
            completed_groups["fresh first review : P"]["response"]["reason"],
            "Current source premise reviewed independently.",
        )

        incomplete = copy.deepcopy(fragment)
        incomplete["entries"].pop("fragment storage address two")
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError,
            "leave current semantic groups unreviewed",
        ):
            COMPLEMENT.assemble_fresh_manual_current_complement_template(
                fresh,
                [incomplete],
                paper=PAPER,
                reviewer="Fixture composition reviewer",
                validated_at="2026-07-28T00:05:00Z",
                review_notes="All current review fragments were assembled by exact facts.",
            )

    def test_review_seed_refuses_candidate_or_draft_inputs(self) -> None:
        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="same"))
        fresh_raw = raw_audit(raw_item("fresh endpoint : P", semantic_tag="same"))
        completed_prior = self._complete(self._template(prior_raw))

        candidate_prior = copy.deepcopy(completed_prior)
        candidate_prior["candidate_only"] = True
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError, "candidate/draft/non-evidence"
        ):
            COMPLEMENT.seed_completed_manual_current_complement_template(
                self._template(fresh_raw), candidate_prior, paper=PAPER
            )

        draft_fresh = self._template(fresh_raw)
        draft_fresh["review_status"] = "draft"
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError, "candidate/draft/non-evidence"
        ):
            COMPLEMENT.seed_completed_manual_current_complement_template(
                draft_fresh, completed_prior, paper=PAPER
            )

    def test_review_seed_leaves_ambiguous_match_classes_unreviewed(self) -> None:
        # Two fresh groups have identical semantic facts and receipts. The
        # seed must not choose one using their presentation keys or FQNs.
        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="same"))
        fresh_raw = raw_audit(
            raw_item("fresh endpoint one : P", semantic_tag="same"),
            raw_item("fresh endpoint two : P", semantic_tag="same"),
        )
        seeded, summary = COMPLEMENT._seed_completed_manual_current_complement_template(
            self._template(fresh_raw),
            self._complete(self._template(prior_raw)),
            paper=PAPER,
        )
        self.assertEqual(
            summary,
            {
                "fresh_group_count": 2,
                "completed_prior_group_count": 1,
                "seeded_group_count": 0,
                "unresolved_group_count": 2,
                "surplus_prior_group_count": 1,
            },
        )
        groups = seeded["manual_current_groups"]
        assert isinstance(groups, dict)
        for entry in groups.values():
            assert isinstance(entry, dict)
            self.assertFalse(entry["reviewed_current_semantics"])
            self.assertEqual(entry["response"], {})
            self.assertEqual(
                entry["review_seed_status"],
                "unreviewed_no_unique_completed_prior_match",
            )

    def test_completed_template_rebind_refuses_candidate_or_draft_inputs(self) -> None:
        prior_raw = raw_audit(raw_item("prior endpoint : P", semantic_tag="same"))
        fresh_raw = raw_audit(raw_item("fresh endpoint : P", semantic_tag="same"))
        completed_prior = self._complete(self._template(prior_raw))

        candidate_prior = copy.deepcopy(completed_prior)
        candidate_prior["candidate_only"] = True
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError, "candidate/draft/non-evidence"
        ):
            COMPLEMENT.rebind_completed_manual_current_complement_template(
                self._template(fresh_raw), candidate_prior, paper=PAPER
            )

        draft_prior = copy.deepcopy(completed_prior)
        draft_prior["review_status"] = "draft"
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError, "candidate/draft/non-evidence"
        ):
            COMPLEMENT.rebind_completed_manual_current_complement_template(
                self._template(fresh_raw), draft_prior, paper=PAPER
            )

        candidate_fresh = self._template(fresh_raw)
        candidate_fresh["candidate_only"] = True
        with self.assertRaisesRegex(
            COMPLEMENT.SourceRecordManualComplementError, "candidate/draft/non-evidence"
        ):
            COMPLEMENT.rebind_completed_manual_current_complement_template(
                candidate_fresh, completed_prior, paper=PAPER
            )

    def test_projector_uses_semantic_precedence_and_nested_pins(self) -> None:
        primary = association("a")
        secondary = association("b")
        grouped = {
            "judgment_key": "semantic response",
            "source_statement_association": primary,
            "semantic_contract_source_association": secondary,
            "semantic_contract_group": association("d"),
            "dimensions": [
                {
                    "id": "joint_law_and_state_evolution",
                    "source_model_composition_association": association("e", nested=True),
                    "source_equality_partition_association": association("c", nested=True),
                    "source_model_derivation_association": association("b", nested=True),
                }
            ],
        }
        response = {
            "semantic_model_dimensions": {
                "joint_law_and_state_evolution": {
                    "source_model_composition_analysis": {},
                    "source_equality_partition_analysis": {},
                    "source_model_derivation_analysis": {},
                }
            }
        }
        projected, error = TARGET.project_source_record_response_association_pins(
            [("semantic_model_items", grouped)], response, judgment_key="semantic response"
        )
        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        dimensions = projected["semantic_model_dimensions"]
        assert isinstance(dimensions, dict)
        dimension = dimensions["joint_law_and_state_evolution"]
        assert isinstance(dimension, dict)
        self.assertEqual(
            dimension["semantic_association_sha256"],
            primary["semantic_association_sha256"],
        )
        composition = dimension["source_model_composition_analysis"]
        equality = dimension["source_equality_partition_analysis"]
        derivation = dimension["source_model_derivation_analysis"]
        assert (
            isinstance(composition, dict)
            and isinstance(equality, dict)
            and isinstance(derivation, dict)
        )
        self.assertEqual(
            composition["semantic_association_sha256"],
            grouped["dimensions"][0]["source_model_composition_association"][
                "semantic_association_sha256"
            ],
        )
        self.assertEqual(
            equality["semantic_association_sha256"],
            grouped["dimensions"][0]["source_equality_partition_association"][
                "semantic_association_sha256"
            ],
        )
        self.assertEqual(
            derivation["semantic_association_sha256"],
            grouped["dimensions"][0]["source_model_derivation_association"][
                "semantic_association_sha256"
            ],
        )

    def test_projector_rejects_conflicting_exact_raw_group_associations(self) -> None:
        first = raw_item("one response", semantic_tag="one")
        second = raw_item("one response", semantic_tag="two")
        first["source_contract_association"] = association("a")
        second["source_contract_association"] = association("b")
        projected, error = TARGET.project_source_record_response_association_pins(
            [
                ("boundary_input_items", first),
                ("conclusion_dependency_items", second),
            ],
            {"classification": "validated_source_assumption"},
            judgment_key="one response",
        )
        self.assertIsNone(projected)
        self.assertIn("conflicting source association pins", error)

    def test_projector_processes_theorem_facing_members_with_boundary_members(self) -> None:
        theorem_facing = raw_item("one response", semantic_tag="theorem-facing")
        boundary = raw_item("one response", semantic_tag="boundary")
        current_association = association("a")
        theorem_facing["source_contract_association"] = current_association
        boundary["source_contract_association"] = current_association

        projected, error = TARGET.project_source_record_response_association_pins(
            [
                ("theorem_facing_input_items", theorem_facing),
                ("boundary_input_items", boundary),
            ],
            {"classification": "validated_source_assumption"},
            judgment_key="one response",
        )

        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        self.assertEqual(
            projected["semantic_association_sha256"],
            current_association["semantic_association_sha256"],
        )

    def test_projector_processes_type_valued_certificate_members(self) -> None:
        certificate = raw_item("one certificate", semantic_tag="type-witness")
        certificate["source_contract_association"] = association("a")

        projected, error = TARGET.project_source_record_response_association_pins(
            [("type_valued_certificate_result_items", certificate)],
            {"classification": "proved_from_primitives"},
            judgment_key="one certificate",
        )

        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        self.assertEqual(
            projected["semantic_association_sha256"],
            certificate["source_contract_association"]["semantic_association_sha256"],
        )

    def test_materialization_accepts_source_free_type_valued_certificate(self) -> None:
        certificate = raw_item("current type witness", semantic_tag="type-witness")
        certificate["kind"] = "type_valued_certificate_result"
        raw = raw_audit()
        raw["type_valued_certificate_result_items"] = [certificate]
        stamp_source_record_audit_receipts(raw)

        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            result = COMPLEMENT.materialize_manual_current_complement(
                raw,
                self._complete(template),
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir
                / "audit"
                / "source_record_match_llm.json",
            )

        self.assertEqual(
            result["items"]["current type witness"]["classification"],
            "validated_source_assumption",
        )

    def test_materialization_accepts_theorem_facing_and_boundary_raw_group(self) -> None:
        boundary = raw_item("current manual : P", semantic_tag="boundary")
        theorem_facing = raw_item("current manual : P", semantic_tag="theorem-facing")
        current_association = association("a")
        boundary["source_contract_association"] = current_association
        theorem_facing["source_contract_association"] = current_association
        raw = raw_audit(boundary)
        raw["theorem_facing_input_items"] = [theorem_facing]
        stamp_source_record_audit_receipts(raw)

        with patch.object(
            COMPLEMENT,
            "_authenticated_overlay_items",
            return_value=self._overlays(),
        ):
            template = COMPLEMENT.manual_current_complement_template(
                raw, paper=PAPER, paper_dir=self.paper_dir
            )
            result = COMPLEMENT.materialize_manual_current_complement(
                raw,
                self._complete(template),
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.paper_dir
                / "audit"
                / "source_record_match_llm.json",
            )

        item = result["items"]["current manual : P"]
        self.assertEqual(
            item["semantic_association_sha256"],
            current_association["semantic_association_sha256"],
        )

    def test_projector_derives_current_corrected_target_map(self) -> None:
        source_association, source_item, expected_targets = corrected_association_fixture()
        item = raw_item("corrected input", semantic_tag="corrected")
        item["source_contract_association"] = source_association
        response = {
            "classification": "validated_source_assumption",
            "source_target_disposition": "approved_corrected_target",
        }
        statement_map = {"items": {"fixture_corrected_source": source_item}}
        projected, error = TARGET.project_source_record_response_association_pins(
            [("boundary_input_items", item)],
            response,
            judgment_key="corrected input",
            statement_map=statement_map,
        )
        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        self.assertEqual(
            projected["corrected_target_sha256_by_source_semantic_sha256"],
            expected_targets,
        )

        semantic_item = {
            "judgment_key": "corrected semantic",
            "source_statement_association": source_association,
            "dimensions": [{"id": "carrier_and_domain"}],
        }
        projected, error = TARGET.project_source_record_response_association_pins(
            [("semantic_model_items", semantic_item)],
            {
                "semantic_model_dimensions": {
                    "carrier_and_domain": {
                        "source_target_disposition": "approved_corrected_target"
                    }
                }
            },
            judgment_key="corrected semantic",
            statement_map=statement_map,
        )
        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        semantic_dimensions = projected["semantic_model_dimensions"]
        assert isinstance(semantic_dimensions, dict)
        semantic_response = semantic_dimensions["carrier_and_domain"]
        assert isinstance(semantic_response, dict)
        self.assertEqual(
            semantic_response["corrected_target_sha256_by_source_semantic_sha256"],
            expected_targets,
        )

        conflicting = copy.deepcopy(response)
        conflicting["corrected_target_sha256_by_source_semantic_sha256"] = {
            next(iter(expected_targets)): digest("0")
        }
        projected, error = TARGET.project_source_record_response_association_pins(
            [("boundary_input_items", item)],
            conflicting,
            judgment_key="corrected input",
            statement_map=statement_map,
        )
        self.assertIsNone(projected)
        self.assertIn("conflicts with the current raw corrected-target map", error)

        projected, error = TARGET.project_source_record_response_association_pins(
            [("boundary_input_items", item)],
            conflicting,
            judgment_key="corrected input",
            statement_map=statement_map,
            replace_generated_credentials=True,
        )
        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        self.assertEqual(
            projected["corrected_target_sha256_by_source_semantic_sha256"],
            expected_targets,
        )

        projected, error = TARGET.project_source_record_response_association_pins(
            [("boundary_input_items", item)],
            {
                **response,
                "corrected_target_sha256_by_source_semantic_sha256": expected_targets,
            },
            judgment_key="corrected input",
            statement_map=statement_map,
            reject_existing=True,
        )
        self.assertIsNone(projected)
        self.assertIn("reviewer-supplied", error)


if __name__ == "__main__":
    unittest.main()
