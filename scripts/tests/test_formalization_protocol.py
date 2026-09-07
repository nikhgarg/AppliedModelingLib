#!/usr/bin/env python3
"""Regression tests for the authoritative formalization protocol."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(ROOT / "scripts"))

from formalization_protocol import (  # noqa: E402
    CLOSEOUT_REVIEW_POLICY_DEFAULT_REPEAT_SCOPE,
    CLOSEOUT_REVIEW_POLICY_DEFAULT_SOURCE_SCOPE,
    EXPECTED_LEGACY_V10_TRANSITION_BASELINE_COMMIT,
    EXPECTED_LEGACY_V10_TRANSITION_TRUSTED_REF,
    EXPECTED_CLEAN_LEAN_OUTPUT_BYTES,
    EXPECTED_LEAN_DIAGNOSTIC_FAILURES,
    EXPECTED_REQUIRED_REUSE_IDENTITIES,
    EXPECTED_REUSE_FAILURES,
    IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
    IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
    IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
    IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
    IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
    PROTOCOL_PATH,
    FORMALIZATION_COVERAGE_PROTOCOL_FIELD,
    FORMALIZATION_REVIEW_PROTOCOL_FIELD,
    FormalizationProtocolError,
    formalization_coverage_protocol_digest,
    formalization_judgment_review_protocol_is_current,
    formalization_item_review_protocol_digest,
    formalization_material_protocol_digest,
    formalization_protocol_digest,
    formalization_protocol_receipt_matches,
    formalization_review_protocol_digest,
    load_formalization_protocol,
    closeout_review_policy_assurance_projection,
    closeout_review_policy_material_projection,
    closeout_review_policy_scheduling_projection,
    resolve_closeout_review_policy,
    resolve_closeout_review_policy_assurance,
    validate_formalization_protocol,
)
import formalization_protocol as protocol_module  # noqa: E402


class FormalizationProtocolTests(unittest.TestCase):
    def test_final_adversary_cannot_promote_default_prose_into_a_blocker(self) -> None:
        prompt = (
            ROOT
            / "skills"
            / "econcs-formalizer"
            / "templates"
            / "FINAL_ADVERSARIAL_SOURCE_AUDIT_PROMPT.md"
        ).read_text(encoding="utf-8")

        self.assertIn("Default-out-of-scope prose cannot support a `FAIL`", prompt)
        self.assertIn(
            "repair is demotion to deep-audit or\nsupporting context",
            prompt,
        )

    def test_final_adversary_treats_prior_terminal_credentials_as_precredential(self) -> None:
        prompt = (
            ROOT
            / "skills"
            / "econcs-formalizer"
            / "templates"
            / "FINAL_ADVERSARIAL_SOURCE_AUDIT_PROMPT.md"
        ).read_text(encoding="utf-8")

        self.assertIn("historical pre-credential evidence", prompt)
        self.assertIn(
            "Do not report that fact as a finding.",
            prompt,
        )

    def manifest_protocol(self) -> dict[str, object]:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        baseline = payload["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]
        baseline.clear()
        baseline.update(
            {
                "authority": IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
                "manifest_path": "config/legacy_v10_material_identity_manifest.json",
                "manifest_sha256": "a" * 64,
                "manifest_schema": IMMUTABLE_V10_TRUST_LEDGER_SCHEMA,
                "material_identity_schema": IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
                "engine_id": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID,
                "engine_schema": IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
                "rule": "Use the immutable semantic trust ledger.",
            }
        )
        return payload

    def test_repository_protocol_is_valid_and_unambiguous(self) -> None:
        payload = load_formalization_protocol()

        self.assertEqual(payload["audit_versions"]["statement_semantic_review"]["current"], "v11")
        self.assertEqual(payload["audit_versions"]["source_record"]["current"], "v10")
        self.assertEqual(payload["audit_versions"]["theorem_realization"]["current"], "v11")
        baseline = payload["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]
        if baseline["authority"] == IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY:
            self.assertEqual(
                baseline["manifest_schema"], IMMUTABLE_V10_TRUST_LEDGER_SCHEMA
            )
            self.assertEqual(
                baseline["material_identity_schema"],
                IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
            )
            self.assertEqual(
                baseline["engine_id"], IMMUTABLE_V10_TRUST_LEDGER_ENGINE_ID
            )
            self.assertEqual(
                baseline["engine_schema"],
                IMMUTABLE_V10_TRUST_LEDGER_ENGINE_SCHEMA,
            )
        else:
            self.assertEqual(
                baseline["git_commit"],
                EXPECTED_LEGACY_V10_TRANSITION_BASELINE_COMMIT,
            )
            self.assertEqual(
                baseline["trusted_ref"],
                EXPECTED_LEGACY_V10_TRANSITION_TRUSTED_REF,
            )
            self.assertEqual(baseline["material_identity_schema"], 1)
        normal = payload["coverage"]["normal_mode"]
        self.assertTrue(
            {"formula", "equation", "algorithm", "algorithmic_formula"}
            <= set(normal["deep_only_standalone_source_kinds"])
        )
        self.assertEqual(payload["reuse"]["granularity"], "item")
        identities = set(payload["reuse"]["required_unchanged_identities"])
        self.assertIn(
            "name_independent_elaborated_statement_structure_and_semantic_proposition",
            identities,
        )
        self.assertNotIn("raw_lean_statement", identities)
        self.assertIn(
            "raw_lean_declaration_spelling_after_unique_semantic_match",
            payload["reuse"]["navigation_only"],
        )
        clean_diagnostics = payload["builds"]["clean_diagnostics"]
        self.assertEqual(
            clean_diagnostics["max_output_bytes"],
            EXPECTED_CLEAN_LEAN_OUTPUT_BYTES,
        )
        self.assertEqual(
            set(clean_diagnostics["reject_on"]),
            EXPECTED_LEAN_DIAGNOSTIC_FAILURES,
        )

    def test_protocol_rejects_standalone_equation_in_normal_scope(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        broken = deepcopy(payload)
        broken["coverage"]["normal_mode"]["included_source_kinds"].append(
            "equation"
        )

        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

        broken = deepcopy(payload)
        broken["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]["trusted_ref"] = "refs/heads/main"
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

    def test_protocol_requires_transitive_dependency_reuse_identity(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        broken = deepcopy(payload)
        broken["reuse"]["required_unchanged_identities"].remove(
            "transitive_elaborated_semantic_dependency_graph"
        )

        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

    def test_protocol_rejects_raw_lean_spelling_as_semantic_identity(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        broken = deepcopy(payload)
        broken["reuse"]["required_unchanged_identities"].append(
            "raw_lean_statement"
        )

        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

    def test_protocol_digest_is_canonical_and_content_sensitive(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        reordered = {
            key: payload[key]
            for key in reversed(list(payload))
        }
        self.assertEqual(
            formalization_protocol_digest(payload),
            formalization_protocol_digest(reordered),
        )

        changed = deepcopy(payload)
        changed["pacing"]["rule"] += " Material policy change."
        self.assertNotEqual(
            formalization_protocol_digest(payload),
            formalization_protocol_digest(changed),
        )

    def test_protocol_digest_observes_same_process_file_change(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "protocol.json"
            with mock.patch.object(protocol_module, "PROTOCOL_PATH", path):
                path.write_text(json.dumps(payload), encoding="utf-8")
                first = protocol_module.formalization_protocol_digest()
                changed = deepcopy(payload)
                changed["pacing"]["rule"] += " Changed in the same process."
                path.write_text(json.dumps(changed), encoding="utf-8")
                second = protocol_module.formalization_protocol_digest()

        self.assertNotEqual(first, second)

    def test_scoped_protocol_digests_follow_operational_invalidation_boundaries(
        self,
    ) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        coverage = formalization_coverage_protocol_digest(payload)
        review = formalization_review_protocol_digest(payload)

        for section, field in (
            ("builds", "proof_iteration"),
            ("pacing", "rule"),
            ("authority", "scope"),
        ):
            with self.subTest(nonoperative=f"{section}.{field}"):
                changed = deepcopy(payload)
                changed[section][field] += " Edited without changing policy."
                self.assertEqual(
                    formalization_coverage_protocol_digest(changed), coverage
                )
                self.assertEqual(formalization_review_protocol_digest(changed), review)

        prose = deepcopy(payload)
        prose["coverage"]["normal_mode"]["rule"] += " Clarified wording."
        prose["classification"]["additional_assumption"]["rule"] += (
            " Clarified wording."
        )
        prose["audit_versions"]["source_record"]["meaning"] += (
            " Clarified wording."
        )
        self.assertEqual(formalization_coverage_protocol_digest(prose), coverage)
        self.assertEqual(formalization_review_protocol_digest(prose), review)

        # v11 transition scheduling changes whether a future closeout enters
        # the optional correspondence lane; it cannot invalidate an existing
        # v10 source-obligation extraction or semantic judgment.
        transition_schedule = deepcopy(payload)
        transition = transition_schedule["audit_versions"]["theorem_realization"]
        transition["required_for"] = list(reversed(transition["required_for"]))
        transition["transition"] += " Clarified migration scheduling."
        transition["legacy_v10_transition_baseline"]["rule"] += (
            " Clarified migration scheduling."
        )
        self.assertEqual(
            formalization_coverage_protocol_digest(transition_schedule), coverage
        )
        self.assertEqual(formalization_review_protocol_digest(transition_schedule), review)

        material_review = deepcopy(payload)
        material_review["reuse"]["operational_review_epoch"] = "v2"
        self.assertEqual(
            formalization_coverage_protocol_digest(material_review), coverage
        )
        self.assertNotEqual(
            formalization_review_protocol_digest(material_review), review
        )

        coverage_change = deepcopy(payload)
        coverage_change["coverage"]["selection_semantics_epoch"] = "v2"
        self.assertNotEqual(
            formalization_coverage_protocol_digest(coverage_change), coverage
        )
        self.assertNotEqual(
            formalization_review_protocol_digest(coverage_change), review
        )

    def test_item_review_digest_excludes_scope_and_scheduling_policy(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        item_review = formalization_item_review_protocol_digest(payload)

        changed_scope = deepcopy(payload)
        changed_scope["coverage"]["selection_semantics_epoch"] = "v2"
        changed_scope["coverage"]["review_intensity"]["override"] += (
            " Clarified scheduling language."
        )
        self.assertEqual(
            formalization_item_review_protocol_digest(changed_scope), item_review
        )

        changed_semantics = deepcopy(payload)
        changed_semantics["reuse"]["operational_review_epoch"] = "v2"
        self.assertNotEqual(
            formalization_item_review_protocol_digest(changed_semantics), item_review
        )

    def test_closeout_review_policy_has_separate_assurance_material_and_schedule(self) -> None:
        policy = resolve_closeout_review_policy()
        self.assertEqual(
            policy.source_scope, CLOSEOUT_REVIEW_POLICY_DEFAULT_SOURCE_SCOPE
        )
        self.assertEqual(
            policy.repeat_final_scope, CLOSEOUT_REVIEW_POLICY_DEFAULT_REPEAT_SCOPE
        )
        material = closeout_review_policy_material_projection(policy)
        assurance = closeout_review_policy_assurance_projection(policy)
        schedule = closeout_review_policy_scheduling_projection(policy)
        self.assertNotIn("required_final_adversary_count", material)
        self.assertEqual(assurance["required_final_adversary_count"], 1)
        self.assertNotIn("required_final_adversary_count", schedule)

        changed = policy.projection()
        changed["required_final_adversary_count"] = 2
        changed["scheduling"]["final_adversarial_review"] = ["reviewer-b"]
        resolved = resolve_closeout_review_policy(changed)
        self.assertEqual(
            closeout_review_policy_material_projection(resolved), material
        )
        self.assertNotEqual(
            closeout_review_policy_assurance_projection(resolved), assurance
        )
        self.assertNotEqual(
            closeout_review_policy_scheduling_projection(resolved), schedule
        )
        self.assertEqual(
            resolve_closeout_review_policy_assurance(assurance), policy
        )

    def test_closeout_policy_rejects_boolean_schema_aliases(self) -> None:
        policy = resolve_closeout_review_policy().projection()
        policy["schema"] = True
        with self.assertRaisesRegex(FormalizationProtocolError, "schema must be 1"):
            resolve_closeout_review_policy(policy)

        limited = resolve_closeout_review_policy().projection()
        limited["source_scope"] = "main_named_theory"
        limited["repeat_final_scope"] = "all_selected"
        limited["scope_approval"] = {
            "schema": True,
            "approval_kind": "explicit_user_instruction",
            "approval_reference": "User explicitly approved main named theory only.",
            "approved_at": "2026-09-05T12:00:00Z",
        }
        with self.assertRaisesRegex(FormalizationProtocolError, "schema must be 1"):
            resolve_closeout_review_policy(limited)

    def test_limited_main_scope_requires_one_exact_user_approval(self) -> None:
        value = resolve_closeout_review_policy().projection()
        value["source_scope"] = "main_named_theory"
        value["repeat_final_scope"] = "all_selected"
        with self.assertRaises(FormalizationProtocolError):
            resolve_closeout_review_policy(value)

        value["scope_approval"] = {
            "schema": 1,
            "approval_kind": "explicit_user_instruction",
            "approval_reference": "User explicitly approved main named theory only.",
            "approved_at": "2026-09-05T12:00:00Z",
        }
        self.assertEqual(
            resolve_closeout_review_policy(value).source_scope,
            "main_named_theory",
        )

    def test_review_intensity_tier_contract_fails_closed(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        for mutation in ("missing", "typo", "wrong_tier"):
            with self.subTest(mutation=mutation):
                changed = deepcopy(payload)
                intensity = changed["coverage"]["review_intensity"]
                if mutation == "missing":
                    del intensity["appendix_baseline"]
                elif mutation == "typo":
                    intensity["default"] = "main_primary"
                else:
                    intensity["appendix_baseline"]["required"] = [
                        "final_adversarial_source_audit"
                    ]
                with self.assertRaises(FormalizationProtocolError):
                    validate_formalization_protocol(changed)

    def test_scoped_receipt_compatibility_is_current_only_and_fail_closed(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        self.assertTrue(
            formalization_protocol_receipt_matches(
                {
                    FORMALIZATION_COVERAGE_PROTOCOL_FIELD: (
                        formalization_coverage_protocol_digest(payload)
                    )
                },
                scope="coverage",
                payload=payload,
            )
        )
        self.assertTrue(
            formalization_protocol_receipt_matches(
                {
                    FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                        formalization_review_protocol_digest(payload)
                    )
                },
                scope="review",
                payload=payload,
            )
        )
        legacy = {"formalization_protocol_sha256": formalization_protocol_digest(payload)}
        self.assertTrue(
            formalization_protocol_receipt_matches(
                legacy, scope="review", payload=payload
            )
        )

        changed = deepcopy(payload)
        changed["pacing"]["rule"] += " Administrative edit."
        self.assertFalse(
            formalization_protocol_receipt_matches(
                legacy, scope="review", payload=changed
            )
        )
        malformed_scoped_with_valid_legacy = {
            **legacy,
            FORMALIZATION_REVIEW_PROTOCOL_FIELD: "not-a-digest",
        }
        self.assertFalse(
            formalization_protocol_receipt_matches(
                malformed_scoped_with_valid_legacy,
                scope="review",
                payload=payload,
            )
        )

    def test_judgment_review_receipt_selects_scoped_sidecar_or_legacy_raw(
        self,
    ) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        coverage_scoped_raw = {
            FORMALIZATION_COVERAGE_PROTOCOL_FIELD: (
                formalization_coverage_protocol_digest(payload)
            )
        }
        self.assertFalse(
            formalization_judgment_review_protocol_is_current(
                coverage_scoped_raw, {}, payload=payload
            )
        )
        current_sidecar = {
            FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                formalization_review_protocol_digest(payload)
            )
        }
        self.assertTrue(
            formalization_judgment_review_protocol_is_current(
                coverage_scoped_raw, current_sidecar, payload=payload
            )
        )
        stale_sidecar = {
            FORMALIZATION_REVIEW_PROTOCOL_FIELD: "0" * 64,
        }
        self.assertFalse(
            formalization_judgment_review_protocol_is_current(
                coverage_scoped_raw, stale_sidecar, payload=payload
            )
        )
        legacy_raw = {
            "formalization_protocol_sha256": formalization_protocol_digest(payload)
        }
        self.assertTrue(
            formalization_judgment_review_protocol_is_current(
                legacy_raw, {}, payload=payload
            )
        )
        self.assertTrue(
            formalization_judgment_review_protocol_is_current(
                {}, {}, payload=payload
            )
        )

    def test_portable_manifest_authority_is_central_and_self_cycle_free(self) -> None:
        git_protocol = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        manifest_protocol = self.manifest_protocol()

        validated = validate_formalization_protocol(manifest_protocol)

        baseline = validated["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]
        self.assertEqual(
            baseline["authority"],
            IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
        )
        # Authority coordinates and the raw manifest digest are excluded from
        # the semantic protocol identity, preventing a config/manifest cycle.
        self.assertEqual(
            formalization_material_protocol_digest(git_protocol),
            formalization_material_protocol_digest(manifest_protocol),
        )
        changed_digest = deepcopy(manifest_protocol)
        changed_digest["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]["manifest_sha256"] = "b" * 64
        self.assertEqual(
            formalization_material_protocol_digest(manifest_protocol),
            formalization_material_protocol_digest(changed_digest),
        )

        changed_prose = deepcopy(manifest_protocol)
        changed_prose["classification"]["source_condition_or_refinement"][
            "rule"
        ] += " Clarified prose only."
        self.assertEqual(
            formalization_material_protocol_digest(manifest_protocol),
            formalization_material_protocol_digest(changed_prose),
        )

        changed_policy = deepcopy(manifest_protocol)
        changed_policy["classification"]["source_condition_or_refinement"][
            "operational_review_epoch"
        ] = "v2"
        self.assertNotEqual(
            formalization_material_protocol_digest(manifest_protocol),
            formalization_material_protocol_digest(changed_policy),
        )

    def test_portable_manifest_authority_rejects_unsafe_or_stale_coordinates(self) -> None:
        payload = self.manifest_protocol()
        mutations = (
            ("manifest_path", "../private/ledger.json"),
            ("manifest_sha256", "not-a-digest"),
            ("manifest_schema", 999),
            ("material_identity_schema", 999),
            ("engine_id", "paper-specific-engine"),
            ("engine_schema", 999),
        )
        for field, value in mutations:
            with self.subTest(field=field):
                broken = deepcopy(payload)
                broken["audit_versions"]["theorem_realization"][
                    "legacy_v10_transition_baseline"
                ][field] = value
                with self.assertRaises(FormalizationProtocolError):
                    validate_formalization_protocol(broken)

        broken = deepcopy(payload)
        broken["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]["git_commit"] = "0" * 40
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

    def test_loaded_protocol_is_not_shared_mutable_state(self) -> None:
        first = load_formalization_protocol()
        first["reuse"]["granularity"] = "whole_repository"
        second = load_formalization_protocol()

        self.assertEqual(second["reuse"]["granularity"], "item")

    def test_protocol_rejects_every_authoritative_prompt_drift(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        for lane in ("statement_semantic_review", "source_record"):
            with self.subTest(lane=lane):
                broken = deepcopy(payload)
                broken["audit_versions"][lane]["prompt_version"] += "-weaker"
                with self.assertRaises(FormalizationProtocolError):
                    validate_formalization_protocol(broken)

    def test_protocol_validates_complete_reuse_identity_contract(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        for identity in EXPECTED_REQUIRED_REUSE_IDENTITIES:
            with self.subTest(identity=identity):
                broken = deepcopy(payload)
                broken["reuse"]["required_unchanged_identities"].remove(identity)
                with self.assertRaises(FormalizationProtocolError):
                    validate_formalization_protocol(broken)
        broken = deepcopy(payload)
        broken["reuse"]["required_unchanged_identities"].append(
            "sidecar_declared_compatibility"
        )
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

    def test_protocol_validates_complete_fail_closed_contract(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        for failure in EXPECTED_REUSE_FAILURES:
            with self.subTest(failure=failure):
                broken = deepcopy(payload)
                broken["reuse"]["fail_closed_on"].remove(failure)
                with self.assertRaises(FormalizationProtocolError):
                    validate_formalization_protocol(broken)
        broken = deepcopy(payload)
        broken["reuse"]["fail_closed_on"].append("best_effort_fallback")
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)
        broken = deepcopy(payload)
        broken["reuse"]["fail_closed_on"].append(" missing_identity ")
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

    def test_protocol_rejects_contradictory_lane_payload(self) -> None:
        payload = json.loads(PROTOCOL_PATH.read_text(encoding="utf-8"))
        broken = deepcopy(payload)
        broken["audit_versions"]["theorem_realization"]["prompt_version"] = (
            "sidecar-selected-v11"
        )
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

        broken = deepcopy(payload)
        broken["audit_versions"]["theorem_realization"][
            "legacy_v10_transition_baseline"
        ]["git_commit"] = "0" * 40
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

        broken = deepcopy(payload)
        broken["audit_versions"]["theorem_realization"]["required_for"] = [
            "new_paper_closeout",
            "materially_reissued_closeout",
        ]
        with self.assertRaises(FormalizationProtocolError):
            validate_formalization_protocol(broken)

    def test_core_agent_docs_defer_to_protocol(self) -> None:
        protocol_reference = "config/formalization_audit_protocol.json"
        for relative in (
            "docs/AGENT_FORMALIZATION_WORKFLOW.md",
            "docs/FORMALIZATION_PROOF_OBLIGATION_HANDOFF_2026-07-10.md",
            "docs/FORMALIZATION_STATUS_POLICY.md",
            "docs/INDEPENDENT_AUDIT_GUIDE.md",
            "docs/VALIDATION_MODEL.md",
            "skills/econcs-formalizer/SKILL.md",
            "skills/econcs-formalizer/references/post-formalization-closeout.md",
        ):
            with self.subTest(relative=relative):
                path = ROOT / relative
                if not path.exists():
                    continue
                text = path.read_text(encoding="utf-8")
                self.assertIn(protocol_reference, text)
                self.assertIn("normative", text.lower())

    def test_dated_obligation_handoff_uses_the_planner_for_closeout(self) -> None:
        """Keep the maintained handoff from restoring a redundant command batch."""

        handoff_path = (
            ROOT / "docs" / "FORMALIZATION_PROOF_OBLIGATION_HANDOFF_2026-07-10.md"
        )
        if not handoff_path.exists():
            return
        handoff = handoff_path.read_text(encoding="utf-8")
        self.assertIn("## Current Verification Route", handoff)
        self.assertIn(
            "python3 scripts/closeout_reuse_plan.py --paper <PaperId>", handoff
        )
        self.assertIn("Execute only the planner's `next_action`", handoff)
        self.assertNotIn(
            "python3 scripts/audit_repository.py --paper <PaperId> "
            "--paper-closeout --include-active --info-limit 0\n",
            handoff,
        )

    def test_live_closeout_entrypoints_distinguish_diagnostics_from_closeout(
        self,
    ) -> None:
        """Keep live guides from restoring an eager pre-closeout command batch."""

        required_phrases = {
            "skills/econcs-formalizer/references/audit-and-closeout.md": (
                "python3 scripts/closeout_reuse_plan.py --paper <PaperRoot>",
                "Execute the returned `next_action`",
                "Do not call a lower-level producer",
                "Do not run concurrent Lake builds in one worktree.",
            ),
            "docs/AGENT_FORMALIZATION_WORKFLOW.md": (
                "Execute only its current `next_action`",
                "not a routine frozen-closeout precursor",
            ),
            "docs/INDEPENDENT_AUDIT_GUIDE.md": (
                "python3 scripts/closeout_reuse_plan.py --paper <Paper>",
                "planner route owns the accepting transaction",
            ),
            "docs/REVIEW_DASHBOARD.md": (
                "frozen-closeout command sequence",
                "Do not run that producer by hand as a frozen-closeout prelude.",
            ),
            "skills/econcs-formalizer/SKILL.md": (
                "only when a named diagnostic or planner action",
                "python3 scripts/closeout_reuse_plan.py --paper <PaperRoot>",
            ),
            "skills/econcs-formalizer/references/formalization-handbook.md": (
                "source-record producer by hand as a closeout predecessor",
                "frozen closeout, begin with the planner",
            ),
            "skills/econcs-formalizer/references/public-private-sync.md": (
                "not a normal frozen-paper",
                "Row names are navigation",
            ),
        }
        for relative, phrases in required_phrases.items():
            with self.subTest(relative=relative):
                text = (ROOT / relative).read_text(encoding="utf-8")
                for phrase in phrases:
                    self.assertIn(phrase, text)

        private_history_phrases = {
            "papers/TEMPLATE/docs/FORMALIZATION_NOTES.md": (
                "not a frozen-closeout",
                "python3 scripts/closeout_reuse_plan.py --paper TEMPLATE",
            ),
            "skills/econcs-formalizer/references/post-formalization-closeout.md": (
                "sole normal closeout",
                "do not run the producer by hand",
            ),
        }
        for relative, phrases in private_history_phrases.items():
            with self.subTest(private_history=relative):
                path = ROOT / relative
                if not path.exists():
                    continue
                text = path.read_text(encoding="utf-8")
                for phrase in phrases:
                    self.assertIn(phrase, text)


if __name__ == "__main__":
    unittest.main()
