#!/usr/bin/env python3
"""Focused regressions for the exact semantic-contract closeout bridge."""

from __future__ import annotations

import hashlib
import inspect
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

from scripts import audit_evidence_integrity as integrity  # noqa: E402
from scripts import audit_repository  # noqa: E402
from scripts import lean_signature_manifest  # noqa: E402
from scripts import review_dashboard  # noqa: E402
from scripts import source_named_result_index  # noqa: E402
from scripts.source_record_integrity import (  # noqa: E402
    stamp_source_record_audit_receipts,
)


class SemanticContractCloseoutBridgeTests(unittest.TestCase):
    def setUp(self) -> None:
        legacy_transition = mock.patch(
            "scripts.theorem_realization_transition.theorem_realization_reissue_requirement",
            return_value=mock.Mock(
                required=False,
                reason="unchanged legacy fixture",
            ),
        )
        legacy_transition.start()
        self.addCleanup(legacy_transition.stop)
        foreign_scope = mock.patch(
            "scripts.lean_signature_manifest.foreign_model_definition_scope",
            return_value=((), (), ""),
        )
        foreign_scope.start()
        self.addCleanup(foreign_scope.stop)
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.paper = Path(self.temporary.name) / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self.source = self.paper / "source.txt"
        # Ordinary coverage is presentation-first: retain a visibly numbered
        # theorem rather than relying on the map's `source_kind` metadata.
        self.source_text = "Theorem 1. States the exact audited property.\n"
        self.source.write_text(self.source_text, encoding="utf-8")
        self.source_digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        self.quote = self.source_text.rstrip("\n")
        self.quote_digest = hashlib.sha256(self.quote.encode("utf-8")).hexdigest()
        (self.paper / "PaperInterface.lean").write_text(
            "namespace Fixture\n"
            "abbrev sourceShape : Prop := (0 : Nat) = 0\n"
            "theorem proofRoute : sourceShape := rfl\n"
            "end Fixture\n",
            encoding="utf-8",
        )
        self.write_status()

    def write_status(self, status: str = "formalized") -> None:
        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "status": status,
                    "review_surface": {
                        "include_names": ["sourceShape", "proofRoute"],
                        "assumption_names": [],
                    },
                }
            ),
            encoding="utf-8",
        )

    def source_anchor(self) -> list[dict[str, object]]:
        return [
            {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": self.quote,
                "quoted_text_sha256": self.quote_digest,
            }
        ]

    def contract_item(self) -> dict[str, object]:
        return {
            "statement": "The source theorem's exact audited property.",
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_location": "source.txt:1",
            "source_anchor_evidence": self.source_anchor(),
            "semantic_contract": {
                "spec_declaration": "Fixture.sourceShape",
                "evidence_declaration": "Fixture.proofRoute",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }

    def write_map(self, items: dict[str, dict[str, object]]) -> None:
        named_result_digest = integrity.named_result_presentations_sha256(
            source_named_result_index.extract_named_result_presentations(
                self.source.read_text(encoding="utf-8"), source_format="text"
            )
        )
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "source_coverage_mode": "named_theoretical_statements",
                    "source_curated": True,
                    "source_inventory_kind": "atomic_source_inventory",
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": self.source_digest,
                    "source_anchor_evidence_required": True,
                    "source_named_result_inventory_review": {
                        "schema": 1,
                        "complete": True,
                        "validator": "fixture-reviewer",
                        "validated_at": "2026-07-26",
                        "method": "fixture named-result source scan",
                        "source_artifact_sha256": self.source_digest,
                        "discovered_named_result_sha256": named_result_digest,
                        "prose_definition_presentations": [],
                        "discovered_prose_definition_sha256": hashlib.sha256(
                            b"[]"
                        ).hexdigest(),
                    },
                    "semantic_contract_schema": 1,
                    "items": items,
                }
            ),
            encoding="utf-8",
        )

    def terminal_transparency(self) -> dict[str, object]:
        """One structurally complete executable-recursion Meta receipt."""

        return {
            "passes": False,
            "failure_tag": "recursive_executable_terminal",
            "failure_declaration": "Fixture.executor",
            "expanded": 1,
            "recursive_executable_terminals": [
                {
                    "declaration": "Fixture.executor",
                    "occurrence_path": ["spec_body", "application"],
                    "application_arity": 1,
                    "application_result_type": "Nat",
                    "normalized_result_type": "Nat",
                }
            ],
        }

    def terminal_policy_context(
        self,
        *,
        snapshot_status: dict[str, object],
        snapshot_map: dict[str, object],
        evidence_status: dict[str, object] | None = None,
        evidence_map: dict[str, object] | None = None,
    ) -> audit_repository.PaperCloseoutRunContext:
        """Build a fault-injection transaction used only before raw-audit access."""

        status_path = self.paper / "status.json"
        map_path = self.audit / "paper_statement_map.json"
        fake_evidence = mock.Mock(
            folder=self.paper.resolve(),
            issued_by_builder=True,
            status_payload=(
                evidence_status if evidence_status is not None else snapshot_status
            ),
            statement_map=(evidence_map if evidence_map is not None else snapshot_map),
            audit_payload=None,
            input_snapshots=(
                mock.Mock(path=status_path, payload=snapshot_status),
                mock.Mock(path=map_path, payload=snapshot_map),
            ),
        )
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            return audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
                "FixturePaper", self.paper, evidence_context=fake_evidence
            )

    def test_terminal_bridge_rejects_unissued_context_and_exposes_no_sidecars(self) -> None:
        """No caller can authorize a terminal with live/raw sidecar arguments."""

        parameters = inspect.signature(
            audit_repository.semantic_contract_executable_terminal_policy_errors
        ).parameters
        self.assertEqual(
            set(parameters),
            {"paper_id", "folder", "source_key", "transparency", "run_context"},
        )
        candidate = self.terminal_transparency()
        with mock.patch.object(
            audit_repository,
            "load_json_object",
            side_effect=AssertionError("unissued terminal policy must not read live JSON"),
        ):
            missing = audit_repository.semantic_contract_executable_terminal_policy_errors(
                "FixturePaper",
                self.paper,
                source_key="opaque_source_atom",
                transparency=candidate,
                run_context=None,
            )
            mixed = audit_repository.semantic_contract_executable_terminal_policy_errors(
                "OtherPaper",
                self.paper,
                source_key="opaque_source_atom",
                transparency=candidate,
                run_context=audit_repository.PaperCloseoutRunContext(
                    "FixturePaper", self.paper
                ),
            )
        self.assertEqual(len(missing), 1)
        self.assertIn("exact builder-issued closeout context", missing[0])
        self.assertEqual(len(mixed), 1)
        self.assertIn("exact builder-issued closeout context", mixed[0])

        fake_evidence = mock.Mock(
            folder=self.paper.resolve(), issued_by_builder=True, audit_payload=None
        )
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            directly_wrapped = audit_repository.PaperCloseoutRunContext(
                "FixturePaper", self.paper, evidence_context=fake_evidence
            )
            direct_errors = audit_repository.semantic_contract_executable_terminal_policy_errors(
                "FixturePaper",
                self.paper,
                source_key="opaque_source_atom",
                transparency=candidate,
                run_context=directly_wrapped,
            )
        self.assertFalse(directly_wrapped.issued_by_builder)
        self.assertEqual(len(direct_errors), 1)
        self.assertIn("exact builder-issued closeout context", direct_errors[0])

    def test_terminal_bridge_rejects_mixed_transaction_snapshots(self) -> None:
        """A stale or mixed status/map snapshot cannot enter the terminal bridge."""

        self.write_map({"opaque_source_atom": self.contract_item()})
        snapshot_status = json.loads((self.paper / "status.json").read_text(encoding="utf-8"))
        snapshot_map = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        context = self.terminal_policy_context(
            snapshot_status=snapshot_status,
            snapshot_map=snapshot_map,
            evidence_status={"status": "partially formalized"},
        )
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            errors = audit_repository.semantic_contract_executable_terminal_policy_errors(
                "FixturePaper",
                self.paper,
                source_key="opaque_source_atom",
                transparency=self.terminal_transparency(),
                run_context=context,
            )
        self.assertEqual(len(errors), 1)
        self.assertIn("snapshot does not match its evidence transaction", errors[0])

    def test_terminal_bridge_rejects_caller_transparency_injection(self) -> None:
        """The bridge recomputes transparency from transaction-owned Lean inputs."""

        self.write_map({"opaque_source_atom": self.contract_item()})
        snapshot_status = json.loads((self.paper / "status.json").read_text(encoding="utf-8"))
        snapshot_map = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        context = self.terminal_policy_context(
            snapshot_status=snapshot_status,
            snapshot_map=snapshot_map,
        )
        injected = self.terminal_transparency()
        injected["failure_declaration"] = "Fixture.injected"
        exact = self.terminal_transparency()
        with (
            mock.patch.object(
                audit_repository, "exact_evidence_run_context", return_value=True
            ),
            mock.patch.object(context, "exact_lean_source_text", return_value="fixture"),
            mock.patch.object(
                lean_signature_manifest,
                "paper_local_module_names",
                return_value=set(),
            ),
            mock.patch.object(
                lean_signature_manifest,
                "run_lean_semantic_contract_transparency_checks",
                return_value={"Fixture.sourceShape": exact},
            ),
        ):
            errors = audit_repository.semantic_contract_executable_terminal_policy_errors(
                "FixturePaper",
                self.paper,
                source_key="opaque_source_atom",
                transparency=injected,
                run_context=context,
            )
        self.assertEqual(len(errors), 1)
        self.assertIn("caller-supplied executable-recursion transparency differs", errors[0])

    def test_repeated_source_presentation_does_not_require_a_second_lean_route(
        self,
    ) -> None:
        """A source-only duplicate relation is not a route-name waiver."""

        self.write_map(
            {
                "canonical_theorem": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:1",
                    "lean_declarations": ["Fixture.proofRoute"],
                },
                "appendix_restatement": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:2",
                    "source_presentation_alias": {
                        "schema": 1,
                        "relation": "repeated_source_presentation",
                        "canonical_source_item": "canonical_theorem",
                        "semantic_basis": (
                            "The separately pinned source presentations have the "
                            "same displayed hypotheses, scope, and conclusion."
                        ),
                        "validator": "fixture source-only reconciliation",
                        "validated_at": "2026-07-27T12:00:00Z",
                    },
                },
            }
        )

        findings = audit_repository.paper_statement_map_declaration_findings(
            "FixturePaper", self.paper, "formalized"
        )

        self.assertEqual(findings, [])

    def test_malformed_repeated_presentation_alias_remains_an_error(self) -> None:
        self.write_map(
            {
                "canonical_theorem": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:1",
                    "lean_declarations": ["Fixture.proofRoute"],
                },
                "appendix_restatement": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:2",
                    "lean_declarations": ["Fixture.proofRoute"],
                    "source_presentation_alias": {
                        "schema": 1,
                        "relation": "repeated_source_presentation",
                        "canonical_source_item": "canonical_theorem",
                        "semantic_basis": "fixture source-only reconciliation",
                        "validator": "fixture source-only reconciliation",
                        "validated_at": "2026-07-27T12:00:00Z",
                    },
                },
            }
        )

        messages = [
            finding.message
            for finding in audit_repository.paper_statement_map_declaration_findings(
                "FixturePaper", self.paper, "formalized"
            )
        ]

        self.assertTrue(
            any("invalid repeated-presentation alias metadata" in message for message in messages),
            messages,
        )

    def test_exact_source_anchored_contract_is_bridge_eligible(self) -> None:
        self.write_map({"opaque_source_atom": self.contract_item()})

        inventory, findings = integrity.semantic_contract_closeout_bridge_inventory(
            self.paper, "formalized"
        )

        self.assertEqual(findings, [])
        assert inventory is not None
        self.assertEqual(inventory.contract_item_keys, ("opaque_source_atom",))
        self.assertEqual(inventory.scope_exclusion_item_keys, ())

        route = ("Fixture.sourceShape", "Fixture.proofRoute", "proves")
        transparent = {
            "Fixture.sourceShape": {
                "passes": True,
                "failure_tag": "",
                "failure_declaration": "",
                "expanded": 0,
            }
        }
        with mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_matches",
            return_value={route: True},
        ), mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_transparency_checks",
            return_value=transparent,
        ), mock.patch.object(
            lean_signature_manifest,
            "foreign_model_definition_scope",
            return_value=((), (), ""),
        ):
            self.assertTrue(
                audit_repository.semantic_contract_closeout_bridge_is_current(
                    "FixturePaper",
                    self.paper,
                    "formalized",
                    json.loads((self.paper / "status.json").read_text(encoding="utf-8")),
                )
            )
        with mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_matches",
            return_value={route: False},
        ), mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_transparency_checks",
            return_value=transparent,
        ):
            self.assertFalse(
                audit_repository.semantic_contract_closeout_bridge_is_current(
                    "FixturePaper",
                    self.paper,
                    "formalized",
                    json.loads((self.paper / "status.json").read_text(encoding="utf-8")),
                )
            )

    def test_invalid_strict_inventory_fails_before_legacy_lean_replay(self) -> None:
        """An inventory error is not repaired by expensive legacy programs."""

        self.write_map({"opaque_source_atom": self.contract_item()})
        payload = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        declarations = audit_repository.paper_lean_declaration_index(self.paper)
        transparency = mock.Mock(
            side_effect=AssertionError("invalid inventory must fail before Lean")
        )
        matches = mock.Mock(
            side_effect=AssertionError("invalid inventory must fail before Lean")
        )
        with (
            mock.patch.object(
                audit_repository,
                "source_spec_correspondence_requested",
                return_value=True,
            ),
            mock.patch.object(
                integrity, "semantic_contract_inventory_findings", return_value=[]
            ),
            mock.patch.object(
                audit_repository,
                "semantic_contract_closeout_bridge_inventory",
                return_value=(None, [mock.Mock()]),
            ),
            mock.patch.object(
                lean_signature_manifest,
                "run_lean_semantic_contract_transparency_checks",
                transparency,
            ),
            mock.patch.object(
                lean_signature_manifest,
                "run_lean_semantic_contract_matches",
                matches,
            ),
        ):
            findings = audit_repository.paper_statement_map_semantic_contract_findings(
                "FixturePaper",
                self.paper,
                "formalized",
                payload,
                declarations,
                set(),
                json.loads((self.paper / "status.json").read_text(encoding="utf-8")),
            )

        self.assertEqual(len(findings), 1)
        self.assertIn("strict source-to-Spec inventory is unavailable", findings[0].message)
        transparency.assert_not_called()
        matches.assert_not_called()

    def test_complete_contract_pass_is_reused_only_in_issuing_transaction(self) -> None:
        """The second bridge consumer cannot replay or fabricate a prior pass."""

        self.write_map({"opaque_source_atom": self.contract_item()})
        snapshot_status = json.loads(
            (self.paper / "status.json").read_text(encoding="utf-8")
        )
        snapshot_map = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        context = self.terminal_policy_context(
            snapshot_status=snapshot_status,
            snapshot_map=snapshot_map,
        )
        with mock.patch.object(
            audit_repository, "exact_evidence_run_context", return_value=True
        ):
            context.record_semantic_contract_closeout_bridge(
                {"opaque_source_atom"}
            )
            self.assertEqual(
                context.current_semantic_contract_closeout_bridge_scope_keys(),
                (),
            )
            context.record_semantic_contract_closeout_bridge(
                {"opaque_source_atom"},
                _issuer=audit_repository._SEMANTIC_CONTRACT_CLOSEOUT_BRIDGE_ISSUER,
            )
            with mock.patch.object(
                integrity,
                "semantic_contract_closeout_bridge_inventory",
                side_effect=AssertionError("complete transaction pass should be reused"),
            ):
                self.assertTrue(
                    audit_repository.semantic_contract_closeout_bridge_is_current(
                        "FixturePaper",
                        self.paper,
                        "formalized",
                        snapshot_status,
                        run_context=context,
                    )
                )

        unissued = audit_repository.PaperCloseoutRunContext(
            "FixturePaper", self.paper
        )
        unissued.record_semantic_contract_closeout_bridge(
            {"opaque_source_atom"},
            _issuer=audit_repository._SEMANTIC_CONTRACT_CLOSEOUT_BRIDGE_ISSUER,
        )
        self.assertEqual(
            unissued.current_semantic_contract_closeout_bridge_scope_keys(),
            (),
        )

    def test_precloseout_pairs_require_partial_status_and_current_exact_contracts(self) -> None:
        self.write_status("partially formalized")
        self.write_map({"opaque_source_atom": self.contract_item()})
        status_payload = json.loads((self.paper / "status.json").read_text(encoding="utf-8"))
        route = ("Fixture.sourceShape", "Fixture.proofRoute", "proves")
        transparent = {
            "Fixture.sourceShape": {
                "passes": True,
                "failure_tag": "",
                "failure_declaration": "",
                "expanded": 0,
            }
        }
        with mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_matches",
            return_value={route: True},
        ), mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_transparency_checks",
            return_value=transparent,
        ):
            pairs = audit_repository.semantic_contract_precloseout_exact_contract_pairs(
                "FixturePaper", self.paper, "partially formalized", status_payload
            )

        self.assertEqual(pairs, (("Fixture.proofRoute", "Fixture.sourceShape"),))
        self.assertEqual(
            audit_repository.semantic_contract_precloseout_exact_contract_pairs(
                "FixturePaper", self.paper, "formalized", status_payload
            ),
            (),
        )
        with mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_matches",
            return_value={route: False},
        ), mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_transparency_checks",
            return_value=transparent,
        ):
            self.assertEqual(
                audit_repository.semantic_contract_precloseout_exact_contract_pairs(
                    "FixturePaper", self.paper, "partially formalized", status_payload
                ),
                (),
            )

    def test_precloseout_pairs_fail_closed_for_corrected_targets(self) -> None:
        self.write_status("partially formalized")
        ordinary = self.contract_item()
        corrected = self.contract_item()
        corrected["coverage_status"] = "corrected_source_statement"
        self.write_map(
            {
                "ordinary_source_atom": ordinary,
                "corrected_source_atom": corrected,
            }
        )
        status_payload = json.loads((self.paper / "status.json").read_text(encoding="utf-8"))
        inventory = integrity.SemanticContractCloseoutInventory(
            contract_item_keys=("ordinary_source_atom", "corrected_source_atom"),
            scope_exclusion_item_keys=(),
        )
        with mock.patch.object(
            integrity,
            "semantic_contract_closeout_bridge_inventory",
            return_value=(inventory, []),
        ), mock.patch.object(
            audit_repository,
            "paper_statement_map_semantic_contract_findings",
            return_value=[],
        ):
            pairs = audit_repository.semantic_contract_precloseout_exact_contract_pairs(
                "FixturePaper",
                self.paper,
                "partially formalized",
                status_payload,
                paper_declarations=audit_repository.paper_lean_declaration_index(
                    self.paper
                ),
            )

        self.assertEqual(pairs, ())

    def test_short_name_duplicate_uses_configured_interface_source(self) -> None:
        """Implementation helpers cannot make a configured interface row unreviewed."""

        (self.paper / "Implementation.lean").write_text(
            "namespace FixtureImplementation\n"
            "abbrev sourceShape : Prop := True\n"
            "theorem proofRoute : sourceShape := trivial\n"
            "end FixtureImplementation\n",
            encoding="utf-8",
        )
        item = self.contract_item()
        contract = item["semantic_contract"]
        assert isinstance(contract, dict)
        contract["spec_declaration"] = "Fixture.sourceShape"
        contract["evidence_declaration"] = "Fixture.proofRoute"
        self.write_map({"opaque_source_atom": item})
        payload = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        declarations = audit_repository.paper_lean_declaration_index(self.paper)
        route = ("Fixture.sourceShape", "Fixture.proofRoute", "proves")
        transparent = {
            "Fixture.sourceShape": {
                "passes": True,
                "failure_tag": "",
                "failure_declaration": "",
                "expanded": 0,
            }
        }
        with mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_matches",
            return_value={route: True},
        ), mock.patch.object(
            lean_signature_manifest,
            "run_lean_semantic_contract_transparency_checks",
            return_value=transparent,
        ):
            findings = audit_repository.paper_statement_map_semantic_contract_findings(
                "FixturePaper",
                self.paper,
                "formalized",
                payload,
                declarations,
                set(),
                json.loads((self.paper / "status.json").read_text(encoding="utf-8")),
            )
        self.assertEqual(findings, [])

    def test_ordinary_claim_without_contract_cannot_use_bridge(self) -> None:
        item = self.contract_item()
        item.pop("semantic_contract")
        self.write_map({"source_item_without_route": item})

        inventory, findings = integrity.semantic_contract_closeout_bridge_inventory(
            self.paper, "formalized"
        )

        self.assertIsNone(inventory)
        self.assertTrue(
            any("requires an exact semantic_contract" in finding.message for finding in findings)
        )

    def test_support_only_source_inventory_does_not_block_direct_bridge(self) -> None:
        """Support rows stay visible without becoming duplicate Spec obligations."""

        support = self.contract_item()
        support.pop("semantic_contract")
        support["source_status"] = "support_only"
        support["inventory_role"] = "proof_support"
        support["support_lean_declarations"] = ["Fixture.proofRoute"]
        self.write_map(
            {
                "direct_source_claim": self.contract_item(),
                "source_proof_support": support,
            }
        )

        inventory, findings = integrity.semantic_contract_closeout_bridge_inventory(
            self.paper, "formalized"
        )

        self.assertEqual(findings, [])
        assert inventory is not None
        self.assertEqual(inventory.contract_item_keys, ("direct_source_claim",))
        self.assertEqual(inventory.scope_exclusion_item_keys, ())

    def test_explicit_byte_pinned_scope_exclusion_stays_visible_but_is_allowed(self) -> None:
        self.source_text = (
            "Theorem 1. States the exact audited property.\n"
            "Proof.\n"
            "\n"
            "An unnumbered computational observation is catalogued.\n"
        )
        self.source.write_text(self.source_text, encoding="utf-8")
        self.source_digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        self.quote = self.source_text.splitlines()[0]
        self.quote_digest = hashlib.sha256(self.quote.encode("utf-8")).hexdigest()
        scoped_quote = self.source_text.splitlines()[3]
        scoped_quote_digest = hashlib.sha256(scoped_quote.encode("utf-8")).hexdigest()
        scoped = {
            "statement": "A source-visible computational observation retained in the inventory.",
            "source_kind": "remark",
            "claim_bearing": True,
            "source_location": "source.txt:4",
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 4,
                    "line_end": 4,
                    "quoted_text": scoped_quote,
                    "quoted_text_sha256": scoped_quote_digest,
                }
            ],
            "user_approved_scope_exclusion": {
                "schema": 1,
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "User instruction on 2026-07-25 excludes this computational observation while retaining it visibly.",
                "approved_at": "2026-07-25",
                "reason": "The user explicitly excluded this source-visible computational observation from the theorem proof target.",
                "source_locator": "source.txt:4",
                "source_evidence": "The pinned source passage is retained as a visible non-proof scope disposition.",
                "source_anchor_quote_sha256": scoped_quote_digest,
            },
        }
        self.write_map(
            {
                "renamed_contract_route": self.contract_item(),
                "renamed_scope_disposition": scoped,
            }
        )

        inventory, findings = integrity.semantic_contract_closeout_bridge_inventory(
            self.paper, "formalized"
        )

        self.assertEqual(findings, [])
        assert inventory is not None
        self.assertEqual(inventory.contract_item_keys, ("renamed_contract_route",))
        self.assertEqual(
            inventory.scope_exclusion_item_keys, ("renamed_scope_disposition",)
        )

    def test_spec_structure_rejects_aliases_and_missing_source(self) -> None:
        path = self.paper / "PaperInterface.lean"
        evidence = audit_repository.LeanDeclaration(
            path=path,
            line=4,
            kind="theorem",
            name="Evidence",
            source="theorem Evidence : Prop := by exact Nat",
        )
        alias_spec = audit_repository.LeanDeclaration(
            path=path,
            line=3,
            kind="abbrev",
            name="SourceSpec",
            source="abbrev SourceSpec : Prop := Evidence",
        )
        declaration_index = {
            "Evidence": [evidence],
            "Fixture.Evidence": [evidence],
            "SourceSpec": [alias_spec],
            "Fixture.SourceSpec": [alias_spec],
        }
        alias_error = audit_repository.semantic_contract_spec_structure_error(
            declaration_index, alias_spec
        )
        self.assertIn("trivial alias", alias_error)

        missing_source_spec = audit_repository.LeanDeclaration(
            path=path,
            line=6,
            kind="def",
            name="MissingSourceSpec",
            source="",
        )
        missing_source_error = audit_repository.semantic_contract_spec_structure_error(
            declaration_index, missing_source_spec
        )
        self.assertIn("explicitly declare result type `Prop`", missing_source_error)

    def write_blank_scaffold(self, filename: str) -> None:
        (self.audit / filename).write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": "FixturePaper",
                    "items": {},
                    "non_evidence_scaffold": {"schema": 1, "status": "needs_review"},
                }
            ),
            encoding="utf-8",
        )

    def test_only_explicitly_blank_scaffolds_are_bridgeable(self) -> None:
        for filename in (
            "review_surface_llm.json",
            "lean_to_tex_llm.json",
            "statement_match_llm.json",
            "paper_coverage_llm.json",
        ):
            self.write_blank_scaffold(filename)

        lanes = audit_repository.semantic_contract_closeout_blank_sidecar_lanes(
            self.paper
        )
        self.assertEqual(
            lanes,
            {"review_surface": True, "statement": True, "coverage": True},
        )

        statement_path = self.audit / "statement_match_llm.json"
        payload = json.loads(statement_path.read_text(encoding="utf-8"))
        payload["items"] = {"row": {"judgment": "mismatch"}}
        statement_path.write_text(json.dumps(payload), encoding="utf-8")

        lanes = audit_repository.semantic_contract_closeout_blank_sidecar_lanes(
            self.paper
        )
        self.assertTrue(lanes["review_surface"])
        self.assertFalse(lanes["statement"])
        self.assertTrue(lanes["coverage"])

    def test_contract_and_legacy_lexical_surface_do_not_turn_off_source_record_judgment_gate(
        self,
    ) -> None:
        item = self.contract_item()
        item["lean_declarations"] = ["Fixture.proofRoute"]
        item["semantic_surface"] = {
            "schema": 1,
            "required_structural_tokens": ["="],
            "required_terms": ["Nat"],
            "forbidden_opaque_terms": ["OpaqueBundle"],
        }
        self.write_map({"opaque_source_atom": item})
        raw_audit = {
            "prompt_version": integrity.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
            "source_record_audit_sha256": "a" * 64,
            "paper_statement_map_sha256": integrity.current_paper_statement_map_sha256(
                self.paper
            ),
            "source_record_input_fingerprint": {
                "max_depth": 4,
                "no_lean": False,
            },
            "expected_semantic_model_judgment_keys": [
                "semantic-model::opaque-source-item"
            ],
            "missing_configured_review_rows": [],
            "configured_review_rows": [{}],
            "configured_review_rows_count": 1,
            "configured_review_row_count": 1,
            "review_row_count": 1,
            "recursive_field_count": 0,
            "recursion_failures": [],
            "recursion_failure_count": 0,
            "constructor_result_type_check_error": "",
            "source_premise_consistency_schema": 1,
            "source_premise_consistency_error": "",
            "source_premise_consistency_items": [],
            "source_premise_consistency_item_count": 0,
            "review_interface_source": {
                "path": "papers/FixturePaper/PaperInterface.lean",
                "sha256": "a" * 64,
            },
            "fresh_source_elaboration": {
                "mode": "isolated_temp_overlay",
                "returncode": 0,
                "source_file": "papers/FixturePaper/PaperInterface.lean",
                "source_sha256": "a" * 64,
            },
            "lean_check": {
                "returncode": 0,
                "requested_checked_rows": [
                    {
                        "row": "fixture",
                        "qualified_declaration": "FixturePaper.PaperInterface.fixture",
                    }
                ],
                "checked_rows": [
                    {
                        "row": "fixture",
                        "qualified_declaration": "FixturePaper.PaperInterface.fixture",
                    }
                ],
                "fresh_source_elaboration": {
                    "mode": "isolated_temp_overlay",
                    "returncode": 0,
                    "source_file": "papers/FixturePaper/PaperInterface.lean",
                    "source_sha256": "a" * 64,
                },
            },
        }
        stamp_source_record_audit_receipts(raw_audit)
        (self.audit / "source_record_audit.json").write_text(
            json.dumps(raw_audit),
            encoding="utf-8",
        )
        (self.audit / "source_record_match_llm.json").write_text(
            json.dumps({"schema": 1, "items": {}}), encoding="utf-8"
        )

        with mock.patch.object(
            integrity,
            "source_record_current_input_fingerprint_error",
            return_value="",
        ):
            findings = integrity.check_source_record_judgments(self.paper, "formalized")

        self.assertTrue(
            any("semantic-model item(s)" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_sidecar_findings_suppress_only_bridgeable_blank_lanes(self) -> None:
        (self.paper / "status.json").write_text("{}", encoding="utf-8")
        surface = {
            "needs_attention": True,
            "has_completed_audit": False,
            "missing_required": True,
        }
        statements = {"needs_attention": True, "missing_judgment_count": 1}
        coverage = {
            "needs_attention": True,
            "source_to_lean_needs_attention": True,
            "missing_required": True,
        }
        assumptions = {"needs_attention": False}
        with (
            mock.patch.object(
                audit_repository,
                "paper_statement_map_declaration_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "semantic_contract_closeout_bridge_is_current",
                return_value=True,
            ),
            mock.patch.object(
                audit_repository,
                "semantic_contract_closeout_blank_sidecar_lanes",
                return_value={
                    "review_surface": True,
                    "statement": True,
                    "coverage": True,
                },
            ),
            mock.patch.object(review_dashboard, "review_items_for_paper", return_value=[]),
            mock.patch.object(review_dashboard, "review_surface_audit_summary", return_value=surface),
            mock.patch.object(
                review_dashboard,
                "statement_translation_audit_summary",
                return_value=statements,
            ),
            mock.patch.object(
                review_dashboard,
                "paper_coverage_audit_summary",
                return_value=coverage,
            ),
            mock.patch.object(
                review_dashboard,
                "assumption_provenance_audit_summary",
                return_value=assumptions,
            ),
        ):
            findings = audit_repository.paper_statement_sidecar_findings(
                "FixturePaper", self.paper, "formalized"
            )
        self.assertEqual(findings, [])

        with (
            mock.patch.object(
                audit_repository,
                "paper_statement_map_declaration_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "semantic_contract_closeout_bridge_is_current",
                return_value=True,
            ),
            mock.patch.object(
                audit_repository,
                "semantic_contract_closeout_blank_sidecar_lanes",
                return_value={
                    "review_surface": True,
                    "statement": True,
                    "coverage": False,
                },
            ),
            mock.patch.object(review_dashboard, "review_items_for_paper", return_value=[]),
            mock.patch.object(review_dashboard, "review_surface_audit_summary", return_value=surface),
            mock.patch.object(
                review_dashboard,
                "statement_translation_audit_summary",
                return_value=statements,
            ),
            mock.patch.object(
                review_dashboard,
                "paper_coverage_audit_summary",
                return_value=coverage,
            ),
            mock.patch.object(
                review_dashboard,
                "assumption_provenance_audit_summary",
                return_value=assumptions,
            ),
        ):
            findings = audit_repository.paper_statement_sidecar_findings(
                "FixturePaper", self.paper, "formalized"
            )
        self.assertTrue(
            any("paper-coverage audit needs attention" in finding.message for finding in findings)
        )

    def test_v11_source_first_coverage_rejects_a_spec_reused_by_two_sources(
        self,
    ) -> None:
        """Context on one card cannot cover a second source presentation."""

        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "status": "formalized",
                    "review_surface": {
                        "require_v11_raw_source_spec_screening": True,
                    },
                }
            ),
            encoding="utf-8",
        )
        shared_contract = {
            "spec_declaration": "Fixture.SharedSpec",
            "evidence_declaration": "Fixture.sharedProof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        map_items = {
            "first_source_presentation": {"semantic_contract": shared_contract},
            "second_source_presentation": {"semantic_contract": shared_contract},
        }
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps({"items": map_items}), encoding="utf-8"
        )
        claim_rows = [
            {
                "human_claim_source_key": "first_source_presentation",
                "full_name": "Fixture.SharedSpec",
                "llm_match_judgment": "matches",
                "llm_match_source": "v11_raw_source_spec_screening.json",
            },
            {
                "human_claim_source_key": "second_source_presentation",
                "full_name": "Fixture.SharedSpec",
                "llm_match_judgment": "matches",
                "llm_match_source": "v11_raw_source_spec_screening.json",
            },
        ]
        clear_summary = {"needs_attention": False, "has_completed_audit": True}
        with (
            mock.patch.object(
                audit_repository,
                "paper_statement_map_declaration_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "semantic_contract_closeout_bridge_is_current",
                return_value=False,
            ),
            mock.patch.object(
                review_dashboard,
                "review_surface_audit_summary",
                return_value=clear_summary,
            ),
            mock.patch.object(
                review_dashboard,
                "statement_translation_audit_summary",
                return_value={"needs_attention": False},
            ),
            mock.patch.object(
                review_dashboard,
                "paper_coverage_audit_summary",
                return_value={"needs_attention": False},
            ),
            mock.patch.object(
                review_dashboard,
                "assumption_provenance_audit_summary",
                return_value={"needs_attention": False},
            ),
            mock.patch.object(
                review_dashboard,
                "human_review_claim_items",
                return_value=claim_rows,
            ),
            mock.patch.object(
                review_dashboard,
                "bind_current_v11_source_spec_screening",
            ),
            mock.patch.object(
                audit_repository,
                "source_coverage_mode_from_map",
                return_value=("named_theoretical_statements", ""),
            ),
            mock.patch.object(
                audit_repository,
                "source_index_byte_pinned_anchor_item_ids",
                return_value=set(),
            ),
            mock.patch.object(
                audit_repository,
                "filter_source_map_items_for_proof_obligations",
                return_value=map_items,
            ),
            mock.patch.object(
                audit_repository,
                "source_presentation_aliases",
                return_value=({}, []),
            ),
        ):
            findings = audit_repository.paper_statement_sidecar_findings(
                "FixturePaper",
                self.paper,
                "formalized",
                review_items_provider=lambda: (),
            )

        self.assertTrue(
            any("Fixture.SharedSpec:multiple_source_items" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_stale_positive_surface_reuse_requires_complete_current_semantic_rows(
        self,
    ) -> None:
        surface = {
            "row_count": 2,
            "recorded_review_rows": 2,
            "review_surface_sha256": "a" * 64,
            "recorded_review_surface_sha256": "b" * 64,
            "judgment": "passes",
            "stale": True,
            "missing_required": False,
            "prompt_version_stale": False,
            "metadata_missing": False,
            "non_evidence_scaffold": False,
            "unknown_judgment": False,
        }
        statements = {
            "row_count": 2,
            "semantic_current_judgment_count": 2,
            "needs_attention": False,
            "missing_draft_count": 0,
            "stale_draft_count": 0,
            "missing_judgment_count": 0,
            "stale_judgment_count": 0,
            "missing_obligation_ledger_count": 0,
            "mismatch_count": 0,
            "uncertain_count": 0,
            "unknown_count": 0,
            "ambiguous_semantic_judgment_count": 0,
        }
        lanes = audit_repository.semantic_contract_closeout_current_semantic_reuse_lanes(
            surface,
            statements,
        )
        self.assertTrue(lanes["review_surface"])

        for field, value in (
            ("semantic_current_judgment_count", 1),
            ("ambiguous_semantic_judgment_count", 1),
            ("stale_draft_count", 1),
            ("needs_attention", True),
        ):
            with self.subTest(field=field):
                incomplete = dict(statements)
                incomplete[field] = value
                lanes = (
                    audit_repository.semantic_contract_closeout_current_semantic_reuse_lanes(
                        surface,
                        incomplete,
                    )
                )
                self.assertFalse(lanes["review_surface"])

        prompt_stale = dict(surface)
        prompt_stale["prompt_version_stale"] = True
        lanes = audit_repository.semantic_contract_closeout_current_semantic_reuse_lanes(
            prompt_stale,
            statements,
        )
        self.assertFalse(lanes["review_surface"])


if __name__ == "__main__":
    unittest.main()
