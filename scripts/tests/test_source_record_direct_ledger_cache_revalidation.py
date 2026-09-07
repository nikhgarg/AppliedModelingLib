#!/usr/bin/env python3
"""Adversarial tests for no-Lean direct statement-ledger cache revalidation."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard as DASHBOARD  # noqa: E402
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)
AUDIT_SPEC = importlib.util.spec_from_file_location(
    "direct_statement_ledger_cache_audit", AUDIT_HELPER
)
assert AUDIT_SPEC is not None and AUDIT_SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(AUDIT_SPEC)
sys.modules[AUDIT_SPEC.name] = AUDIT
AUDIT_SPEC.loader.exec_module(AUDIT)


PAPER = "Fixture"
ROW = "endpoint"
QUALIFIED = "Fixture.PaperInterface.endpoint"
SPEC_QUALIFIED = "Fixture.PaperInterface.endpointSpec"
KEY = "endpoint.hsource : SourceCondition"
GAIN_KEY = "endpoint.hsecond : SecondCondition"
STATEMENT = "Theorem 1: every source condition has the stated endpoint."


def manifest() -> dict[str, object]:
    value: dict[str, object] = {
        "schema": 2,
        "declaration_kind": "theorem",
        "conclusion_mode": "type_only",
        "atoms": [
            {
                "ref": "result",
                "role": "conclusion",
                "binder_info": "explicit",
                "canonical": {"tag": "result"},
                "display": "P",
            }
        ],
    }
    value["sha256"] = DASHBOARD.signature_manifest_digest(value)
    return value


class DirectStatementLedgerCacheRevalidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.audit_dir.mkdir(parents=True)
        (self.paper_dir / ".review_traces").mkdir()
        self.interface_path = self.paper_dir / "PaperInterface.lean"
        self.interface_text = (
            "namespace Fixture.PaperInterface\n\n"
            "theorem endpoint (h : True) : True := h\n\n"
            "def endpointSpec (h : True) : Prop := True\n\n"
            "theorem neighbor (h : True) : True := h\n\n"
            "end Fixture.PaperInterface\n"
        )
        self.interface_path.write_text(self.interface_text, encoding="utf-8")
        self._write_status("formalized")
        self.map_path = self.audit_dir / "paper_statement_map.json"
        self.sidecar_path = self.audit_dir / "statement_match_llm.json"
        self.raw_path = self.audit_dir / "source_record_audit.json"
        self.signature_manifest = manifest()
        self.signature = str(self.signature_manifest["sha256"])
        declarations = AUDIT.parse_local_declarations(self.root, [self.interface_path])
        self.declaration_source = next(
            declaration.source
            for declaration in declarations
            if declaration.name == QUALIFIED
        )
        parsed = DASHBOARD.parse_review_source_declarations(self.interface_path)
        endpoint = next(declaration for declaration in parsed if declaration[2] == QUALIFIED)
        neighbor = next(
            declaration
            for declaration in parsed
            if declaration[2] == "Fixture.PaperInterface.neighbor"
        )
        self.interface_source = str(endpoint[3]).strip()
        self.interface_line = int(endpoint[5])
        self.neighbor_interface_source = str(neighbor[3]).strip()
        self.neighbor_interface_line = int(neighbor[5])
        self.fingerprint: dict[str, object] = {
            "fixture": "direct-ledger-current",
            "no_lean": False,
        }

    def _write_status(self, status: str) -> None:
        (self.paper_dir / "status.json").write_text(
            json.dumps(
                {
                    "status": status,
                    "review_surface": {
                        "source_file": f"papers/{PAPER}/PaperInterface.lean"
                    },
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )

    def _write_map(self, *, semantic_contract: bool = False) -> tuple[str, str]:
        source_item: dict[str, object] = {
            "claim_bearing": True,
            "source_kind": "theorem",
            "statement": STATEMENT,
            "source_location": "source.txt:1-1",
            "lean_declarations": ["endpoint" if semantic_contract else QUALIFIED],
        }
        if semantic_contract:
            source_item["semantic_contract"] = {
                "evidence_declaration": QUALIFIED,
                "spec_declaration": SPEC_QUALIFIED,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        source_map: dict[str, object] = {
            "source_coverage_mode": "deep_paper_with_all_prose_claims",
            "items": {"source_result": source_item},
        }
        if semantic_contract:
            source_map["semantic_contract_schema"] = 1
        self.map_path.write_text(
            json.dumps(
                source_map,
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        return AUDIT.paper_statement_map_cache_receipts(self.paper_dir)

    def _write_statement_sidecar(self, *, stale_signature: bool = False) -> None:
        self.sidecar_path.write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": PAPER,
                    "prompt_version": DASHBOARD.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                    "validator": "fixture semantic reviewer",
                    "validated_at": "2026-07-28T00:00:00Z",
                    "items": {
                        ROW: {
                            "judgment": "matches",
                            "lean_signature_sha256": (
                                "0" * 64 if stale_signature else self.signature
                            ),
                            "paper_statement_sha256": DASHBOARD.statement_digest(
                                STATEMENT
                            ),
                            "tex_statement_sha256": DASHBOARD.statement_digest(
                                "P"
                            ),
                        }
                    },
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )

    def _write_manifest_cache(
        self,
        *,
        interface_source: str | None = None,
        line_number: int | None = None,
    ) -> None:
        (self.paper_dir / ".review_traces" / "paper_interface_cache.json").write_text(
            json.dumps(
                {
                    "schema": DASHBOARD.PAPER_INTERFACE_CACHE_SCHEMA,
                    "paper": PAPER,
                    "hashes": {
                        "review_source_file": "PaperInterface.lean",
                        "interface_sha256": DASHBOARD.statement_digest(
                            self.interface_text
                        ),
                    },
                    "rows": [
                        {
                            "name": ROW,
                            "interface_source": (
                                self.interface_source
                                if interface_source is None
                                else interface_source
                            ),
                            "line_number": (
                                self.interface_line
                                if line_number is None
                                else line_number
                            ),
                            "lean_signature_sha256": self.signature,
                            "lean_signature_manifest": self.signature_manifest,
                            "paper_statement": STATEMENT,
                            "agent_statement": "P",
                        }
                    ],
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )

    def _raw_item(
        self,
        key: str,
        *,
        association_mode: str = "explicit_source_map_direct_route",
        semantic_contract: bool = False,
        semantic_contract_member_role: str = "direct_evidence",
    ) -> dict[str, object]:
        identity = {
            "qualified_declaration": QUALIFIED,
            "declaration_sha256": hashlib.sha256(
                self.declaration_source.encode("utf-8")
            ).hexdigest(),
        }
        signature_identity = {
            "qualified_declaration": QUALIFIED,
            "elaborated_signature_sha256": self.signature,
        }
        association: dict[str, object]
        if semantic_contract:
            source_map = json.loads(self.map_path.read_text(encoding="utf-8"))
            source_item = source_map["items"]["source_result"]
            assert isinstance(source_item, dict)
            association = AUDIT.source_contract_association_payload(
                association_mode="semantic_contract_group_member",
                semantic_model_judgment_key="semantic-model::endpoint",
                member_role=semantic_contract_member_role,
                reviewed_identity=identity,
                source_identities=[
                    AUDIT.semantic_contract_source_identity("source_result", source_item)
                ],
                reviewed_signature_identity=signature_identity,
            )
        else:
            association = {
                "association_mode": association_mode,
                "reviewed_declaration_identity": identity,
                "reviewed_elaborated_signature_identity": signature_identity,
                "source_map_item_keys": ["source_result"],
            }
        return {
            "row": ROW,
            "judgment_key": key,
            "effective_qualified_declaration": QUALIFIED,
            "reviewed_declaration_identity": identity,
            "reviewed_elaborated_signature_identities": [signature_identity],
            "source_contract_association": association,
        }

    def _raw(
        self,
        *,
        gain: bool = False,
        malformed: bool = False,
        bridge_only: bool = False,
        semantic_contract: bool = False,
        semantic_contract_member_role: str = "direct_evidence",
    ) -> dict[str, object]:
        map_sha256, _semantic_sha256 = self._write_map(
            semantic_contract=semantic_contract
        )
        items = [
            self._raw_item(
                KEY,
                association_mode=(
                    "semantic_contract_closeout_bridge"
                    if bridge_only
                    else "explicit_source_map_direct_route"
                ),
                semantic_contract=semantic_contract,
                semantic_contract_member_role=semantic_contract_member_role,
            )
        ]
        expected = [KEY]
        if gain:
            items.append(
                self._raw_item(
                    GAIN_KEY,
                    semantic_contract=semantic_contract,
                    semantic_contract_member_role=semantic_contract_member_role,
                )
            )
            expected.append(GAIN_KEY)
        ledger: list[str] = [KEY]
        if malformed:
            ledger.append(KEY)
        raw: dict[str, object] = {
            "paper": PAPER,
            "prompt_version": AUDIT.SOURCE_RECORD_PROMPT_VERSION,
            "source_record_input_fingerprint": self.fingerprint,
            "paper_statement_map_sha256": map_sha256,
            "lean_check": {"returncode": 0},
            "expected_input_judgment_keys": expected,
            "boundary_input_items": items,
            "conclusion_dependency_items": [],
            "statement_ledger_covered_boundary_input_keys": ledger,
            "precloseout_contract_covered_boundary_input_keys": [],
        }
        stamp_source_record_audit_receipts(raw)
        self.raw_path.write_text(
            json.dumps(raw, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        return raw

    def _cache_args(self) -> SimpleNamespace:
        return SimpleNamespace(
            paper=PAPER,
            force=False,
            refresh_judgment_summary=False,
            ignore_current_judgments=False,
            no_lean=False,
        )

    def _reusable(
        self,
        raw: dict[str, object],
        *,
        fingerprint: dict[str, object] | None = None,
    ) -> dict[str, object] | None:
        map_sha256, map_semantic_sha256 = AUDIT.paper_statement_map_cache_receipts(
            self.paper_dir
        )
        with (
            patch.object(
                AUDIT,
                "source_record_input_fingerprint",
                return_value=(self.fingerprint if fingerprint is None else fingerprint),
            ),
            patch.object(
                AUDIT,
                "source_record_raw_scan_completeness_error",
                return_value="",
            ),
            patch.object(
                AUDIT,
                "source_record_raw_reusable_item_metadata_error",
                return_value="",
            ),
            patch.object(
                DASHBOARD,
                "semantic_obligation_ledger_error",
                return_value="",
            ),
            patch.object(
                AUDIT,
                "refresh_existing_judgment_summary",
                return_value={"reused": True},
            ) as refresh,
        ):
            result = AUDIT.reusable_source_record_audit(
                self._cache_args(),
                self.root,
                self.paper_dir,
                paper_statement_map_sha256=map_sha256,
                paper_statement_map_semantic_sha256=map_semantic_sha256,
            )
            if result is None:
                refresh.assert_not_called()
            else:
                self.assertEqual(refresh.call_count, 1)
            return result

    def _prepare_current_fixture(self, **raw_kwargs: object) -> dict[str, object]:
        self._write_manifest_cache()
        self._write_statement_sidecar()
        return self._raw(**raw_kwargs)

    def test_equal_coverage_reuses_without_subprocess(self) -> None:
        raw = self._prepare_current_fixture()
        with (
            patch.object(
                DASHBOARD.subprocess,
                "run",
                side_effect=AssertionError("direct-ledger revalidation ran a subprocess"),
            ),
            patch.object(
                DASHBOARD.subprocess,
                "Popen",
                side_effect=AssertionError("direct-ledger revalidation ran a subprocess"),
            ),
            patch.object(
                DASHBOARD,
                "semantic_obligation_ledger_error",
                return_value="",
            ),
        ):
            self.assertEqual(
                AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                    self.root, self.paper_dir, raw
                ),
                {KEY},
            )
        self.assertEqual(self._reusable(raw), {"reused": True})

    def test_current_coverage_gain_reuses_old_raw_surface(self) -> None:
        raw = self._prepare_current_fixture(gain=True)
        with patch.object(
            DASHBOARD, "semantic_obligation_ledger_error", return_value=""
        ):
            current = AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                self.root, self.paper_dir, raw
            )
        self.assertEqual(current, {KEY, GAIN_KEY})
        self.assertEqual(self._reusable(raw), {"reused": True})

    def test_stale_direct_statement_sidecar_loses_cache_reuse(self) -> None:
        raw = self._prepare_current_fixture()
        self._write_statement_sidecar(stale_signature=True)
        with patch.object(
            DASHBOARD, "semantic_obligation_ledger_error", return_value=""
        ):
            self.assertEqual(
                AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                    self.root, self.paper_dir, raw
                ),
                set(),
            )
        self.assertIsNone(self._reusable(raw))

    def test_malformed_saved_direct_ledger_refuses_reuse(self) -> None:
        raw = self._prepare_current_fixture(malformed=True)
        self.assertIsNone(AUDIT.source_record_saved_statement_ledger_coverages(raw))
        self.assertIsNone(self._reusable(raw))

    def test_precloseout_projection_remains_stricter_than_direct_revalidation(self) -> None:
        raw = self._prepare_current_fixture()
        raw = copy.deepcopy(raw)
        raw["precloseout_contract_covered_boundary_input_keys"] = [KEY]
        stamp_source_record_audit_receipts(raw)
        self.raw_path.write_text(
            json.dumps(raw, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        self.assertIsNone(self._reusable(raw))

    def test_saved_semantic_contract_bridge_never_inherits_direct_cache_credit(self) -> None:
        raw = self._prepare_current_fixture(bridge_only=True)
        with patch.object(
            DASHBOARD, "semantic_obligation_ledger_error", return_value=""
        ):
            self.assertIsNone(
                AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                    self.root, self.paper_dir, raw
                )
            )
        self.assertIsNone(self._reusable(raw))

    def test_saved_semantic_contract_direct_evidence_reuses_current_exact_route(self) -> None:
        raw = self._prepare_current_fixture(semantic_contract=True)
        with (
            patch.object(
                DASHBOARD.subprocess,
                "run",
                side_effect=AssertionError("direct-ledger revalidation ran a subprocess"),
            ),
            patch.object(
                DASHBOARD.subprocess,
                "Popen",
                side_effect=AssertionError("direct-ledger revalidation ran a subprocess"),
            ),
            patch.object(
                DASHBOARD, "semantic_obligation_ledger_error", return_value=""
            ),
        ):
            self.assertEqual(
                AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                    self.root, self.paper_dir, raw
                ),
                {KEY},
            )
        self.assertEqual(self._reusable(raw), {"reused": True})

    def test_semantic_contract_spec_member_never_inherits_direct_cache_credit(self) -> None:
        raw = self._prepare_current_fixture(
            semantic_contract=True,
            semantic_contract_member_role="transparent_spec",
        )
        with patch.object(
            DASHBOARD, "semantic_obligation_ledger_error", return_value=""
        ):
            self.assertIsNone(
                AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                    self.root, self.paper_dir, raw
                )
            )
        self.assertIsNone(self._reusable(raw))

    def test_semantic_contract_source_semantic_change_refuses_reuse(self) -> None:
        raw = self._prepare_current_fixture(semantic_contract=True)
        source_map = json.loads(self.map_path.read_text(encoding="utf-8"))
        source_map["items"]["source_result"]["statement"] = "Changed source theorem."
        self.map_path.write_text(
            json.dumps(source_map, sort_keys=True), encoding="utf-8"
        )
        with patch.object(
            DASHBOARD, "semantic_obligation_ledger_error", return_value=""
        ):
            self.assertIsNone(
                AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                    self.root, self.paper_dir, raw
                )
            )
        self.assertIsNone(self._reusable(raw))

    def test_retired_partial_transition_artifact_does_not_override_fingerprint(
        self,
    ) -> None:
        self._write_status("partially formalized")
        raw = self._prepare_current_fixture(semantic_contract=True)
        partial_fingerprint = {
            **self.fingerprint,
            "max_depth": 4,
            "relevant_status_sha256": "a" * 64,
        }
        formalized_fingerprint = {
            **partial_fingerprint,
            "relevant_status_sha256": "b" * 64,
        }
        raw = copy.deepcopy(raw)
        raw["source_record_input_fingerprint"] = partial_fingerprint
        stamp_source_record_audit_receipts(raw)
        self.raw_path.write_text(
            json.dumps(raw, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        (self.audit_dir / "source_record_partial_to_formalized_transition.json").write_text(
            json.dumps(
                {
                    "schema": 2,
                    "paper": PAPER,
                    "historical_only": True,
                }
            ),
            encoding="utf-8",
        )
        self._write_status("formalized")

        # A historical filename is inert provenance. The changed current
        # fingerprint must follow the normal current-engine path.
        self.assertIsNone(
            self._reusable(raw, fingerprint=formalized_fingerprint)
        )
        with patch.object(
            AUDIT,
            "current_direct_statement_ledger_covered_boundary_input_keys_without_lean",
            return_value=set(),
        ):
            self.assertIsNone(
                self._reusable(raw, fingerprint=formalized_fingerprint)
            )

    def test_same_signature_neighbor_cache_row_refuses_reuse(self) -> None:
        raw = self._prepare_current_fixture()
        self._write_manifest_cache(
            interface_source=self.neighbor_interface_source,
            line_number=self.neighbor_interface_line,
        )
        with patch.object(
            DASHBOARD, "semantic_obligation_ledger_error", return_value=""
        ):
            self.assertIsNone(
                AUDIT.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
                    self.root, self.paper_dir, raw
                )
            )
        self.assertIsNone(self._reusable(raw))


if __name__ == "__main__":
    unittest.main()
