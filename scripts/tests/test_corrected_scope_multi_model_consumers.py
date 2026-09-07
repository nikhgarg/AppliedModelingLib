#!/usr/bin/env python3
"""Regression tests for exact target-to-model corrected-scope routing."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

from scripts import audit_conclusion_provenance as conclusion  # noqa: E402
from scripts import audit_repository as repository  # noqa: E402


def sha256(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


class CorrectedScopeMultiModelConsumerTests(unittest.TestCase):
    """Exercise consumers with structurally disjoint governing models."""

    optional_target = "Fixture.PaperInterface.optional_endpoint"
    report_target = "Fixture.PaperInterface.report_endpoint"
    optional_model = "Fixture.OptionalModel"
    report_model = "Fixture.ReportModel"
    paired_model = "Fixture.PairedModel"
    optional_field = "Fixture.OptionalModel.optional_rule"
    report_field = "Fixture.ReportModel.report_rule"

    def _targets(self) -> tuple[str, str]:
        return (self.optional_target, self.report_target)

    def _multi_scope(self) -> dict[str, object]:
        return {
            "target_result_declarations": list(self._targets()),
            "model_spec_declarations": [self.optional_model, self.report_model],
            "target_model_spec_declarations": {
                self.optional_target: self.optional_model,
                self.report_target: self.report_model,
            },
        }

    def _legacy_scope(self) -> dict[str, object]:
        return {
            "target_result_declarations": [self.optional_target],
            "model_spec_declaration": self.optional_model,
        }

    @staticmethod
    def _aggregate_item(item: dict[str, object]) -> dict[str, object]:
        return {
            **item,
            "source_record_item_reuse_eligibility": {
                "eligible": False,
                "blockers": ["fixture aggregate receipt"],
            },
        }

    def _semantic_item(
        self,
        *,
        target: str,
        row: str,
        model: str,
        field: str,
        include_input_binding: bool = False,
    ) -> dict[str, object]:
        item: dict[str, object] = {
            "judgment_key": f"semantic-model::{row}",
            "row": row,
            "qualified_declaration": target,
            "reviewed_declaration_identity": {
                "qualified_declaration": target,
                "declaration_sha256": sha256(f"declaration:{target}"),
            },
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": target,
                    "elaborated_signature_sha256": sha256(f"signature:{target}"),
                }
            ],
            "expanded_lean_surface": {
                "record_field_types": [{"path": f"{model} -> {field}"}],
            },
        }
        if include_input_binding:
            item["expanded_lean_surface"] = {
                "record_field_types": [{"path": f"{model} -> {field}"}],
                "binder_domains": [
                    {
                        "expanded_type": model,
                        "alpha_normalized_type": model,
                    }
                ],
                "record_roots": [model],
            }
            item["record_input_bindings"] = [
                {
                    "binder_names": ["source_model"],
                    "record_roots": [model],
                    "source_type_canonical": model,
                    "expanded_type": model,
                    "alpha_normalized_type": model,
                    "fully_qualified_expanded_type_canonical": model,
                }
            ]
        return self._aggregate_item(item)

    def _attach_transparent_spec_pair(
        self, item: dict[str, object]
    ) -> None:
        """Attach the generator-owned pair receipt consumed by projections."""

        target = str(item["qualified_declaration"])
        spec = "Fixture.PaperInterface.TransparentStatementOwner"
        direct_identity = item["reviewed_declaration_identity"]
        direct_signature = item["reviewed_elaborated_signature_identities"][0]
        spec_identity = {
            "qualified_declaration": spec,
            "declaration_sha256": sha256(f"declaration:{spec}"),
        }
        source_identity = {
            "source_key": "fixture_source_theorem",
            "source_location": "source.tex:10-12",
            "source_kind": "theorem",
            "source_map_item_sha256": sha256("fixture source-map item"),
            "source_semantic_sha256": sha256("fixture source semantics"),
            "semantic_contract": {
                "spec_declaration": spec,
                "evidence_declaration": target,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        alpha_surface = {
            "alpha_normalized_result": "forall _b0, Endpoint _b0",
            "binder_domains": [],
        }
        item.update(
            {
                "semantic_surface_origin": {
                    "kind": "transparent_spec_body",
                    "qualified_declaration": spec,
                },
                "semantic_contract_group": {
                    "schema": 1,
                    "structural_alpha_normalized_equal": True,
                    "source_item_identities": [deepcopy(source_identity)],
                    "member_rows": [
                        {
                            "role": "direct_evidence",
                            "row": "unrelated-direct-label",
                            "qualified_declaration": target,
                            "reviewed_declaration_identity": deepcopy(
                                direct_identity
                            ),
                        },
                        {
                            "role": "transparent_spec",
                            "row": "unrelated-spec-label",
                            "qualified_declaration": spec,
                            "reviewed_declaration_identity": deepcopy(
                                spec_identity
                            ),
                        },
                    ],
                    "direct_evidence_type": {
                        "qualified_declaration": target,
                        "structural_alpha_normalized_surface": deepcopy(
                            alpha_surface
                        ),
                    },
                    "surface_root": {
                        "kind": "transparent_spec_body",
                        "qualified_declaration": spec,
                        "structural_alpha_normalized_surface": deepcopy(
                            alpha_surface
                        ),
                    },
                },
                "semantic_contract_source_association": {
                    "schema": 2,
                    "role": "direct_evidence",
                    "paired_qualified_declaration": spec,
                    "review_scope": "individual_row_only",
                    "structural_pairing": "not_asserted_by_source_association",
                    "reviewed_declaration_identity": deepcopy(direct_identity),
                    "reviewed_elaborated_signature_identity": deepcopy(
                        direct_signature
                    ),
                    "source_item_identities": [deepcopy(source_identity)],
                    "semantic_association_sha256": (
                        conclusion.semantic_association_record_digest(
                            [source_identity["source_semantic_sha256"]],
                            direct_signature,
                        )
                    ),
                },
            }
        )

    def _field_item(self, *, model: str, field: str) -> dict[str, object]:
        return self._aggregate_item(
            {
                "judgment_key": field,
                "structure": model,
                "nested_structures": [],
                "path": f"{model} -> {field}",
            }
        )

    @staticmethod
    def _mapping(key: str, **fields: str) -> dict[str, object]:
        return {
            "source_record_item_key": key,
            "aggregate_audit_freshness_only": True,
            **fields,
        }

    def _conclusion_payload(
        self, *, legacy: bool = False
    ) -> tuple[dict[str, object], dict[str, object]]:
        targets = (self.optional_target,) if legacy else self._targets()
        semantic_items = [
            self._semantic_item(
                target=self.optional_target,
                row="optional_endpoint",
                model=self.optional_model,
                field=self.optional_field,
            )
        ]
        self._attach_transparent_spec_pair(semantic_items[0])
        field_items = [
            self._field_item(model=self.optional_model, field=self.optional_field)
        ]
        if not legacy:
            semantic_items.append(
                self._semantic_item(
                    target=self.report_target,
                    row="report_endpoint",
                    model=self.report_model,
                    field=self.report_field,
                )
            )
            field_items.append(
                self._field_item(model=self.report_model, field=self.report_field)
            )
        contract: dict[str, object] = {
            "semantic_item_keys": [
                str(item["judgment_key"]) for item in semantic_items
            ],
            "target_result_declarations": list(targets),
            "target_result_mappings": [
                self._mapping(
                    str(item["judgment_key"]),
                    target_declaration=str(item["qualified_declaration"]),
                    **(
                        {}
                        if legacy
                        else {
                            "model_spec_declaration": (
                                self.optional_model
                                if item["qualified_declaration"] == self.optional_target
                                else self.report_model
                            )
                        }
                    ),
                )
                for item in semantic_items
            ],
            "assumption_mappings": [],
            "semantic_item_mappings": [
                self._mapping(
                    str(item["judgment_key"]),
                    qualified_declaration=str(item["qualified_declaration"]),
                )
                for item in semantic_items
            ],
            "model_field_mappings": [
                self._mapping(str(item["judgment_key"])) for item in field_items
            ],
        }
        if legacy:
            contract["model_spec_declaration"] = self.optional_model
        else:
            contract.update(
                {
                    "model_spec_declarations": [
                        self.optional_model,
                        self.report_model,
                    ],
                    "target_model_spec_declarations": {
                        self.optional_target: self.optional_model,
                        self.report_target: self.report_model,
                    },
                }
            )
        payload: dict[str, object] = {
            "semantic_model_items": semantic_items,
            "expected_semantic_model_judgment_keys": [
                str(item["judgment_key"]) for item in semantic_items
            ],
            "recursive_field_items": field_items,
        }
        return payload, contract

    def _dependency(
        self,
        *,
        target: str,
        record: str,
        field: str,
        path: str | None,
    ) -> dict[str, object]:
        conclusion_field: dict[str, object] = {
            "judgment_key": field,
            "source_antecedent_eligible": True,
            "relation_to_row_result": "",
        }
        if path is not None:
            conclusion_field["path"] = path
        return {
            "kind": "record_conclusion_input",
            "record": record,
            "reviewed_declaration_identity": {
                "qualified_declaration": target,
                "declaration_sha256": sha256(f"declaration:{target}"),
            },
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": target,
                    "elaborated_signature_sha256": sha256(f"signature:{target}"),
                }
            ],
            "conclusion_fields": [conclusion_field],
            "valid_constructors": [],
            "conditional_constructors": [],
            "rejected_constructors": [],
        }

    def _transparent_spec_dependency(
        self,
        *,
        target: str,
        semantic_key: str,
        record: str,
        field: str,
        path: str,
    ) -> dict[str, object]:
        """Build a schema-2 Spec/evidence association without naming heuristics."""

        spec = "Fixture.PaperInterface.TransparentStatementOwner"
        dependency = self._dependency(
            target=spec,
            record=record,
            field=field,
            path=path,
        )
        signature = {
            "qualified_declaration": spec,
            "elaborated_signature_sha256": sha256(f"signature:{spec}"),
        }
        source_identity = {
            "source_key": "fixture_source_theorem",
            "source_location": "source.tex:10-12",
            "source_kind": "theorem",
            "source_map_item_sha256": sha256("fixture source-map item"),
            "source_semantic_sha256": sha256("fixture source semantics"),
            "semantic_contract": {
                "spec_declaration": spec,
                "evidence_declaration": target,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        association: dict[str, object] = {
            "schema": conclusion.SEMANTIC_ASSOCIATION_SCHEMA,
            "association_mode": "semantic_contract_group_member",
            "semantic_model_judgment_key": semantic_key,
            "semantic_contract_member_role": "transparent_spec",
            "reviewed_declaration_identity": dict(
                dependency["reviewed_declaration_identity"]
            ),
            "reviewed_elaborated_signature_identity": signature,
            "source_item_identities": [source_identity],
            "source_map_item_keys": [source_identity["source_key"]],
            "source_map_item_sha256_by_key": {
                source_identity["source_key"]: source_identity[
                    "source_map_item_sha256"
                ]
            },
            "source_map_item_keys_sha256": (
                conclusion.source_map_item_record_digest(
                    [source_identity["source_key"]]
                )
            ),
        }
        association["semantic_association_sha256"] = (
            conclusion.semantic_association_record_digest(
                [source_identity["source_semantic_sha256"]], signature
            )
        )
        association["association_sha256"] = (
            conclusion.source_contract_association_record_digest(association)
        )
        dependency["source_contract_association"] = association
        return dependency

    def test_conclusion_bridge_separates_disjoint_target_models(self) -> None:
        payload, contract = self._conclusion_payload()
        scope = self._multi_scope()
        status = {"review_surface": {"assumption_names": []}}
        with (
            mock.patch.object(conclusion, "load_payload", return_value=status),
            mock.patch.object(
                conclusion,
                "_current_corrected_contract",
                return_value=(contract, scope),
            ),
        ):
            bridge = conclusion.corrected_model_conclusion_bridge("Fixture", payload)

        self.assertIsNotNone(bridge)
        assert bridge is not None
        governing_roots = {
            row.qualified_declaration: row.governing_model_spec_declaration
            for row in bridge.rows
        }
        self.assertEqual(
            governing_roots,
            {
                self.optional_target: self.optional_model,
                self.report_target: self.report_model,
            },
        )
        self.assertTrue(
            conclusion.corrected_model_dependency_is_covered(
                bridge,
                self._dependency(
                    target=self.optional_target,
                    record=self.optional_model,
                    field=self.optional_field,
                    path=f"{self.optional_model} -> {self.optional_field}",
                ),
            )
        )
        self.assertTrue(
            conclusion.corrected_model_dependency_is_covered(
                bridge,
                self._dependency(
                    target=self.report_target,
                    record=self.report_model,
                    field=self.report_field,
                    path=f"{self.report_model} -> {self.report_field}",
                ),
            )
        )
        self.assertFalse(
            conclusion.corrected_model_dependency_is_covered(
                bridge,
                self._dependency(
                    target=self.report_target,
                    record=self.paired_model,
                    field=self.report_field,
                    path=f"{self.paired_model} -> {self.report_field}",
                ),
            )
        )
        self.assertFalse(
            conclusion.corrected_model_dependency_is_covered(
                bridge,
                self._dependency(
                    target=self.report_target,
                    record=self.report_model,
                    field=self.optional_field,
                    path=f"{self.report_model} -> {self.optional_field}",
                ),
            )
        )

    def test_conclusion_bridge_uses_exact_transparent_spec_association(self) -> None:
        payload, contract = self._conclusion_payload()
        scope = self._multi_scope()
        status = {"review_surface": {"assumption_names": []}}
        with (
            mock.patch.object(conclusion, "load_payload", return_value=status),
            mock.patch.object(
                conclusion,
                "_current_corrected_contract",
                return_value=(contract, scope),
            ),
        ):
            bridge = conclusion.corrected_model_conclusion_bridge("Fixture", payload)

        assert bridge is not None
        dependency = self._transparent_spec_dependency(
            target=self.optional_target,
            semantic_key="semantic-model::optional_endpoint",
            record=self.optional_model,
            field=self.optional_field,
            path=f"{self.optional_model} -> {self.optional_field}",
        )
        self.assertTrue(
            conclusion.corrected_model_dependency_is_covered(bridge, dependency)
        )

    def test_transparent_spec_association_mismatches_fail_closed(self) -> None:
        payload, contract = self._conclusion_payload()
        scope = self._multi_scope()
        status = {"review_surface": {"assumption_names": []}}
        with (
            mock.patch.object(conclusion, "load_payload", return_value=status),
            mock.patch.object(
                conclusion,
                "_current_corrected_contract",
                return_value=(contract, scope),
            ),
        ):
            bridge = conclusion.corrected_model_conclusion_bridge("Fixture", payload)
        assert bridge is not None

        def base_dependency() -> dict[str, object]:
            return self._transparent_spec_dependency(
                target=self.optional_target,
                semantic_key="semantic-model::optional_endpoint",
                record=self.optional_model,
                field=self.optional_field,
                path=f"{self.optional_model} -> {self.optional_field}",
            )

        def refresh_association_digest(dependency: dict[str, object]) -> None:
            association = dependency["source_contract_association"]
            assert isinstance(association, dict)
            association["association_sha256"] = (
                conclusion.source_contract_association_record_digest(association)
            )

        cases: dict[str, object] = {
            "wrong semantic row": lambda association: association.__setitem__(
                "semantic_model_judgment_key", "semantic-model::report_endpoint"
            ),
            "wrong evidence theorem": lambda association: association[
                "source_item_identities"
            ][0]["semantic_contract"].__setitem__(
                "evidence_declaration", self.report_target
            ),
            "wrong member role": lambda association: association.__setitem__(
                "semantic_contract_member_role", "direct_evidence"
            ),
        }
        for label, mutate in cases.items():
            with self.subTest(label=label):
                dependency = base_dependency()
                association = dependency["source_contract_association"]
                assert isinstance(association, dict)
                assert callable(mutate)
                mutate(association)
                refresh_association_digest(dependency)
                self.assertFalse(
                    conclusion.corrected_model_dependency_is_covered(
                        bridge, dependency
                    )
                )

        dependency = base_dependency()
        association = dependency["source_contract_association"]
        assert isinstance(association, dict)
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(signature, dict)
        signature["elaborated_signature_sha256"] = sha256("mismatched Spec signature")
        association["semantic_association_sha256"] = (
            conclusion.semantic_association_record_digest(
                [
                    association["source_item_identities"][0][
                        "source_semantic_sha256"
                    ]
                ],
                signature,
            )
        )
        refresh_association_digest(dependency)
        self.assertFalse(
            conclusion.corrected_model_dependency_is_covered(bridge, dependency)
        )

    def test_conclusion_bridge_keeps_legacy_scalar_scope(self) -> None:
        payload, contract = self._conclusion_payload(legacy=True)
        scope = self._legacy_scope()
        status = {"review_surface": {"assumption_names": []}}
        with (
            mock.patch.object(conclusion, "load_payload", return_value=status),
            mock.patch.object(
                conclusion,
                "_current_corrected_contract",
                return_value=(contract, scope),
            ),
        ):
            bridge = conclusion.corrected_model_conclusion_bridge("Fixture", payload)

        self.assertIsNotNone(bridge)
        assert bridge is not None
        # Legacy records did not retain a field-path receipt on every
        # dependency. Keep their original scalar-root compatibility path.
        self.assertTrue(
            conclusion.corrected_model_dependency_is_covered(
                bridge,
                self._dependency(
                    target=self.optional_target,
                    record=self.optional_model,
                    field=self.optional_field,
                    path=None,
                ),
            )
        )


    def test_repository_premise_bridge_rejects_a_paired_model_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit_folder = folder / "audit"
            audit_folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture.PaperInterface\n"
                "theorem optional_endpoint : True := by trivial\n"
                "theorem report_endpoint : True := by trivial\n"
                "end Fixture.PaperInterface\n",
                encoding="utf-8",
            )
            interface_sha = hashlib.sha256(interface.read_bytes()).hexdigest()
            semantic_items = [
                self._semantic_item(
                    target=self.optional_target,
                    row="optional_endpoint",
                    model=self.optional_model,
                    field=self.optional_field,
                    include_input_binding=True,
                ),
                self._semantic_item(
                    target=self.report_target,
                    row="report_endpoint",
                    model=self.report_model,
                    field=self.report_field,
                    include_input_binding=True,
                ),
            ]
            field_items = [
                self._field_item(model=self.optional_model, field=self.optional_field),
                self._field_item(model=self.report_model, field=self.report_field),
            ]
            audit_payload = {
                "recursive_field_items": field_items,
                "expected_semantic_model_judgment_keys": [
                    str(item["judgment_key"]) for item in semantic_items
                ],
                "semantic_model_items": semantic_items,
                "configured_review_rows": [
                    {
                        "qualified_declaration": target,
                        "source_file": str(interface.resolve()),
                        "source_sha256": interface_sha,
                        "elaborated_signature_sha256": sha256(
                            f"configured-signature:{target}"
                        ),
                    }
                    for target in self._targets()
                ],
            }
            (audit_folder / "source_record_audit.json").write_text(
                json.dumps(audit_payload), encoding="utf-8"
            )
            contract = {
                "target_result_mappings": [
                    {
                        "source_record_item_key": str(item["judgment_key"]),
                        "target_declaration": str(item["qualified_declaration"]),
                        "model_spec_declaration": (
                            self.optional_model
                            if item["qualified_declaration"] == self.optional_target
                            else self.report_model
                        ),
                    }
                    for item in semantic_items
                ],
                "assumption_mappings": [],
                "semantic_item_mappings": [
                    {
                        "source_record_item_key": str(item["judgment_key"]),
                        "qualified_declaration": str(item["qualified_declaration"]),
                    }
                    for item in semantic_items
                ],
            }
            (audit_folder / "contract.json").write_text(
                json.dumps(contract), encoding="utf-8"
            )
            status = {
                "review_surface": {},
                "formalization_scope": {
                    **self._multi_scope(),
                    "semantic_contract": {"path": "audit/contract.json"},
                },
            }
            mapped_fields = {
                str(item["judgment_key"]): item for item in field_items
            }
            with mock.patch.object(
                repository,
                "current_corrected_model_contract_field_items",
                return_value=mapped_fields,
            ):
                bridge = repository.current_corrected_model_premise_bridge(
                    folder, status
                )

                self.assertIsNotNone(bridge)
                assert bridge is not None
                self.assertEqual(
                    bridge.declaration_bindings[self.optional_target][1][0]
                    .governing_model_spec_declaration,
                    self.optional_model,
                )
                self.assertEqual(
                    bridge.declaration_bindings[self.report_target][1][0]
                    .governing_model_spec_declaration,
                    self.report_model,
                )

                paired_audit = deepcopy(audit_payload)
                paired_item = paired_audit["semantic_model_items"][1]
                assert isinstance(paired_item, dict)
                paired_bindings = paired_item["record_input_bindings"]
                assert isinstance(paired_bindings, list)
                paired_binding = paired_bindings[0]
                assert isinstance(paired_binding, dict)
                paired_binding["record_roots"] = [
                    self.report_model,
                    self.paired_model,
                ]
                (audit_folder / "source_record_audit.json").write_text(
                    json.dumps(paired_audit), encoding="utf-8"
                )
                self.assertIsNone(
                    repository.current_corrected_model_premise_bridge(folder, status)
                )

    def test_current_contract_normalizes_multi_model_and_legacy_shapes(self) -> None:
        for legacy in (False, True):
            targets = (self.optional_target,) if legacy else self._targets()
            model_shape: dict[str, object]
            if legacy:
                model_shape = {"model_spec_declaration": self.optional_model}
            else:
                model_shape = {
                    "model_spec_declarations": [
                        self.optional_model,
                        self.report_model,
                    ],
                    "target_model_spec_declarations": {
                        self.optional_target: self.optional_model,
                        self.report_target: self.report_model,
                    },
                }
            with tempfile.TemporaryDirectory() as temp_dir:
                folder = Path(temp_dir) / "Fixture"
                (folder / "audit").mkdir(parents=True)
                audit_scope = {
                    "kind": "approved_corrected_model",
                    "scope_id": "fixture-scope",
                    "approval_artifact_sha256": sha256("approval"),
                    "base_archive_sha256": sha256("archive"),
                    "target_result_declarations": list(targets),
                    "correction_ids": ["FIXTURE-1"],
                    "archival_equivalence_claimed": False,
                    "scope_sha256": sha256("scope"),
                    **model_shape,
                }
                contract = {
                    "source_record_audit_sha256": sha256("raw audit"),
                    "source_record_audit_integrity_sha256": sha256("integrity"),
                    "source_record_scope_sha256": sha256("scope"),
                    "scope_id": "fixture-scope",
                    "target_result_declarations": list(targets),
                    **model_shape,
                }
                contract_path = folder / "audit" / "contract.json"
                contract_path.write_text(json.dumps(contract), encoding="utf-8")
                scope = {
                    "kind": "approved_corrected_model",
                    "scope_id": "fixture-scope",
                    "approval": {"artifact_sha256": sha256("approval")},
                    "base_archive": {"sha256": sha256("archive")},
                    "target_result_declarations": list(targets),
                    "correction_ids": ["FIXTURE-1"],
                    "semantic_contract": {
                        "path": "audit/contract.json",
                        "sha256": hashlib.sha256(contract_path.read_bytes()).hexdigest(),
                    },
                    **model_shape,
                }
                audit_payload = {
                    "prompt_version": conclusion.SOURCE_RECORD_PROMPT_VERSION,
                    "formalization_scope": audit_scope,
                    "source_record_audit_sha256": sha256("raw audit"),
                    "source_record_audit_integrity_sha256": sha256("integrity"),
                }
                with (
                    mock.patch.object(
                        conclusion,
                        "author_approved_corrected_scope_contract_is_current",
                        return_value=True,
                    ),
                    mock.patch.object(
                        conclusion,
                        "author_approved_corrected_scope",
                        return_value=scope,
                    ),
                ):
                    current = conclusion._current_corrected_contract(
                        folder, {}, audit_payload
                    )

            self.assertIsNotNone(current)
            assert current is not None
            self.assertEqual(current[0], contract)
            self.assertEqual(current[1], scope)


if __name__ == "__main__":
    unittest.main()
