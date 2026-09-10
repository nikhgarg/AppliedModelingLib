from __future__ import annotations

import hashlib
import json
import unittest
from pathlib import Path

from scripts import public_release_projection as projection
from scripts.corrected_target_identity import (
    CORRECTED_TARGET_RECORD_SHA256_FIELD,
    CORRECTED_TARGET_REVIEW_SHA256_FIELD,
    corrected_target_record_digest,
    corrected_target_review_digest,
)
from scripts.source_coverage_scope import source_map_structural_errors


def _corrected_target(
    statement: str = "For every feasible allocation, welfare is at most the displayed benchmark.",
) -> dict[str, object]:
    excerpt = (
        "Private approval record quoted a user instruction and identified a local "
        "source.tar.gz file; none of this prose belongs in the public source map."
    )
    approval = {
        "artifact_path": "docs/PRIVATE_APPROVAL_MEMO.md",
        "artifact_protocol": "unique_normalized_artifact_excerpt_v1",
        "artifact_excerpt": excerpt,
        "artifact_excerpt_sha256": hashlib.sha256(excerpt.encode()).hexdigest(),
        "kind": "recorded_user_direction",
        "recorded_at": "2026-09-07",
        "reference": "/home/reviewer/private approval notes",
        "target_statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
    }
    target: dict[str, object] = {
        "schema": 1,
        "statement": statement,
        "archival_equivalence_claimed": False,
        "archival_source_locator": "Theorem 1",
        "archival_source_quote_sha256": "a" * 64,
        "governing_defect_ids": ["D1"],
        "approval": approval,
    }
    target[CORRECTED_TARGET_RECORD_SHA256_FIELD] = corrected_target_record_digest(target)
    target[CORRECTED_TARGET_REVIEW_SHA256_FIELD] = corrected_target_review_digest(target)
    return target


class PublicReleaseProjectionTests(unittest.TestCase):
    def test_packet_mixed_indentation_preserves_quote_text_and_alignment(self):
        raw = "\\begin{ReviewVerbatim}\n    \t\\lambda(x) >= 0\n\\end{ReviewVerbatim}\n"
        self.assertEqual(
            projection.project_text(raw, relative_path="papers/Fixture/docs/HUMAN_REVIEW_PACKET.tex"),
            raw.replace("    \t", "        "),
        )
        self.assertEqual(
            projection.project_text(raw, relative_path="papers/Fixture/docs/MEMO.tex"),
            raw,
        )

    def test_reader_inventory_locations_preserve_claims_without_local_paths(self):
        payload = {
            "canonical_source_path": "sources/source_archive_surface.tex",
            "source_label": "Appendix B example (sources/paper.txt:1333-1385)",
            "grouping_reason": "Section 4 states stability at source.txt:232–249.",
            "source_sha256": "a" * 64,
        }
        public = projection.project_json_payload(
            payload, relative_path="papers/Fixture/docs/REPORT_MEMO_COVERAGE.json"
        )
        self.assertEqual(public["canonical_source_path"], "cited publication")
        self.assertEqual(public["source_label"], "Appendix B example (cited publication:1333-1385)")
        self.assertIn("Section 4 states stability at cited publication", public["grouping_reason"])
        self.assertEqual(public["source_sha256"], payload["source_sha256"])

    def test_status_omits_historical_review_surface_but_preserves_current_route(self):
        payload = {"artifacts": {
            "legacy_review_surface": "LegacyReviewSurface.lean",
            "review_surface": "PaperInterface.lean",
        }}
        self.assertEqual(
            projection.project_json_payload(payload, relative_path="papers/Fixture/status.json"),
            {"artifacts": {"review_surface": "PaperInterface.lean"}},
        )
        self.assertEqual(
            projection.project_json_payload(payload, relative_path="config/fixture.json"),
            payload,
        )

    def test_report_evidence_links_use_current_closeout_without_changing_claims(self):
        raw = (
            "Theorem 1: **Exact.**\n"
            "[Source review](audit/v11_raw_source_spec_screening.json)\n"
            "[Statement map](audit/paper_statement_map.json)\n"
            "[Clarification](docs/SOURCE_CLARIFICATIONS.md#theorem-2)\n"
        )
        public = projection.project_text(
            raw, relative_path="papers/Fixture/FINAL_VALIDATION_REPORT.md"
        )
        self.assertEqual(
            public,
            raw.replace(
                "](audit/v11_raw_source_spec_screening.json)",
                "](FINAL_CLOSURE_RECEIPT.md)",
            ),
        )
        self.assertEqual(
            projection.project_text(raw, relative_path="papers/Fixture/docs/MEMO.md"),
            raw,
        )
        receipt = (
            '+++\nschema = 6\n[accepted_graph]\n'
            'pointer = "papers/Fixture/audit/obligation_evidence/current_accepted_graph.json"\n'
            '+++\n\n# Final closure receipt\n\nCurrent accepted graph.\n'
        )
        exported = projection.project_text(
            receipt, relative_path="papers/Fixture/FINAL_CLOSURE_RECEIPT.md"
        )
        self.assertTrue(exported.startswith(receipt))
        self.assertIn(
            "[Accepted review and proof record](audit/obligation_evidence/current_accepted_graph.json)",
            exported,
        )
        self.assertEqual(
            projection.project_text(exported, relative_path="papers/Fixture/FINAL_CLOSURE_RECEIPT.md"),
            exported,
        )

    def test_scope_and_support_approval_history_is_withheld_without_changing_scope(self):
        payload = {"items": {"claim": {
            "coverage_status": "out_of_scope",
            "user_approved_scope_exclusion": {
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "Private user exchange: leave this result for later.",
                "reason": "The numerical example is outside the selected theorem scope.",
            },
            "deep_support_repair": {
                "statement": "For every feasible allocation, the displayed bound holds.",
                "approval": {"reference": "Private user quotation", "recorded_at": "2026-01-01"},
            },
        }}}
        projected = json.loads(projection.project_bytes(
            "papers/Fixture/audit/paper_statement_map.json", json.dumps(payload).encode()
        ))
        row = projected["items"]["claim"]
        self.assertEqual(row["coverage_status"], "out_of_scope")
        self.assertEqual(row["user_approved_scope_exclusion"]["reason"],
                         payload["items"]["claim"]["user_approved_scope_exclusion"]["reason"])
        self.assertEqual(row["user_approved_scope_exclusion"]["approval_reference"],
                         projection.PUBLIC_WITHHELD_APPROVAL_REFERENCE)
        self.assertEqual(row["deep_support_repair"]["statement"],
                         payload["items"]["claim"]["deep_support_repair"]["statement"])
        self.assertNotIn("Private user", json.dumps(projected))
        self.assertIn("private_record_sha256", row["deep_support_repair"]["approval"])

    def test_json_projection_preserves_source_evidence_without_private_workflow(self) -> None:
        source_sha256 = "a" * 64
        quote = "Verbatim source excerpt: each allocation assigns each item."
        quote_sha256 = hashlib.sha256(quote.encode("utf-8")).hexdigest()
        payload = {
            "paper": "Fixture",
            "source_url": "https://arxiv.org/abs/2405.16762",
            "source_version": (
                "arXiv:2405.16762; exact audit extraction recorded separately "
                "from the older tracked text extraction"
            ),
            "source_artifact_path": ".audit_source/Fixture.txt",
            "source_artifact_sha256": source_sha256,
            "source_artifact_provisioning": {
                "audit_path": "papers/Fixture/.audit_source/Fixture.txt",
                "origin_path": "/tmp/econcs_source_text/Fixture.txt",
            },
            "canonical_source_audit": {
                "path": "papers/Fixture/.audit_source/Fixture.txt",
                "sha256": source_sha256,
            },
            "source_inventory_policy": (
                "The exact extraction /tmp/econcs_source_text/Fixture.txt "
                f"(SHA256 {source_sha256}) is the source record."
            ),
            "llm_judge_prompt": (
                "Compare the source anchor at .audit_source/Fixture.txt:12-15 "
                "with the expanded Lean proposition."
            ),
            "source_text_companion": {
                "canonical_text": {"path": "source.txt", "sha256": source_sha256},
                "visual_comparison_attestation": {
                    "method": "The private text extraction was checked against the primary scan."
                },
                "page_map": [{"line_start": 12, "line_end": 15, "pdf_page": 2}],
            },
            "source_archive_surface": {
                "archive": {"path": "source_arxiv.tar", "sha256": source_sha256}
            },
            "signature_cache": "papers/Fixture/.review_traces/rows.json",
            "items": {
                "claim": {
                    "statement": "The mathematical claim is unchanged.",
                    "source_url": "https://arxiv.org/abs/2405.16762",
                    "source_location": ".audit_source/Fixture.txt:12-15",
                    "source_anchor_evidence": [
                        {
                            "path": ".audit_source/Fixture.txt",
                            "line_start": 12,
                            "line_end": 15,
                            "quoted_text": quote,
                            "quoted_text_sha256": quote_sha256,
                        }
                    ],
                    "source_note": "The unresolved mathematical handoff is retained in the deep observation.",
                    "source_locator": "Theorem 1; .audit_source/Fixture.txt:12-15",
                    "source_restatement_evidence": {
                        "path": "source.txt",
                        "line_start": 12,
                        "line_end": 15,
                        "quoted_text": quote,
                        "quoted_text_sha256": quote_sha256,
                    },
                }
            },
            "defects": [
                {
                    "affected_source_locators": [
                        ".audit_source/Fixture.txt:12-15"
                    ],
                    "source_artifact_identities": [
                        {"path": ".audit_source/Fixture.txt", "sha256": source_sha256}
                    ],
                }
            ],
            "review_surface": {
                "source_proof_fidelity_review": {
                    "policy": "Keep the remediation handoff current before closeout."
                }
            },
            "artifacts": {
                "source_fidelity_remediation": "docs/SOURCE_FIDELITY_REMEDIATION.md"
            },
            "remediation_scope": {"kind": "remediation_closed"},
            "deep_audit_observations": [
                {
                    "repair_handoff": (
                        "A future source review should state the computational model."
                    )
                }
            ],
        }

        raw = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        first = projection.project_bytes(
            "papers/Fixture/audit/paper_statement_map.json",
            raw,
            include_source_display_marker=True,
        )
        second = projection.project_bytes(
            "papers/Fixture/audit/paper_statement_map.json",
            raw,
            include_source_display_marker=True,
        )
        self.assertEqual(first, second)

        projected = json.loads(first)
        self.assertNotIn("source_artifact_path", projected)
        self.assertNotIn("source_artifact_provisioning", projected)
        self.assertNotIn("canonical_source_audit", projected)
        self.assertNotIn("source_archive_surface", projected)
        self.assertNotIn("signature_cache", projected)
        self.assertEqual(projected["source_artifact_sha256"], source_sha256)
        self.assertEqual(projected["source_url"], payload["source_url"])
        self.assertNotIn("private source extraction", projected["source_version"].lower())
        self.assertEqual(projected["source_version"], "cited publication source record")
        self.assertIn(source_sha256, projected["source_inventory_policy"])
        self.assertNotIn(".audit_source", projected["llm_judge_prompt"])
        # A companion has no useful public meaning once its byte paths are
        # deliberately withheld.  Its retained hash would otherwise look like
        # a locally re-verifiable source record, so the public projection omits
        # the whole private-only companion rather than leaving a malformed
        # pathless schema fragment.
        self.assertNotIn("source_text_companion", projected)
        marker = projected[projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD]
        self.assertEqual(marker["schema"], projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA)
        self.assertEqual(
            marker["manifest"], projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST
        )
        self.assertFalse(marker["raw_source_bytes_included"])

        unmarked = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json", raw
            )
        )
        self.assertNotIn(projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD, unmarked)
        anchor = projected["items"]["claim"]["source_anchor_evidence"][0]
        self.assertNotIn("path", anchor)
        self.assertEqual(anchor["publication_locator"], projection.PUBLICATION_LOCATOR)
        self.assertEqual(anchor["line_start"], 12)
        self.assertEqual(anchor["line_end"], 15)
        self.assertEqual(anchor["quoted_text"], quote)
        self.assertEqual(anchor["quoted_text_sha256"], quote_sha256)
        self.assertEqual(
            projected["items"]["claim"]["source_location"], "publication text:12-15"
        )
        self.assertIn(
            "remaining mathematical issue", projected["items"]["claim"]["source_note"]
        )
        self.assertNotIn(
            ".audit_source", projected["items"]["claim"]["source_locator"]
        )
        restatement = projected["items"]["claim"]["source_restatement_evidence"]
        self.assertNotIn("path", restatement)
        self.assertEqual(restatement["publication_locator"], projection.PUBLICATION_LOCATOR)
        self.assertNotIn(
            ".audit_source",
            projected["defects"][0]["affected_source_locators"][0],
        )
        self.assertEqual(
            projected["defects"][0]["source_artifact_identities"][0]["path"],
            projection.PUBLICATION_LOCATOR,
        )
        self.assertIn(
            "source-review record",
            projected["review_surface"]["source_proof_fidelity_review"]["policy"],
        )
        self.assertIn("source_fidelity_review", projected["artifacts"])
        self.assertNotIn("source_fidelity_remediation", projected["artifacts"])
        self.assertEqual(projected["review_scope"]["kind"], "review_complete")
        self.assertNotIn("repair_handoff", projected["deep_audit_observations"][0])
        self.assertIn("scope_note", projected["deep_audit_observations"][0])

    def test_unknown_unsafe_json_content_fails_closed(self) -> None:
        payload = {
            "paper": "Fixture",
            "ordinary_note": "The worktree receipt is stored at /tmp/private-note.txt.",
        }
        with self.assertRaisesRegex(projection.ProjectionError, "ordinary_note"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_nested_object_below_quote_field_is_not_a_source_excerpt_bypass(self) -> None:
        payload = {"quoted_text": {"hidden": "/tmp/private-record.txt"}}
        with self.assertRaisesRegex(projection.ProjectionError, "hidden"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_scalar_quote_requires_a_bound_source_record(self) -> None:
        payload = {"quoted_text": "/tmp/private-record.txt"}
        with self.assertRaisesRegex(projection.ProjectionError, "quoted_text"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_bound_quote_in_an_arbitrary_audit_file_cannot_bypass_hygiene(self) -> None:
        quote = "/home/nkgarg/secret-private-workflow"
        payload = {
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
            "publication_locator": "https://arxiv.org/abs/1234.5678",
            "line_start": 1,
            "line_end": 1,
        }
        with self.assertRaisesRegex(projection.ProjectionError, "local /tmp or /home path"):
            projection.project_bytes(
                "papers/Fixture/audit/record.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_bound_source_anchor_cannot_publish_a_local_workstation_path(self) -> None:
        quote = "/home/nkgarg/secret-private-workflow"
        payload = {
            "items": {
                "claim": {
                    "source_anchor": {
                        "path": "source.txt",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": quote,
                        "quoted_text_sha256": hashlib.sha256(
                            quote.encode("utf-8")
                        ).hexdigest(),
                    }
                }
            }
        }
        with self.assertRaisesRegex(projection.ProjectionError, "local /tmp or /home path"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_source_item_id_suffix_does_not_change_nested_anchor_projection(self) -> None:
        quote = "Algorithm 5 selects the current comparison pivot."
        payload = {
            "items": {
                "algorithm5_pick_anchor": {
                    "source_kind": "algorithm",
                    "source_anchor_evidence": [
                        {
                            "path": "sources/fixture.txt",
                            "line_start": 5,
                            "line_end": 5,
                            "quoted_text": quote,
                            "quoted_text_sha256": hashlib.sha256(
                                quote.encode("utf-8")
                            ).hexdigest(),
                        }
                    ],
                }
            }
        }

        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )
        )
        item = projected["items"]["algorithm5_pick_anchor"]
        self.assertEqual(item["source_kind"], "algorithm")
        anchor = item["source_anchor_evidence"][0]
        self.assertNotIn("path", anchor)
        self.assertEqual(anchor["publication_locator"], projection.PUBLICATION_LOCATOR)
        self.assertEqual(anchor["quoted_text"], quote)

    def test_source_item_id_suffix_does_not_grant_excerpt_safety_privileges(self) -> None:
        quote = "The record refers to source.tar.gz."
        payload = {
            "items": {
                "algorithm5_pick_anchor": {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                }
            }
        }

        with self.assertRaisesRegex(
            projection.ProjectionError, "non-public source artifact locator"
        ):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_corrected_target_projection_withholds_approval_and_preserves_identities(
        self,
    ) -> None:
        target = _corrected_target()
        payload = {
            "items": {
                "claim": {
                    "coverage_status": "subsumed_by_selected_result",
                    "corrected_target": target,
                }
            }
        }

        projected_bytes = projection.project_bytes(
            "papers/Fixture/audit/paper_statement_map.json",
            json.dumps(payload).encode("utf-8"),
            include_source_display_marker=True,
        )
        projected = json.loads(projected_bytes)
        public_target = projected["items"]["claim"]["corrected_target"]
        self.assertNotIn("approval", public_target)
        self.assertEqual(public_target["statement"], target["statement"])
        self.assertEqual(
            public_target[CORRECTED_TARGET_RECORD_SHA256_FIELD],
            target[CORRECTED_TARGET_RECORD_SHA256_FIELD],
        )
        self.assertEqual(
            public_target[CORRECTED_TARGET_REVIEW_SHA256_FIELD],
            target[CORRECTED_TARGET_REVIEW_SHA256_FIELD],
        )
        self.assertEqual(
            projected[projection.PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD],
            {
                "schema": projection.PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
                "approval_material_included": False,
            },
        )
        self.assertIn(projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD, projected)
        self.assertNotIn("Private approval record", projected_bytes.decode("utf-8"))
        self.assertNotIn("PRIVATE_APPROVAL_MEMO", projected_bytes.decode("utf-8"))

    def test_corrected_target_projection_rejects_stale_private_bindings(self) -> None:
        cases = {
            "record": (
                lambda target: target.__setitem__(
                    CORRECTED_TARGET_RECORD_SHA256_FIELD, "0" * 64
                ),
                CORRECTED_TARGET_RECORD_SHA256_FIELD,
            ),
            "review": (
                lambda target: target.__setitem__(
                    CORRECTED_TARGET_REVIEW_SHA256_FIELD, "0" * 64
                ),
                CORRECTED_TARGET_REVIEW_SHA256_FIELD,
            ),
            "excerpt": (
                lambda target: (
                    target["approval"].__setitem__("artifact_excerpt_sha256", "0" * 64),
                    target.__setitem__(
                        CORRECTED_TARGET_RECORD_SHA256_FIELD,
                        corrected_target_record_digest(target),
                    ),
                ),
                "approval excerpt authority",
            ),
            "statement": (
                lambda target: (
                    target["approval"].__setitem__("target_statement_sha256", "0" * 64),
                    target.__setitem__(
                        CORRECTED_TARGET_RECORD_SHA256_FIELD,
                        corrected_target_record_digest(target),
                    ),
                ),
                "target_statement_sha256",
            ),
            "artifact_path": (
                lambda target: (
                    target["approval"].__setitem__(
                        "artifact_path", "docs/../PRIVATE_APPROVAL.md"
                    ),
                    target.__setitem__(
                        CORRECTED_TARGET_RECORD_SHA256_FIELD,
                        corrected_target_record_digest(target),
                    ),
                ),
                "noncanonical private approval artifact_path",
            ),
            "original_artifact_path": (
                lambda target: (
                    target["approval"].__setitem__(
                        "original_artifact_path",
                        target["approval"]["artifact_path"],
                    ),
                    target.__setitem__(
                        CORRECTED_TARGET_RECORD_SHA256_FIELD,
                        corrected_target_record_digest(target),
                    ),
                ),
                "original_artifact_path",
            ),
        }
        for name, (mutate, expected) in cases.items():
            with self.subTest(name=name):
                target = _corrected_target()
                mutate(target)
                payload = {"items": {"claim": {"corrected_target": target}}}
                with self.assertRaisesRegex(projection.ProjectionError, expected):
                    projection.project_bytes(
                        "papers/Fixture/audit/paper_statement_map.json",
                        json.dumps(payload).encode("utf-8"),
                    )

    def test_corrected_target_projection_never_rewrites_mathematical_statement(
        self,
    ) -> None:
        target = _corrected_target(
            "The formal claim refers literally to source.tar.gz as part of its proposition."
        )
        payload = {"items": {"claim": {"corrected_target": target}}}

        with self.assertRaisesRegex(
            projection.ProjectionError, "would change corrected target statement"
        ):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_private_url_is_rejected_before_public_url_masking(self) -> None:
        payload = {
            "reference_url": "https://github.com/nikhgarg/EconCSLib-private/tree/main/tmp/secret"
        }
        with self.assertRaisesRegex(projection.ProjectionError, "private repository"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_percent_encoded_private_url_is_rejected_before_public_url_masking(self) -> None:
        payload = {
            "reference_url": "https://github.com/nikhgarg/EconCSLib%2Dprivate/tree/main"
        }
        with self.assertRaisesRegex(projection.ProjectionError, "private repository"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_html_entity_encoded_private_url_is_rejected_before_public_url_masking(self) -> None:
        payload = {
            "reference_url": "https://github.com/nikhgarg/EconCSLib&#45;private/tree/main"
        }
        with self.assertRaisesRegex(projection.ProjectionError, "private repository"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_already_public_safe_json_keeps_its_exact_bytes(self) -> None:
        raw = b'{"paper":"Fixture", "source_url":"https://arxiv.org/abs/1"}\n'
        self.assertEqual(
            projection.project_bytes("papers/Fixture/status.json", raw), raw
        )

    def test_text_projection_rewrites_known_workflow_labels(self) -> None:
        raw = (
            "\\textbf{Source version:} arXiv source; byte-pinned private text extraction\\\\\n"
            "The remediation handoff references /tmp/econcslib/source.txt.\n"
        ).encode("utf-8")
        projected = projection.project_bytes("papers/Fixture/docs/HUMAN_REVIEW_PACKET.tex", raw)
        text = projected.decode("utf-8")
        self.assertNotIn("private text extraction", text.lower())
        self.assertNotIn("remediation handoff", text.lower())
        self.assertNotIn("/tmp/", text)
        self.assertIn("publication source record", text)

        notes = projection.project_bytes(
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.tex",
            b"Local workflow: PAPER_NOTES.md\n",
        ).decode("utf-8")
        self.assertNotIn("PAPER_NOTES", notes)
        self.assertIn("source-review record", notes)

        workflow = projection.project_bytes(
            "site/index.html",
            (
                b"New paper formalizations should start in a private workflow and be\n"
                b"            proposed to enter the library through a pull request when ready.\n"
            ),
        ).decode("utf-8")
        self.assertIn("private workflow", workflow)

        repository = projection.project_bytes(
            "docs/ordinary-guide.md",
            b"Work in a private repository until the branch is ready.\n",
        ).decode("utf-8")
        self.assertNotIn("private repository", repository)
        self.assertIn("development repository", repository)

        tutorial = b'SOURCE_ARTIFACT=".scratch/$PAPER/source.pdf"\n'
        public_tutorial = projection.project_bytes(
            "docs/ordinary-guide.md", tutorial
        ).decode("utf-8")
        self.assertNotIn(".scratch", public_tutorial)
        self.assertNotIn("source.pdf", public_tutorial)
        self.assertIn("cited publication", public_tutorial)

        navigation = projection.project_bytes(
            "docs/PUBLIC_RELEASE_CHECKLIST.md",
            b"Open site/index.html and compile docs/DependencyDAG.tex.\n",
        ).decode("utf-8")
        self.assertIn("site/index.html", navigation)
        self.assertIn("docs/DependencyDAG.tex", navigation)
        self.assertNotIn("cited publication", navigation)

    def test_public_http_source_url_is_not_rewritten_as_a_local_locator(self) -> None:
        url = "https://arxiv.org/e-print/2601.00001/source/main.tex"
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps({"source_url": url}).encode("utf-8"),
            )
        )
        self.assertEqual(projected["source_url"], url)

    def test_ordinary_html_namespace_and_packet_pdf_path_are_not_source_locators(self) -> None:
        payload = {
            "lean_import_closure": {"external_import_modules": ["ProofWidgets.Data.Html"]},
            "artifacts": {
                "human_review_packet_pdf": (
                    "papers/Fixture/docs/HUMAN_REVIEW_PACKET.pdf"
                )
            },
        }
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_record_audit.json",
                json.dumps(payload).encode("utf-8"),
            )
        )
        self.assertEqual(projected, payload)

    def test_lean_comment_projection_neutralizes_private_transcript_locator(self) -> None:
        raw = (
            b"/-- Source anchor: source_tex/sections/theorem.tex, lines 2--18. -/\n"
            b"def semantic_target : Prop := True\n"
        )
        projected = projection.project_bytes(
            "papers/Fixture/Assumptions.lean", raw
        ).decode("utf-8")
        self.assertNotIn("source_tex/sections/theorem.tex", projected)
        self.assertIn(projection.PUBLICATION_LOCATOR, projected)
        self.assertIn("def semantic_target : Prop := True", projected)

    def test_source_evidence_keeps_its_mathematical_summary_without_private_notes(self) -> None:
        payload = {
            "source_evidence": (
                "Source basis: /tmp/econcs_source_text/Fixture.txt, PAPER_NOTES.md, "
                "and local PDF cache. Lemma 1 assumes a finite item universe."
            )
        }

        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_coverage_llm.json",
                json.dumps(payload).encode("utf-8"),
            )
        )

        evidence = projected["source_evidence"]
        self.assertIn("Lemma 1 assumes a finite item universe.", evidence)
        self.assertNotIn("/tmp", evidence)
        self.assertNotIn("PAPER_NOTES", evidence)
        self.assertNotIn("local PDF cache", evidence)

    def test_status_source_transcript_names_become_citation_records(self) -> None:
        payload = {
            "artifacts": {
                "source_tex": "papers/Fixture/source_tex/arxiv.tex",
                "journal_source_transcript": "sources/article.txt",
            }
        }
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/status.json", json.dumps(payload).encode("utf-8")
            )
        )
        self.assertEqual(projected["artifacts"]["source_tex"], "cited publication record")
        self.assertEqual(
            projected["artifacts"]["journal_source_transcript"],
            "cited publication record",
        )

    def test_transcript_locators_are_neutralized_outside_verbatim_source(self) -> None:
        payload = {
            "reason": (
                "Compare source.txt., sources/2101.05853.txt:12, and "
                "source_tex/main.tex:3."
            ),
            "source_evidence": "The proof uses audit/source_archive_surface.tex:20.",
            "source_anchor": {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": "The cited source itself says sources/2101.05853.txt.",
                "quoted_text_sha256": hashlib.sha256(
                    b"The cited source itself says sources/2101.05853.txt."
                ).hexdigest(),
            },
        }

        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_record_match_llm.json",
                json.dumps(payload).encode("utf-8"),
            )
        )

        self.assertNotIn("sources/2101.05853.txt", projected["reason"])
        self.assertNotIn("source.txt", projected["reason"])
        self.assertNotIn("source_tex/main.tex", projected["reason"])
        semantic_match = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_record_match_llm.json",
                json.dumps(
                    {"source_anchor": {"semantic_match": "See Fixture.txt:12."}}
                ).encode("utf-8"),
            )
        )
        self.assertNotIn("Fixture.txt", semantic_match["source_anchor"]["semantic_match"])
        self.assertEqual(
            projected["source_anchor"]["quoted_text"],
            payload["source_anchor"]["quoted_text"],
        )
        archive = projection.project_bytes(
            "papers/Fixture/audit/statement_match_llm.json",
            b'{"reason":"Checked source.tar member source.txt."}',
        ).decode("utf-8")
        self.assertNotIn("source.tar", archive)
        self.assertNotIn("source.txt", archive)
        archive_field = json.loads(
            projection.project_bytes(
                "papers/Fixture/status.json",
                b'{"artifacts":{"source_archive":"papers/Fixture/source.tar.gz"}}',
            )
        )
        self.assertEqual(
            archive_field["artifacts"]["source_archive"],
            "cited publication",
        )
        archive_object = json.loads(
            projection.project_bytes(
                "papers/Fixture/status.json",
                b'{"formalization_scope":{"base_archive":{"path":"source.tar.gz","sha256":"abc"}}}',
            )
        )
        self.assertEqual(
            archive_object["formalization_scope"]["base_archive"]["path"],
            "cited publication",
        )
        provenance = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_proof_fidelity.json",
                b'{"provenance":"A clarification of source.tar.gz."}',
            )
        )
        self.assertNotIn("source.tar", provenance["provenance"])
        self.assertIn("cited publication", provenance["provenance"])
        self.assertNotIn("audit/source_archive_surface.tex", projected["source_evidence"])
        self.assertIn(projection.PUBLICATION_LOCATOR, projected["reason"])

    def test_strict_private_anchor_schemas_become_public_display_records(self) -> None:
        quote = "The source uses the standard term at this exact location."
        anchor = {
            "path": "source.txt",
            "line_start": 7,
            "line_end": 7,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
        }
        payload = {
            "items": {
                "standard_term": {
                    "source_standard_term_interpretation": {
                        "source_term_use_anchor": anchor,
                        "standard_interpretation": "A public mathematical explanation.",
                    }
                },
                "partitioned_definition": {
                    "source_definition_partition": {
                        "components": [
                            {
                                "source_location": "source.txt:7",
                                "source_anchor_evidence": [anchor],
                            }
                        ]
                    }
                },
            }
        }
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )
        )
        standard = projected["items"]["standard_term"]
        self.assertNotIn("source_standard_term_interpretation", standard)
        public_standard = standard["publication_standard_term_interpretation"]
        self.assertNotIn("path", public_standard["source_term_use_anchor"])
        self.assertEqual(
            public_standard["source_term_use_anchor"]["publication_locator"],
            projection.PUBLICATION_LOCATOR,
        )
        definition = projected["items"]["partitioned_definition"]
        self.assertNotIn("source_definition_partition", definition)
        public_partition = definition["publication_source_definition_partition"]
        public_anchor = public_partition["components"][0]["source_anchor_evidence"][0]
        self.assertNotIn("path", public_anchor)
        self.assertEqual(public_anchor["publication_locator"], projection.PUBLICATION_LOCATOR)
        self.assertEqual(
            public_partition["components"][0]["source_location"],
            f"{projection.PUBLICATION_LOCATOR}:7",
        )

    def test_real_public_maps_preserve_strict_map_shape_by_renaming_private_audit_records(
        self,
    ) -> None:
        root = Path(__file__).resolve().parents[2]
        for paper in (
            "GCG24UserItemFairness",
            "LG21TestOptionalPolicies",
            "GHW01DigitalGoods",
        ):
            relative = f"papers/{paper}/audit/paper_statement_map.json"
            raw = (root / relative).read_bytes()
            payload = json.loads(raw)
            if projection.PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD in payload:
                # The public checkout contains the exported map. It must still
                # satisfy the same structural checks, while the exporter must
                # reject it as an unauthenticated private source for a new run.
                with self.assertRaises(projection.ProjectionError):
                    projection.project_bytes(relative, raw)
                projected = payload
            else:
                projected = json.loads(projection.project_bytes(relative, raw))
            self.assertFalse(
                any(
                    "source_standard_term_interpretation" in item
                    or "source_definition_partition" in item
                    for item in projected["items"].values()
                ),
                paper,
            )
            self.assertFalse(
                source_map_structural_errors(projected["items"]), paper
            )

    def test_approved_source_tex_and_contributor_workflow_are_byte_preserved(self) -> None:
        raw = b"% source excerpt: /tmp and .audit_source and private text extraction\n"
        self.assertEqual(
            projection.project_bytes("papers/Fixture/source/main.tex", raw), raw
        )
        for relative in projection.PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS:
            with self.subTest(relative=relative):
                self.assertEqual(projection.project_bytes(relative, raw), raw)

    def test_contributor_shell_example_is_preserved_without_approving_nearby_path(
        self,
    ) -> None:
        root = Path(__file__).resolve().parents[2]
        relative = "docs/contributing/README.md"
        raw = (root / relative).read_bytes()

        self.assertEqual(projection.project_bytes(relative, raw), raw)
        text = raw.decode("utf-8")
        self.assertIn('SOURCE_ARTIFACT=".scratch/$PAPER/source.pdf"', text)
        self.assertIn('STATEMENT_SPEC=".scratch/$PAPER/statement-spec.json"', text)
        self.assertIn('mkdir -p ".scratch/$PAPER"', text)

        with self.assertRaises(projection.ProjectionError):
            projection.project_bytes(
                "docs/contributing/PRIVATE_NOTES.md",
                b"private source cache at /tmp/unreviewed.txt\n",
            )

    def test_formalizer_skill_and_stage_references_are_byte_preserved(self) -> None:
        root = Path(__file__).resolve().parents[2]
        relative = "skills/econcs-formalizer/SKILL.md"
        raw = (root / relative).read_bytes()
        projected = projection.project_bytes(relative, raw)

        self.assertEqual(projected, raw)
        router = projected.decode("utf-8")
        self.assertIn("references/audit-and-closeout.md", router)
        self.assertIn("references/release-and-sync.md", router)
        self.assertIn("references/formalization-handbook.md", router)
        self.assertIn("references/public-private-sync.md", router)

        expected_stage_text = {
            "skills/econcs-formalizer/references/intake-and-source-surface.md": (
                "private source review"
            ),
            "skills/econcs-formalizer/references/audit-and-closeout.md": (
                "raw-source-to-expanded-Spec"
            ),
            "skills/econcs-formalizer/references/public-private-sync.md": (
                ".review_traces"
            ),
        }
        for stage_relative, marker in expected_stage_text.items():
            with self.subTest(stage=stage_relative):
                stage_raw = (root / stage_relative).read_bytes()
                self.assertIn(stage_relative, projection.PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS)
                self.assertEqual(
                    projection.project_bytes(stage_relative, stage_raw), stage_raw
                )
                self.assertIn(marker.lower(), stage_raw.decode("utf-8").lower())

    def test_readme_wiki_boundary_guidance_is_preserved_only_at_root(self) -> None:
        raw = (projection.PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE + "\n").encode()
        self.assertEqual(projection.project_bytes("README.md", raw), raw)
        self.assertNotEqual(projection.project_bytes("docs/reader.md", raw), raw)

    def test_source_presentation_metadata_projects_locators_without_changing_claims(self) -> None:
        digest = "a" * 64
        claim = "For every feasible allocation, welfare is at most 1."
        payload = {
            "source_artifact": {"path": "sources/arxiv_source/main.tex", "sha256": digest},
            "source_pdf_artifact": {
                "path": "papers/Fixture/sources/paper.pdf", "sha256": digest,
                "text_extraction": "source.txt produced with pdftotext",
            },
            "cited_source_artifacts": [{"path": "sources/related.txt", "sha256": digest}],
            "items": {"lemma": {
                "aliases": ["Footnote 10 (source.txt:527-532)"],
                "statement": claim,
                "semantic_source_anchor_evidence": [{"path": "source.txt", "sha256": digest, "line_start": 527, "line_end": 532}],
            }},
            "source_named_result_inventory_review": {"candidate_presentations": [
                {"presentation_label": "Lemma 1 (sources/paper.txt:20-30)"}
            ]},
        }
        result = json.loads(projection.project_bytes(
            "papers/Fixture/audit/paper_statement_map.json", json.dumps(payload).encode()
        ))
        self.assertEqual(result["items"]["lemma"]["statement"], claim)
        self.assertEqual(result["source_artifact"]["sha256"], digest)
        self.assertEqual(result["items"]["lemma"]["semantic_source_anchor_evidence"][0]["line_start"], 527)
        self.assertIn("Footnote 10", result["items"]["lemma"]["aliases"][0])
        self.assertNotIn("source.txt", json.dumps(result))
        self.assertNotIn("text_extraction", result["source_pdf_artifact"])
        status = json.loads(projection.project_bytes(
            "papers/Fixture/status.json",
            json.dumps({"artifacts": {"source_transcript": "sources/paper.tex", "paper_interface": "papers/Fixture/PaperInterface.lean"}}).encode(),
        ))
        self.assertEqual(status["artifacts"], {"paper_interface": "papers/Fixture/PaperInterface.lean"})


if __name__ == "__main__":
    unittest.main()
