from __future__ import annotations

import hashlib
import json
import unittest

from scripts.corrected_target_identity import (
    CORRECTED_TARGET_RECORD_SHA256_FIELD,
    CORRECTED_TARGET_REVIEW_SHA256_FIELD,
    corrected_target_record_digest,
    corrected_target_review_digest,
)
from scripts.obligation_evidence_projection import _source_role_contract
from scripts.public_release_projection import (
    PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD,
    project_bytes,
)
from scripts.source_display_projection import (
    PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD,
    PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR,
    PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST,
    PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
)
from scripts import public_source_role_projection as projection


def _sha256(value: str | bytes) -> str:
    raw = value.encode("utf-8") if isinstance(value, str) else value
    return hashlib.sha256(raw).hexdigest()


def _corrected_target() -> dict[str, object]:
    statement = "Every feasible allocation has welfare at most the displayed benchmark."
    excerpt = (
        "Private approval record expressly approves this corrected mathematical target "
        "for the bounded formalization and contains local material that stays private."
    )
    approval = {
        "artifact_path": "docs/PRIVATE_APPROVAL_MEMO.md",
        "artifact_protocol": "unique_normalized_artifact_excerpt_v1",
        "artifact_excerpt": excerpt,
        "artifact_excerpt_sha256": _sha256(excerpt),
        "kind": "recorded_user_direction",
        "recorded_at": "2026-09-07",
        "reference": "/home/reviewer/private approval notes",
        "target_statement_sha256": _sha256(statement),
    }
    target: dict[str, object] = {
        "schema": 1,
        "statement": statement,
        "archival_equivalence_claimed": False,
        "archival_source_locator": "Fixture.txt:1-2",
        "archival_source_quote_sha256": "a" * 64,
        "governing_defect_ids": ["D1"],
        "approval": approval,
    }
    target[CORRECTED_TARGET_RECORD_SHA256_FIELD] = corrected_target_record_digest(target)
    target[CORRECTED_TARGET_REVIEW_SHA256_FIELD] = corrected_target_review_digest(target)
    return target


class PublicSourceRoleProjectionTests(unittest.TestCase):
    paper = "Fixture"
    graph_sha256 = "9" * 64

    def setUp(self) -> None:
        quote = "Theorem 1. Every fixture satisfies the displayed claim."
        self.private_map = {
            "schema": 1,
            "paper": self.paper,
            "source_artifact_path": ".audit_source/Fixture.txt",
            "source_artifact_sha256": "b" * 64,
            "items": {
                "scope_item": {
                    "source_kind": "theorem",
                    "coverage_status": "user_approved_scope_exclusion",
                    "scope_disposition": "user_approved_scope_exclusion",
                    "source_anchor_evidence": [
                        {
                            "path": ".audit_source/Fixture.txt",
                            "line_start": 1,
                            "line_end": 1,
                            "quoted_text": quote,
                            "quoted_text_sha256": _sha256(quote),
                        }
                    ],
                    "user_approved_scope_exclusion": {
                        "schema": 1,
                        "approval_kind": "explicit_user_instruction",
                        "approval_reference": (
                            "User direction recorded privately for this exact boundary."
                        ),
                        "approved_at": "2026-09-07",
                        "reason": "The exact source result remains outside this bounded closeout.",
                        "source_locator": ".audit_source/Fixture.txt:1",
                        "source_evidence": (
                            "The cited result at Fixture.txt:1 is visible and remains uncredited."
                        ),
                        "source_anchor_quote_sha256": _sha256(quote),
                    },
                },
                "corrected_item": {
                    "source_kind": "theorem",
                    "coverage_status": "formalized",
                    "corrected_target": _corrected_target(),
                },
            },
        }
        self.private_bytes = self._bytes(self.private_map)
        self.public_bytes = project_bytes(
            f"papers/{self.paper}/audit/paper_statement_map.json",
            self.private_bytes,
            include_source_display_marker=True,
        )
        self.public_map = json.loads(self.public_bytes)
        self.display = {
            "schema": 1,
            "generator": "python3 scripts/public_source_display_projection.py",
            "paper_id": self.paper,
            "private_source_map_sha256": _sha256(self.private_bytes),
            "public_source_map_sha256": _sha256(self.public_bytes),
            "public_manifest_path": (
                f"papers/{self.paper}/audit/public_source_display_projection.json"
            ),
            "raw_source_artifact_included": False,
        }
        self.display_bytes = self._bytes(self.display)
        self.accepted_roles = {
            item_id: _source_role_contract(item)
            for item_id, item in self.private_map["items"].items()
        }

    def test_wire_constants_match_lightweight_display_and_release_owners(self) -> None:
        self.assertEqual(
            projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD,
            PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD,
        )
        self.assertEqual(
            projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
            PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
        )
        self.assertEqual(
            projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST,
            PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST,
        )
        self.assertEqual(
            projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR,
            PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR,
        )
        self.assertEqual(
            projection.PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD,
            PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD,
        )

    @staticmethod
    def _bytes(value: object) -> bytes:
        return (
            json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8")

    def _build(self) -> dict[str, object]:
        return projection.build_public_source_role_projection_envelope(
            paper=self.paper,
            private_source_map_bytes=self.private_bytes,
            public_source_map_bytes=self.public_bytes,
            public_display_manifest_bytes=self.display_bytes,
            accepted_graph_sha256=self.graph_sha256,
            accepted_role_sha256s_by_source_item=self.accepted_roles,
        )

    def _runtime(
        self,
        envelope: dict[str, object],
        *,
        public_bytes: bytes | None = None,
        display_bytes: bytes | None = None,
    ) -> dict[str, str]:
        return projection.validate_runtime_public_source_role_projection(
            trusted_envelope_bytes=(
                projection.canonical_public_source_role_projection_bytes(envelope)
            ),
            paper=self.paper,
            public_source_map_bytes=public_bytes or self.public_bytes,
            public_display_manifest_bytes=display_bytes or self.display_bytes,
            accepted_graph_sha256=self.graph_sha256,
            accepted_role_sha256s_by_source_item=self.accepted_roles,
        )

    def _changed_public_material(self, mutate) -> tuple[bytes, bytes]:
        public_map = json.loads(self.public_bytes)
        mutate(public_map)
        public_bytes = self._bytes(public_map)
        display = dict(self.display)
        display["public_source_map_sha256"] = _sha256(public_bytes)
        return public_bytes, self._bytes(display)

    def test_guard_builds_one_bridge_for_scope_and_corrected_target(self) -> None:
        envelope = self._build()
        bindings = envelope["bindings_by_source_item"]
        self.assertEqual(
            bindings["scope_item"]["withheld_field_paths"],
            [
                "user_approved_scope_exclusion.approval_reference",
                "user_approved_scope_exclusion.source_evidence",
                "user_approved_scope_exclusion.source_locator",
            ],
        )
        self.assertEqual(
            bindings["corrected_item"]["withheld_field_paths"],
            [
                "corrected_target.approval",
                "corrected_target.archival_source_locator",
            ],
        )
        self.assertNotEqual(
            bindings["scope_item"]["accepted_source_role_contract_sha256"],
            bindings["scope_item"]["public_source_role_projection_sha256"],
        )
        self.assertEqual(set(self._runtime(envelope)), set(self.accepted_roles))

    def test_private_role_must_match_exact_accepted_graph_atom_role(self) -> None:
        wrong = dict(self.accepted_roles, scope_item="0" * 64)
        with self.assertRaisesRegex(
            projection.PublicSourceRoleProjectionError, "accepted role digest"
        ):
            projection.build_public_source_role_projection_envelope(
                paper=self.paper,
                private_source_map_bytes=self.private_bytes,
                public_source_map_bytes=self.public_bytes,
                public_display_manifest_bytes=self.display_bytes,
                accepted_graph_sha256=self.graph_sha256,
                accepted_role_sha256s_by_source_item=wrong,
            )

    def test_marker_is_mandatory(self) -> None:
        unmarked = project_bytes(
            f"papers/{self.paper}/audit/paper_statement_map.json",
            self.private_bytes,
        )
        display = dict(self.display, public_source_map_sha256=_sha256(unmarked))
        with self.assertRaisesRegex(
            projection.PublicSourceRoleProjectionError, "marker-bearing"
        ):
            projection.build_public_source_role_projection_envelope(
                paper=self.paper,
                private_source_map_bytes=self.private_bytes,
                public_source_map_bytes=unmarked,
                public_display_manifest_bytes=self._bytes(display),
                accepted_graph_sha256=self.graph_sha256,
                accepted_role_sha256s_by_source_item=self.accepted_roles,
            )

    def test_mismatched_display_manifest_is_rejected(self) -> None:
        changed = dict(self.display, public_source_map_sha256="0" * 64)
        with self.assertRaisesRegex(
            projection.PublicSourceRoleProjectionError,
            "display manifest public_source_map_sha256",
        ):
            projection.build_public_source_role_projection_envelope(
                paper=self.paper,
                private_source_map_bytes=self.private_bytes,
                public_source_map_bytes=self.public_bytes,
                public_display_manifest_bytes=self._bytes(changed),
                accepted_graph_sha256=self.graph_sha256,
                accepted_role_sha256s_by_source_item=self.accepted_roles,
            )

    def test_trusted_envelope_rejects_reason_status_and_anchor_edits(self) -> None:
        envelope = self._build()
        mutations = (
            lambda value: value["items"]["scope_item"][
                "user_approved_scope_exclusion"
            ].__setitem__("reason", "Edited public reason."),
            lambda value: value["items"]["scope_item"].__setitem__(
                "coverage_status", "formalized"
            ),
            lambda value: value["items"]["scope_item"]["source_anchor_evidence"][
                0
            ].__setitem__("quoted_text", "Invented anchor."),
        )
        for mutate in mutations:
            with self.subTest(mutate=mutate):
                public_bytes, display_bytes = self._changed_public_material(mutate)
                with self.assertRaisesRegex(
                    projection.PublicSourceRoleProjectionError,
                    "trusted source-role envelope public_source_map",
                ):
                    self._runtime(
                        envelope,
                        public_bytes=public_bytes,
                        display_bytes=display_bytes,
                    )

    def test_trusted_envelope_rejects_corrected_target_edit(self) -> None:
        envelope = self._build()
        public_bytes, display_bytes = self._changed_public_material(
            lambda value: value["items"]["corrected_item"]["corrected_target"].__setitem__(
                "statement", "A branch-only corrected target."
            )
        )
        with self.assertRaises(projection.PublicSourceRoleProjectionError):
            self._runtime(
                envelope,
                public_bytes=public_bytes,
                display_bytes=display_bytes,
            )

    def test_tampered_envelope_cannot_rebind_an_accepted_role(self) -> None:
        envelope = self._build()
        envelope["bindings_by_source_item"]["scope_item"][
            "accepted_source_role_contract_sha256"
        ] = "0" * 64
        with self.assertRaisesRegex(
            projection.PublicSourceRoleProjectionError, "stale or malformed"
        ):
            self._runtime(envelope)

    def test_branch_only_envelope_is_not_a_substitute_for_trusted_bytes(self) -> None:
        trusted = self._build()
        branch = json.loads(json.dumps(trusted))
        branch["bindings_by_source_item"]["scope_item"][
            "public_source_role_projection_sha256"
        ] = "0" * 64
        # Runtime succeeds with canonical bytes and rejects the branch-only
        # bytes. Canonical-remote/ref selection belongs to the caller.
        self._runtime(trusted)
        with self.assertRaises(projection.PublicSourceRoleProjectionError):
            self._runtime(branch)

    def test_wrong_graph_and_incomplete_route_set_fail_closed(self) -> None:
        envelope = self._build()
        with self.assertRaisesRegex(
            projection.PublicSourceRoleProjectionError, "authority or paper identity"
        ):
            projection.validate_runtime_public_source_role_projection(
                trusted_envelope_bytes=(
                    projection.canonical_public_source_role_projection_bytes(envelope)
                ),
                paper=self.paper,
                public_source_map_bytes=self.public_bytes,
                public_display_manifest_bytes=self.display_bytes,
                accepted_graph_sha256="8" * 64,
                accepted_role_sha256s_by_source_item=self.accepted_roles,
            )
        incomplete = {"scope_item": self.accepted_roles["scope_item"]}
        with self.assertRaisesRegex(
            projection.PublicSourceRoleProjectionError, "exact accepted source routes"
        ):
            projection.validate_runtime_public_source_role_projection(
                trusted_envelope_bytes=(
                    projection.canonical_public_source_role_projection_bytes(envelope)
                ),
                paper=self.paper,
                public_source_map_bytes=self.public_bytes,
                public_display_manifest_bytes=self.display_bytes,
                accepted_graph_sha256=self.graph_sha256,
                accepted_role_sha256s_by_source_item=incomplete,
            )


if __name__ == "__main__":
    unittest.main()
