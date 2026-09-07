#!/usr/bin/env python3
"""Focused regression tests for content-pinned statement receipt reissue."""

from __future__ import annotations

import base64
import copy
import hashlib
import io
import json
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from typing import Mapping
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    text = str(import_root)
    if text not in sys.path:
        sys.path.insert(0, text)

import review_dashboard  # noqa: E402
import statement_receipt_reissue as REISSUE  # noqa: E402
import historical_statement_manifest_replay as HISTORICAL_REPLAY  # noqa: E402
import audit_evidence_integrity as EVIDENCE_INTEGRITY  # noqa: E402
import historical_manifest_store_recovery as STORE_RECOVERY  # noqa: E402
from scripts import statement_receipt_reissue as PACKAGE_REISSUE  # noqa: E402
from scripts.tests import test_historical_statement_manifest_replay as HISTORICAL_FIXTURE  # noqa: E402
from scripts.tests.test_statement_obligation_ledger import (  # noqa: E402
    refresh_manifest_digest,
    valid_ledger,
    valid_manifest,
)


PAPER = "FixturePaper"
SOURCE_STATEMENT = "P x"
TRANSLATION = "P x"
LEAN_TEXT = "theorem fixture : P x"
FIXTURE_SOURCE_RECORD_AUDIT = {"fixture": "current source-record authority"}
FIXTURE_SOURCE_RECORD_AUDIT_BYTES = REISSUE._json_bytes(FIXTURE_SOURCE_RECORD_AUDIT)
FIXTURE_CLOSURE = {"fixture": "current Lean import closure"}
FIXTURE_CLOSURE_BYTES = REISSUE._json_bytes(FIXTURE_CLOSURE)
FIXTURE_CLOSURE_SHA256 = str(
    HISTORICAL_FIXTURE.recipe()["current_execution_inputs"][
        "lean_import_closure_sha256"
    ]
)


def fixture_source_record_authority(
    _surface: REISSUE.CurrentReceiptSurface,
    raw_audit: Mapping[str, object],
) -> tuple[dict[str, object], bytes, str]:
    """Test seam for materializer-only transport tests.

    Production uses the source-record raw receipt validator.  These narrow
    reissue tests exercise the pinned transport independently of the much
    larger source-record generator fixture.
    """

    if dict(raw_audit) != FIXTURE_SOURCE_RECORD_AUDIT:
        raise REISSUE.StatementReceiptReissueError("fixture source-record audit changed")
    return dict(FIXTURE_CLOSURE), FIXTURE_CLOSURE_BYTES, FIXTURE_CLOSURE_SHA256


def make_target(
    *,
    paper_statement: str = SOURCE_STATEMENT,
    translation: str = TRANSLATION,
    lean_text: str = LEAN_TEXT,
) -> REISSUE.CurrentReceiptTarget:
    manifest = valid_manifest()
    return REISSUE.CurrentReceiptTarget(
        lean_signature_sha256=str(manifest["sha256"]),
        paper_statement_sha256=review_dashboard.statement_digest(paper_statement),
        tex_statement_sha256=review_dashboard.statement_digest(translation),
        lean_statement_sha256=review_dashboard.statement_digest(lean_text),
        manifest=manifest,
    )


def make_surface(
    *targets: REISSUE.CurrentReceiptTarget,
    source_kind: str = "theorem",
    source_key: str = "source_result",
    source_statement: str = SOURCE_STATEMENT,
) -> REISSUE.CurrentReceiptSurface:
    inventory = {
        source_key: {
            "statement": source_statement,
            "statement_sha256": review_dashboard.statement_digest(source_statement),
            "source_location": "source.txt:1-1",
            "source_kind": source_kind,
            "spec_lean_declarations": ["Fixture.SourceSpec"],
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": source_statement,
                    "quoted_text_sha256": hashlib.sha256(
                        source_statement.encode("utf-8")
                    ).hexdigest(),
                }
            ],
        }
    }
    return REISSUE.CurrentReceiptSurface(
        paper=PAPER,
        cache_sha256="a" * 64,
        source_map_sha256="b" * 64,
        source_map_semantic_sha256="d" * 64,
        source_route_inventory_sha256="c" * 64,
        current_surface_sha256=REISSUE._surface_digest(targets),
        targets=list(targets),
        source_route_inventory=inventory,
    )


def fresh_body(
    *,
    source_key: str = "source_result",
    route_kind: str = "direct",
    relation: str | None = None,
    source_statement: str = SOURCE_STATEMENT,
) -> dict[str, object]:
    body = copy.deepcopy(valid_ledger())
    source_item = {
        "statement": source_statement,
        "statement_sha256": review_dashboard.statement_digest(source_statement),
        "source_location": "source.txt:1-1",
        "source_kind": "theorem",
        "spec_lean_declarations": ["Fixture.SourceSpec"],
        "source_anchor_evidence": [
            {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": source_statement,
                "quoted_text_sha256": hashlib.sha256(
                    source_statement.encode("utf-8")
                ).hexdigest(),
            }
        ],
    }
    anchor_identity, anchor_error = review_dashboard.source_anchor_quote_identity(
        source_item
    )
    assert anchor_error == ""
    _source_text, source_input_identity, source_input_error = (
        review_dashboard.source_semantic_input_bundle(
            source_item, require_context_roles=True
        )
    )
    assert source_input_error == ""
    body.update(
        {
            "source_input_protocol": "verbatim_source_anchor_bundle_v1",
            "source_input_bundle_sha256": source_input_identity,
            "lean_target_protocol": "expanded_paperinterface_spec_v1",
            "semantic_target_declaration": "Fixture.SourceSpec",
        }
    )
    conclusion = body["source_obligations"][1]
    assert isinstance(conclusion, dict)
    conclusion.update(
        {
            "source_item": source_key,
            "source_statement_sha256": review_dashboard.statement_digest(source_statement),
            "source_location": "source.txt:1-1",
            "statement": source_statement,
            "source_anchor_quote_identity_sha256": anchor_identity,
            "source_input_bundle_sha256": source_input_identity,
        }
    )
    route: dict[str, object] = {
        "source_item": source_key,
        "source_statement_sha256": review_dashboard.statement_digest(source_statement),
        "source_location": "source.txt:1-1",
        "source_anchor_quote_identity_sha256": anchor_identity,
        "route_kind": route_kind,
    }
    if relation is not None:
        route.update(
            {
                "semantic_relation": relation,
                "source_support_scope": (
                    "This is source model context only and does not stand in for the "
                    "reviewed result endpoint, although it describes the shared scalar domain."
                ),
                "lean_evidence_ids": ["l_conclusion"],
            }
        )
    body["source_routes"] = [route]
    return body


def generated_entry(
    target: REISSUE.CurrentReceiptTarget,
    *,
    body: dict[str, object] | None = None,
) -> dict[str, object]:
    entry = copy.deepcopy(body or fresh_body())
    entry.update(
        {
            "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
            "validator": "fixture reviewer",
            "validator_type": "agent",
            "validated_at": "2026-08-13T00:00:00Z",
            "lean_statement_sha256": target.lean_statement_sha256,
            **target.identity,
        }
    )
    return entry


def prior_sidecar(*entries: dict[str, object]) -> REISSUE.PriorSidecar:
    payload = {
        "schema": 1,
        "paper": PAPER,
        "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
        "validator": "fixture reviewer",
        "validator_type": "agent",
        "validated_at": "2026-08-13T00:00:00Z",
        "items": {f"navigation_{index}": value for index, value in enumerate(entries)},
    }
    raw = (json.dumps(payload, indent=1, sort_keys=False) + "\n").encode("utf-8")
    with tempfile.TemporaryDirectory() as temporary:
        path = Path(temporary) / "statement_match_llm.json"
        path.write_bytes(raw)
        return REISSUE.load_prior_sidecar(path)


def base_plan(
    surface: REISSUE.CurrentReceiptSurface,
    prior: REISSUE.PriorSidecar,
    actions: list[dict[str, object]],
) -> dict[str, object]:
    return {
        "schema": REISSUE.REISSUE_SCHEMA,
        "artifact_kind": REISSUE.PLAN_KIND,
        "policy_version": REISSUE.POLICY_VERSION,
        "paper": PAPER,
        "current_inputs": surface.input_pins(),
        "prior_sidecar": prior.descriptor(),
        "reviewer": "fresh fixture reviewer",
        "validator_type": "llm_semantic_statement_review",
        "validated_at": "2026-08-13T00:00:00Z",
        "comment": "Each current target was independently reviewed against the current source and Lean facts.",
        "actions": actions,
    }


def historical_replay_fixture() -> tuple[
    REISSUE.CurrentReceiptSurface,
    REISSUE.PriorSidecar,
    REISSUE.CurrentReceiptTarget,
    dict[str, object],
    bytes,
    dict[str, object],
    bytes,
    dict[str, object],
    bytes,
]:
    """Build one name-free historic/current manifest transport fixture."""

    current_manifest = HISTORICAL_FIXTURE.current_manifest()
    target = REISSUE.CurrentReceiptTarget(
        lean_signature_sha256=str(current_manifest["sha256"]),
        paper_statement_sha256=review_dashboard.statement_digest(SOURCE_STATEMENT),
        tex_statement_sha256=review_dashboard.statement_digest(TRANSLATION),
        lean_statement_sha256=review_dashboard.statement_digest("theorem current : P x"),
        manifest=current_manifest,
    )
    surface = make_surface(target)
    historical_manifest = HISTORICAL_FIXTURE.historic_manifest()
    archived_entry = valid_ledger()
    refresh_manifest_digest(archived_entry, historical_manifest)
    routed_body = fresh_body()
    archived_entry.update(
        {
            "paper_statement_sha256": target.paper_statement_sha256,
            "tex_statement_sha256": target.tex_statement_sha256,
            "lean_statement_sha256": review_dashboard.statement_digest(
                "theorem historical : P x"
            ),
            "source_obligations": routed_body["source_obligations"],
            "source_routes": routed_body["source_routes"],
        }
    )
    prior = prior_sidecar(archived_entry)
    (
        historical_manifest_carrier,
        historical_manifest_carrier_bytes,
        historical_manifest_authority,
        historical_manifest_authority_bytes,
    ) = HISTORICAL_FIXTURE.historical_semantic_store(historical_manifest)
    bridge_targets = REISSUE.historical_manifest_replay_current_targets(surface)
    bridge, error = HISTORICAL_REPLAY.build_historical_statement_manifest_replay(
        paper=PAPER,
        historical_serializer_recipe=HISTORICAL_FIXTURE.recipe(),
        prior_sidecar=prior.payload,
        prior_sidecar_bytes=prior.raw_bytes,
        historical_manifest_carrier=historical_manifest_carrier,
        historical_manifest_carrier_bytes=historical_manifest_carrier_bytes,
        historical_manifest_authority=historical_manifest_authority,
        historical_manifest_authority_bytes=historical_manifest_authority_bytes,
        current_targets=bridge_targets,
        current_evidence_sha256=(
            REISSUE.historical_manifest_replay_current_evidence_sha256(surface)
        ),
        historical_manifest_runner=HISTORICAL_FIXTURE.historic_runner(
            {str(current_manifest["sha256"]): historical_manifest}
        ),
        historical_blob_verifier=HISTORICAL_FIXTURE.blob_verifier,
        current_target_validator=(
            lambda raw: REISSUE._historical_manifest_replay_target_validator(
                surface, raw
            )
        ),
        source_route_validator=(
            lambda raw: REISSUE._historical_manifest_replay_source_route_validator(
                surface, raw
            )
        ),
    )
    assert error == "", error
    assert bridge is not None
    bridge_bytes = REISSUE._json_bytes(bridge)
    return (
        surface,
        prior,
        target,
        bridge,
        bridge_bytes,
        historical_manifest_carrier,
        historical_manifest_carrier_bytes,
        historical_manifest_authority,
        historical_manifest_authority_bytes,
    )


def historical_replay_plan(
    surface: REISSUE.CurrentReceiptSurface,
    prior: REISSUE.PriorSidecar,
    target: REISSUE.CurrentReceiptTarget,
    bridge: dict[str, object],
    bridge_bytes: bytes,
    historical_manifest_carrier_bytes: bytes,
    historical_manifest_authority_bytes: bytes,
) -> dict[str, object]:
    """Return a completed plan whose bridge reference is byte-pinned."""

    bridge_sha = str(
        bridge[
            HISTORICAL_REPLAY.HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD
        ]
    )
    prior_payload_sha = next(iter(prior.groups))
    plan = base_plan(
        surface,
        prior,
        [
            {
                "action": REISSUE.HISTORICAL_REPLAY_ACTION,
                "target": target.descriptor(),
                "prior_entry_payload_sha256": prior_payload_sha,
                "historical_manifest_replay_sha256": bridge_sha,
            }
        ],
    )
    plan[REISSUE.HISTORICAL_REPLAY_PLAN_FIELD] = {
        "artifact_path": "audit/historical_statement_manifest_replay.json",
        "artifact_bytes_sha256": REISSUE._bytes_sha256(bridge_bytes),
        "replay_receipt_sha256": bridge_sha,
        "historical_manifest_carrier_path": "audit/historical_manifest_carrier.json",
        "historical_manifest_carrier_bytes_sha256": REISSUE._bytes_sha256(
            historical_manifest_carrier_bytes
        ),
        "historical_manifest_authority_path": "audit/historical_manifest_authority.json",
        "historical_manifest_authority_bytes_sha256": REISSUE._bytes_sha256(
            historical_manifest_authority_bytes
        ),
        "current_source_record_audit_path": "audit/current_source_record_audit.json",
        "current_source_record_audit_bytes_sha256": REISSUE._bytes_sha256(
            FIXTURE_SOURCE_RECORD_AUDIT_BYTES
        ),
        "prior_sidecar_archive_path": "audit/prior.json",
    }
    return plan


def verified_historical_recipe(recipe: Mapping[str, object]) -> str:
    """Fixture stand-in for production runner.verify_recipe."""

    return (
        ""
        if dict(recipe) == HISTORICAL_FIXTURE.recipe()
        else "historical Git/blob/current-file recipe pins are not verified"
    )


def historical_replay_materialization_kwargs(
    *,
    bridge: Mapping[str, object],
    bridge_bytes: bytes,
    carrier: Mapping[str, object],
    carrier_bytes: bytes,
    authority: Mapping[str, object],
    authority_bytes: bytes,
) -> dict[str, object]:
    """Exact retrieval inputs used by the historic-replay materializer."""

    return {
        "historical_manifest_replay_receipt": bridge,
        "historical_manifest_replay_bytes": bridge_bytes,
        "historical_manifest_replay_path": "audit/historical_statement_manifest_replay.json",
        "historical_manifest_carrier": carrier,
        "historical_manifest_carrier_bytes": carrier_bytes,
        "historical_manifest_carrier_path": "audit/historical_manifest_carrier.json",
        "historical_manifest_authority": authority,
        "historical_manifest_authority_bytes": authority_bytes,
        "historical_manifest_authority_path": "audit/historical_manifest_authority.json",
        "historical_manifest_current_source_record_audit": (
            FIXTURE_SOURCE_RECORD_AUDIT
        ),
        "historical_manifest_current_source_record_audit_bytes": (
            FIXTURE_SOURCE_RECORD_AUDIT_BYTES
        ),
        "historical_manifest_current_source_record_audit_path": (
            "audit/current_source_record_audit.json"
        ),
        "historical_manifest_current_source_record_authority_verifier": (
            fixture_source_record_authority
        ),
        "historical_manifest_replay_archive_path": "audit/prior.json",
    }


def recovered_manifest_store_bundle(
    *,
    carrier: Mapping[str, object],
    carrier_bytes: bytes,
    authority: Mapping[str, object],
    authority_bytes: bytes,
) -> dict[str, object]:
    """Make a compact, self-attesting gzip bundle around the replay fixture."""

    receipt_path = "audit/recovered_manifest_store.receipt.json"
    authority_path = "audit/recovered_manifest_store.authority.json"
    carrier_path = "audit/recovered_manifest_store.carrier.json.gz"
    compressed_carrier = STORE_RECOVERY.deterministic_gzip_compress(carrier_bytes)
    receipt: dict[str, object] = {
        "schema": STORE_RECOVERY.HISTORICAL_MANIFEST_STORE_RECOVERY_SCHEMA,
        "artifact_kind": STORE_RECOVERY.HISTORICAL_MANIFEST_STORE_RECOVERY_ARTIFACT_KIND,
        "policy_version": STORE_RECOVERY.HISTORICAL_MANIFEST_STORE_RECOVERY_POLICY_VERSION,
        "paper": PAPER,
        "recovered_store": {
            "authority": {
                "paper_relative_path": authority_path,
                "bytes_sha256": REISSUE._bytes_sha256(authority_bytes),
                "byte_length": len(authority_bytes),
                "canonical_payload_sha256": STORE_RECOVERY.manifest_store.canonical_json_sha256(
                    authority
                ),
                "schema": authority.get("schema"),
                "entries_sha256": authority.get("entries_sha256"),
                "contexts_sha256": authority.get("contexts_sha256"),
            },
            "carrier": {
                "paper_relative_path": carrier_path,
                "encoding": "gzip",
                "compression_policy": STORE_RECOVERY.DETERMINISTIC_GZIP_POLICY_VERSION,
                "compressed_bytes_sha256": REISSUE._bytes_sha256(
                    compressed_carrier
                ),
                "compressed_byte_length": len(compressed_carrier),
                "uncompressed_bytes_sha256": REISSUE._bytes_sha256(carrier_bytes),
                "uncompressed_byte_length": len(carrier_bytes),
                "uncompressed_canonical_payload_sha256": (
                    STORE_RECOVERY.manifest_store.canonical_json_sha256(carrier)
                ),
                "schema": carrier.get("schema"),
            },
            "receipt_paper_relative_path": receipt_path,
        },
    }
    receipt[STORE_RECOVERY.HISTORICAL_MANIFEST_STORE_RECOVERY_INTEGRITY_FIELD] = (
        STORE_RECOVERY.historical_manifest_store_recovery_digest(receipt)
    )
    receipt_bytes = REISSUE._json_bytes(receipt)
    return {
        "receipt": receipt,
        "receipt_bytes": receipt_bytes,
        "receipt_path": receipt_path,
        "authority": dict(authority),
        "authority_bytes": authority_bytes,
        "authority_path": authority_path,
        "carrier_compressed_bytes": compressed_carrier,
        "carrier_compressed_path": carrier_path,
    }


def recovered_historical_replay_plan(
    legacy_plan: Mapping[str, object],
    bundle: Mapping[str, object],
) -> dict[str, object]:
    """Replace only the legacy store input pins with recovered-store pins."""

    plan = copy.deepcopy(dict(legacy_plan))
    descriptor = plan[REISSUE.HISTORICAL_REPLAY_PLAN_FIELD]
    assert isinstance(descriptor, dict)
    for key in (
        "historical_manifest_carrier_path",
        "historical_manifest_carrier_bytes_sha256",
        "historical_manifest_authority_path",
        "historical_manifest_authority_bytes_sha256",
    ):
        descriptor.pop(key)
    descriptor[REISSUE.HISTORICAL_REPLAY_RECOVERED_STORE_FIELD] = {
        "recovery_receipt_path": bundle["receipt_path"],
        "recovery_receipt_bytes_sha256": REISSUE._bytes_sha256(
            bundle["receipt_bytes"]  # type: ignore[arg-type]
        ),
        "authority_path": bundle["authority_path"],
        "authority_bytes_sha256": REISSUE._bytes_sha256(
            bundle["authority_bytes"]  # type: ignore[arg-type]
        ),
        "carrier_compressed_path": bundle["carrier_compressed_path"],
        "carrier_compressed_bytes_sha256": REISSUE._bytes_sha256(
            bundle["carrier_compressed_bytes"]  # type: ignore[arg-type]
        ),
    }
    return plan


def recovered_historical_replay_materialization_kwargs(
    *,
    bridge: Mapping[str, object],
    bridge_bytes: bytes,
    bundle: Mapping[str, object],
) -> dict[str, object]:
    """Return the replay and raw recovered-store artifacts, never a raw carrier."""

    return {
        "historical_manifest_replay_receipt": bridge,
        "historical_manifest_replay_bytes": bridge_bytes,
        "historical_manifest_replay_path": "audit/historical_statement_manifest_replay.json",
        "historical_manifest_store_recovery_receipt": bundle["receipt"],
        "historical_manifest_store_recovery_receipt_bytes": bundle["receipt_bytes"],
        "historical_manifest_store_recovery_receipt_path": bundle["receipt_path"],
        "historical_manifest_store_recovery_authority": bundle["authority"],
        "historical_manifest_store_recovery_authority_bytes": bundle[
            "authority_bytes"
        ],
        "historical_manifest_store_recovery_authority_path": bundle[
            "authority_path"
        ],
        "historical_manifest_store_recovery_carrier_compressed_bytes": bundle[
            "carrier_compressed_bytes"
        ],
        "historical_manifest_store_recovery_carrier_compressed_path": bundle[
            "carrier_compressed_path"
        ],
        "historical_manifest_current_source_record_audit": (
            FIXTURE_SOURCE_RECORD_AUDIT
        ),
        "historical_manifest_current_source_record_audit_bytes": (
            FIXTURE_SOURCE_RECORD_AUDIT_BYTES
        ),
        "historical_manifest_current_source_record_audit_path": (
            "audit/current_source_record_audit.json"
        ),
        "historical_manifest_current_source_record_authority_verifier": (
            fixture_source_record_authority
        ),
        "historical_manifest_replay_archive_path": "audit/prior.json",
    }


class StatementReceiptReissueTests(unittest.TestCase):
    def test_statement_receipt_surface_excludes_assumption_rows(self) -> None:
        claim = SimpleNamespace(is_assumption=False)
        assumption = SimpleNamespace(is_assumption=True)

        self.assertEqual(
            REISSUE.statement_receipt_review_rows([claim, assumption]), [claim]
        )

    def test_template_is_non_evidence_and_content_addressed(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar(generated_entry(target))

        template = REISSUE.statement_receipt_reissue_template(surface, prior)

        self.assertEqual(template["artifact_kind"], REISSUE.TEMPLATE_KIND)
        self.assertTrue(template["non_evidence_scaffold"])
        self.assertTrue(template["must_not_be_written_to_repository_sidecar"])
        self.assertEqual(template["actions"], [])
        current_targets = template["current_targets"]
        self.assertEqual(len(current_targets), 1)
        self.assertNotIn("name", current_targets[0])
        self.assertNotIn("declaration", current_targets[0])
        self.assertEqual(
            current_targets[0]["semantic_target_sha256"], target.semantic_target_sha256
        )

    def test_action_scaffold_reuses_only_exact_current_evidence(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar(generated_entry(target))
        prior_digest = next(iter(prior.groups))

        scaffold = REISSUE.statement_receipt_reissue_action_scaffold(surface, prior)

        self.assertEqual(scaffold["artifact_kind"], REISSUE.ACTION_SCAFFOLD_KIND)
        self.assertTrue(scaffold["non_evidence_scaffold"])
        self.assertTrue(scaffold["must_not_be_written_to_repository_sidecar"])
        self.assertEqual(scaffold["unresolved_semantic_classes"], [])
        self.assertEqual(len(scaffold["candidate_actions"]), 1)
        action = scaffold["candidate_actions"][0]
        self.assertEqual(action["action"], "reuse")
        self.assertEqual(action["classification"], "exact_valid_identity_match")
        self.assertEqual(action["target"], target.descriptor())
        self.assertEqual(action["prior_entry_payload_sha256"], prior_digest)
        self.assertTrue(action["candidate_only"])
        self.assertNotIn("navigation_0", REISSUE._json_bytes(scaffold).decode("utf-8"))
        self.assertNotIn("source_result", REISSUE._json_bytes(scaffold).decode("utf-8"))

        # A scaffold has the wrong artifact kind and remains non-evidence even
        # though this particular candidate is exact-current.
        with self.assertRaisesRegex(REISSUE.StatementReceiptReissueError, "artifact_kind"):
            REISSUE.materialize_statement_receipt_reissue(surface, prior, scaffold)

    def test_action_scaffold_ties_stale_source_route_to_fresh_supersession(self) -> None:
        target = make_target()
        old_entry = generated_entry(target, body=fresh_body(source_key="old_source"))
        prior = prior_sidecar(old_entry)
        prior_digest = next(iter(prior.groups))
        surface = make_surface(target, source_key="new_source")

        scaffold = REISSUE.statement_receipt_reissue_action_scaffold(surface, prior)

        self.assertEqual(scaffold["unresolved_semantic_classes"], [])
        self.assertEqual(len(scaffold["candidate_actions"]), 1)
        action = scaffold["candidate_actions"][0]
        self.assertEqual(action["action"], "fresh")
        self.assertEqual(
            action["classification"], "same_semantic_class_stale_source_identity"
        )
        self.assertEqual(action["target"], target.descriptor())
        self.assertEqual(
            action["supersedes_prior_entry_payload_sha256"], [prior_digest]
        )
        self.assertTrue(action["reviewer_body_required"])
        self.assertNotIn("body", action)

        # Changing the artifact kind and removing the marker still cannot turn
        # a fresh candidate into evidence: the reviewer body is absent.
        incomplete = copy.deepcopy(action)
        incomplete.pop("candidate_only")
        plan = base_plan(surface, prior, [incomplete])
        with self.assertRaisesRegex(REISSUE.StatementReceiptReissueError, "reviewer body"):
            REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

    def test_action_scaffold_ties_changed_source_target_to_fresh_supersession(self) -> None:
        old_source = "P x in the prior transcript"
        current_source = "P x in the revised transcript"
        old_target = make_target(paper_statement=old_source)
        current_target = make_target(paper_statement=current_source)
        prior = prior_sidecar(
            generated_entry(old_target, body=fresh_body(source_statement=old_source))
        )
        prior_digest = next(iter(prior.groups))
        surface = make_surface(current_target, source_statement=current_source)

        scaffold = REISSUE.statement_receipt_reissue_action_scaffold(surface, prior)

        self.assertEqual(scaffold["unresolved_semantic_classes"], [])
        self.assertEqual(len(scaffold["candidate_actions"]), 1)
        action = scaffold["candidate_actions"][0]
        self.assertEqual(action["action"], "fresh")
        self.assertEqual(
            action["classification"], "same_semantic_class_stale_source_identity"
        )
        self.assertEqual(action["target"], current_target.descriptor())
        self.assertEqual(
            action["supersedes_prior_entry_payload_sha256"], [prior_digest]
        )

    def test_action_scaffold_marks_nonmatching_prior_class_for_retirement(self) -> None:
        target = make_target(translation="current P x")
        surface = make_surface(target)
        orphan_target = make_target(translation="orphan P x")
        prior = prior_sidecar(generated_entry(orphan_target))
        prior_digest = next(iter(prior.groups))

        scaffold = REISSUE.statement_receipt_reissue_action_scaffold(surface, prior)

        retire = [
            action
            for action in scaffold["candidate_actions"]
            if action["action"] == "retire"
        ]
        self.assertEqual(len(retire), 1)
        self.assertEqual(retire[0]["classification"], "no_current_semantic_class_match")
        self.assertEqual(retire[0]["prior_entry_payload_sha256"], prior_digest)
        self.assertTrue(retire[0]["reviewer_reason_required"])
        self.assertNotIn("reason", retire[0])

    def test_action_scaffold_refuses_to_guess_between_same_class_targets(self) -> None:
        first = make_target(paper_statement="P one")
        second = make_target(paper_statement="P two")
        stale = make_target(paper_statement="P before source repair")
        surface = make_surface(first, second)
        prior = prior_sidecar(generated_entry(stale))
        prior_digest = next(iter(prior.groups))

        scaffold = REISSUE.statement_receipt_reissue_action_scaffold(surface, prior)

        self.assertEqual(scaffold["candidate_actions"], [])
        self.assertEqual(len(scaffold["unresolved_semantic_classes"]), 1)
        unresolved = scaffold["unresolved_semantic_classes"][0]
        self.assertEqual(
            unresolved["classification"], "ambiguous_same_semantic_class_supersession"
        )
        self.assertEqual(
            {value["semantic_target_sha256"] for value in unresolved["current_targets"]},
            {first.semantic_target_sha256, second.semantic_target_sha256},
        )
        self.assertEqual(
            unresolved["prior_payload_groups"][0]["prior_entry_payload_sha256"],
            prior_digest,
        )

    def test_fresh_replaces_payload_and_archives_exact_prior_bytes(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar(generated_entry(target))
        old_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "fresh",
                    "target": target.descriptor(),
                    "body": fresh_body(),
                    "supersedes_prior_entry_payload_sha256": [old_digest],
                }
            ],
        )

        result = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

        self.assertEqual(result.report["fresh_target_count"], 1)
        self.assertEqual(result.report["reused_target_count"], 0)
        self.assertIn("semantic_" + target.semantic_target_sha256, result.sidecar["items"])
        self.assertIsNotNone(result.archive)
        assert result.archive is not None
        self.assertEqual(result.archive["prior_sidecar_sha256"], prior.raw_sha256)
        self.assertEqual(
            base64.b64decode(result.archive["prior_sidecar_bytes_base64"]), prior.raw_bytes
        )

    def test_historical_replay_reuse_statically_transports_every_lean_atom(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )

        # Materialization has no runner argument. Guard the explicit strong
        # verifier to make the no-second-Lean-run contract visible here.
        with (
            mock.patch.object(
                HISTORICAL_REPLAY,
                "validate_historical_statement_manifest_replay_static",
                wraps=HISTORICAL_REPLAY.validate_historical_statement_manifest_replay_static,
            ) as static_validator,
            mock.patch.object(
                HISTORICAL_REPLAY,
                "validate_historical_statement_manifest_replay_replay",
                side_effect=AssertionError("materialization must not rerun historic Lean"),
            ),
        ):
            result = REISSUE.materialize_statement_receipt_reissue(
                surface,
                prior,
                plan,
                **historical_replay_materialization_kwargs(
                    bridge=bridge,
                    bridge_bytes=bridge_bytes,
                    carrier=carrier,
                    carrier_bytes=carrier_bytes,
                    authority=authority,
                    authority_bytes=authority_bytes,
                ),
                historical_manifest_replay_recipe_verifier=verified_historical_recipe,
            )
        static_validator.assert_called_once()

        self.assertEqual(result.report["fresh_target_count"], 0)
        self.assertEqual(result.report["reused_target_count"], 0)
        self.assertEqual(result.report["historical_replay_reused_target_count"], 1)
        entry = next(iter(result.sidecar["items"].values()))
        self.assertEqual(entry["lean_signature_sha256"], target.lean_signature_sha256)
        obligations = entry["lean_obligations"]
        assert isinstance(obligations, list)
        self.assertEqual(
            {str(obligation["signature_ref"]) for obligation in obligations},
            {"new/0", "result"},
        )
        manifest_atoms = {
            str(atom["ref"]): review_dashboard.signature_manifest_atom_digest(atom)
            for atom in target.manifest["atoms"]
        }
        self.assertEqual(
            {
                str(obligation["signature_ref"]): str(
                    obligation["signature_atom_sha256"]
                )
                for obligation in obligations
            },
            manifest_atoms,
        )
        provenance = entry[REISSUE.HISTORICAL_REPLAY_PROVENANCE_FIELD]
        assert isinstance(provenance, dict)
        self.assertEqual(
            provenance["replay_artifact_bytes_sha256"],
            REISSUE._bytes_sha256(bridge_bytes),
        )
        self.assertEqual(
            provenance["prior_sidecar_bytes_sha256"], prior.raw_sha256,
        )
        self.assertEqual(
            provenance["replay_artifact_path"],
            "audit/historical_statement_manifest_replay.json",
        )
        self.assertEqual(
            provenance["historical_manifest_carrier_bytes_sha256"],
            REISSUE._bytes_sha256(carrier_bytes),
        )
        self.assertEqual(
            provenance["historical_manifest_authority_bytes_sha256"],
            REISSUE._bytes_sha256(authority_bytes),
        )
        self.assertEqual(
            provenance["current_source_record_audit_path"],
            "audit/current_source_record_audit.json",
        )
        self.assertEqual(
            provenance["current_source_record_audit_bytes_sha256"],
            REISSUE._bytes_sha256(FIXTURE_SOURCE_RECORD_AUDIT_BYTES),
        )
        self.assertEqual(
            provenance["current_lean_import_closure_sha256"],
            FIXTURE_CLOSURE_SHA256,
        )
        self.assertEqual(provenance["prior_sidecar_archive_path"], "audit/prior.json")
        self.assertNotIn("navigation_0", json.dumps(provenance, sort_keys=True))
        assert result.archive is not None
        self.assertEqual(
            result.archive["historical_statement_manifest_replay_transports"],
            [provenance],
        )

    def test_recovered_manifest_store_replay_transports_only_verified_raw_carrier(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        legacy_plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        bundle = recovered_manifest_store_bundle(
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )
        plan = recovered_historical_replay_plan(legacy_plan, bundle)

        with mock.patch.object(
            HISTORICAL_REPLAY,
            "validate_historical_statement_manifest_replay_replay",
            side_effect=AssertionError("recovered materialization must not rerun historic Lean"),
        ):
            result = REISSUE.materialize_statement_receipt_reissue(
                surface,
                prior,
                plan,
                **recovered_historical_replay_materialization_kwargs(
                    bridge=bridge,
                    bridge_bytes=bridge_bytes,
                    bundle=bundle,
                ),
                historical_manifest_replay_recipe_verifier=verified_historical_recipe,
            )

        self.assertEqual(result.report["historical_replay_reused_target_count"], 1)
        entry = next(iter(result.sidecar["items"].values()))
        provenance = entry[REISSUE.HISTORICAL_REPLAY_PROVENANCE_FIELD]
        assert isinstance(provenance, dict)
        self.assertEqual(
            provenance["policy_version"],
            REISSUE.HISTORICAL_REPLAY_RECOVERED_STORE_PROVENANCE_POLICY_VERSION,
        )
        self.assertEqual(
            set(provenance),
            REISSUE._PERSISTED_HISTORICAL_REPLAY_RECOVERED_STORE_PROVENANCE_FIELDS,
        )
        self.assertNotIn("historical_manifest_carrier_path", provenance)
        self.assertNotIn("historical_manifest_authority_path", provenance)
        recovered = provenance[REISSUE.HISTORICAL_REPLAY_RECOVERED_STORE_FIELD]
        assert isinstance(recovered, dict)
        self.assertEqual(
            recovered["carrier_compressed_bytes_sha256"],
            REISSUE._bytes_sha256(bundle["carrier_compressed_bytes"]),  # type: ignore[arg-type]
        )
        self.assertEqual(
            recovered["authority_bytes_sha256"],
            REISSUE._bytes_sha256(bundle["authority_bytes"]),  # type: ignore[arg-type]
        )
        self.assertEqual(
            recovered["recovery_receipt_bytes_sha256"],
            REISSUE._bytes_sha256(bundle["receipt_bytes"]),  # type: ignore[arg-type]
        )

    def test_verified_recovered_store_reader_feeds_direct_bridge_construction(self) -> None:
        (
            surface,
            prior,
            _target,
            bridge,
            _bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        bundle = recovered_manifest_store_bundle(
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )
        verified_authority, verified_carrier, raw_carrier = (
            STORE_RECOVERY.verified_recovered_manifest_store_artifacts(
                paper=PAPER,
                receipt=bundle["receipt"],  # type: ignore[arg-type]
                receipt_bytes=bundle["receipt_bytes"],  # type: ignore[arg-type]
                authority_bytes=bundle["authority_bytes"],  # type: ignore[arg-type]
                carrier_compressed_bytes=bundle["carrier_compressed_bytes"],  # type: ignore[arg-type]
            )
        )
        rebuilt, error = HISTORICAL_REPLAY.build_historical_statement_manifest_replay(
            paper=PAPER,
            historical_serializer_recipe=HISTORICAL_FIXTURE.recipe(),
            prior_sidecar=prior.payload,
            prior_sidecar_bytes=prior.raw_bytes,
            historical_manifest_carrier=verified_carrier,
            historical_manifest_carrier_bytes=raw_carrier,
            historical_manifest_authority=verified_authority,
            historical_manifest_authority_bytes=bytes(bundle["authority_bytes"]),
            current_targets=REISSUE.historical_manifest_replay_current_targets(surface),
            current_evidence_sha256=(
                REISSUE.historical_manifest_replay_current_evidence_sha256(surface)
            ),
            historical_manifest_runner=HISTORICAL_FIXTURE.historic_runner(
                {str(surface.targets[0].manifest["sha256"]): HISTORICAL_FIXTURE.historic_manifest()}
            ),
            historical_blob_verifier=HISTORICAL_FIXTURE.blob_verifier,
            current_target_validator=(
                lambda raw: REISSUE._historical_manifest_replay_target_validator(
                    surface, raw
                )
            ),
            source_route_validator=(
                lambda raw: REISSUE._historical_manifest_replay_source_route_validator(
                    surface, raw
                )
            ),
        )
        self.assertEqual(error, "")
        self.assertEqual(rebuilt, bridge)

    def test_recovered_manifest_store_replay_rejects_forged_gzip_and_receipt_mismatch(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        legacy_plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        bundle = recovered_manifest_store_bundle(
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )
        plan = recovered_historical_replay_plan(legacy_plan, bundle)
        kwargs = recovered_historical_replay_materialization_kwargs(
            bridge=bridge,
            bridge_bytes=bridge_bytes,
            bundle=bundle,
        )

        with self.subTest("forged gzip remains rejected after its plan pin is changed"):
            forged_plan = copy.deepcopy(plan)
            descriptor = forged_plan[REISSUE.HISTORICAL_REPLAY_PLAN_FIELD]
            assert isinstance(descriptor, dict)
            recovered = descriptor[REISSUE.HISTORICAL_REPLAY_RECOVERED_STORE_FIELD]
            assert isinstance(recovered, dict)
            forged_gzip = bytes(bundle["carrier_compressed_bytes"]) + b"forged"
            recovered["carrier_compressed_bytes_sha256"] = REISSUE._bytes_sha256(
                forged_gzip
            )
            forged_kwargs = dict(kwargs)
            forged_kwargs[
                "historical_manifest_store_recovery_carrier_compressed_bytes"
            ] = forged_gzip
            with self.assertRaisesRegex(
                REISSUE.StatementReceiptReissueError,
                "recovery bundle does not verify: compressed carrier bytes",
            ):
                REISSUE.materialize_statement_receipt_reissue(
                    surface,
                    prior,
                    forged_plan,
                    **forged_kwargs,
                    historical_manifest_replay_recipe_verifier=verified_historical_recipe,
                )

        with self.subTest("receipt object cannot disagree with its exact raw bytes"):
            mismatched_kwargs = dict(kwargs)
            forged_receipt = dict(bundle["receipt"])
            forged_receipt["paper"] = "OtherPaper"
            mismatched_kwargs["historical_manifest_store_recovery_receipt"] = (
                forged_receipt
            )
            with self.assertRaisesRegex(
                REISSUE.StatementReceiptReissueError,
                "recovery receipt object differs from its exact bytes",
            ):
                REISSUE.materialize_statement_receipt_reissue(
                    surface,
                    prior,
                    plan,
                    **mismatched_kwargs,
                    historical_manifest_replay_recipe_verifier=verified_historical_recipe,
                )

        with self.subTest("forged receipt bytes remain rejected after their plan pin is changed"):
            forged_plan = copy.deepcopy(plan)
            descriptor = forged_plan[REISSUE.HISTORICAL_REPLAY_PLAN_FIELD]
            assert isinstance(descriptor, dict)
            recovered = descriptor[REISSUE.HISTORICAL_REPLAY_RECOVERED_STORE_FIELD]
            assert isinstance(recovered, dict)
            forged_receipt = dict(bundle["receipt"])
            forged_receipt["paper"] = "OtherPaper"
            forged_receipt_bytes = REISSUE._json_bytes(forged_receipt)
            recovered["recovery_receipt_bytes_sha256"] = REISSUE._bytes_sha256(
                forged_receipt_bytes
            )
            forged_kwargs = dict(kwargs)
            forged_kwargs["historical_manifest_store_recovery_receipt"] = (
                forged_receipt
            )
            forged_kwargs["historical_manifest_store_recovery_receipt_bytes"] = (
                forged_receipt_bytes
            )
            with self.assertRaisesRegex(
                REISSUE.StatementReceiptReissueError,
                "recovery bundle does not verify: recovery receipt has the wrong schema, policy, or paper",
            ):
                REISSUE.materialize_statement_receipt_reissue(
                    surface,
                    prior,
                    forged_plan,
                    **forged_kwargs,
                    historical_manifest_replay_recipe_verifier=verified_historical_recipe,
                )

    def test_historical_replay_action_requires_its_byte_pinned_artifact(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        inputs = historical_replay_materialization_kwargs(
            bridge=bridge,
            bridge_bytes=bridge_bytes,
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )

        with self.assertRaisesRegex(
            REISSUE.StatementReceiptReissueError,
            "static historical recipe verifier is required",
        ):
            REISSUE.materialize_statement_receipt_reissue(
                surface,
                prior,
                plan,
                **inputs,
            )

        with self.assertRaisesRegex(
            REISSUE.StatementReceiptReissueError,
            "artifact bytes differ from the plan pin",
        ):
            REISSUE.materialize_statement_receipt_reissue(
                surface,
                prior,
                plan,
                **{
                    **inputs,
                    "historical_manifest_replay_bytes": bridge_bytes + b"\n",
                },
                historical_manifest_replay_recipe_verifier=verified_historical_recipe,
            )

        # A bridge artifact may not silently turn ordinary reuse into a
        # transport path.  The distinct action is required.
        ordinary_reuse = copy.deepcopy(plan)
        actions = ordinary_reuse["actions"]
        assert isinstance(actions, list)
        actions[0]["action"] = "reuse"
        actions[0].pop("historical_manifest_replay_sha256")
        with self.assertRaisesRegex(
            REISSUE.StatementReceiptReissueError,
            "no historical_replay_reuse action",
        ):
            REISSUE.materialize_statement_receipt_reissue(
                surface,
                prior,
                ordinary_reuse,
                **inputs,
                historical_manifest_replay_recipe_verifier=verified_historical_recipe,
            )

    def test_historical_replay_recipe_verifier_rejects_rehashed_fake_git_recipe(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            _bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        mutations = (
            ("historical_git_commit", "d" * 40),
            ("historical_serializer_blob.git_object_id", "e" * 40),
            ("runner_identity_sha256", "f" * 64),
        )
        for field, replacement in mutations:
            with self.subTest(field=field):
                tampered = copy.deepcopy(bridge)
                recipe = tampered["historical_serializer_recipe"]
                assert isinstance(recipe, dict)
                if "." in field:
                    outer, inner = field.split(".", maxsplit=1)
                    nested = recipe[outer]
                    assert isinstance(nested, dict)
                    nested[inner] = replacement
                else:
                    recipe[field] = replacement
                tampered["historical_serializer_recipe_sha256"] = (
                    HISTORICAL_REPLAY.historical_serializer_recipe_sha256(recipe)
                )
                tampered[
                    HISTORICAL_REPLAY.HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD
                ] = HISTORICAL_REPLAY.historical_statement_manifest_replay_digest(
                    tampered
                )
                tampered_bytes = REISSUE._json_bytes(tampered)
                plan = historical_replay_plan(
                    surface,
                    prior,
                    target,
                    tampered,
                    tampered_bytes,
                    carrier_bytes,
                    authority_bytes,
                )
                with self.assertRaisesRegex(
                    REISSUE.StatementReceiptReissueError,
                    "recipe is not independently verified",
                ):
                    REISSUE.materialize_statement_receipt_reissue(
                        surface,
                        prior,
                        plan,
                        **historical_replay_materialization_kwargs(
                            bridge=tampered,
                            bridge_bytes=tampered_bytes,
                            carrier=carrier,
                            carrier_bytes=carrier_bytes,
                            authority=authority,
                            authority_bytes=authority_bytes,
                        ),
                        historical_manifest_replay_recipe_verifier=(
                            verified_historical_recipe
                        ),
                    )

    def test_historical_replay_rejects_changed_current_route_surface(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        changed_surface = copy.deepcopy(surface)
        changed_route = changed_surface.source_route_inventory["source_result"]
        changed_route["source_location"] = "source.txt:2-2"
        changed_surface.source_route_inventory_sha256 = REISSUE._route_inventory_digest(
            changed_surface.source_route_inventory
        )
        plan["current_inputs"] = changed_surface.input_pins()

        with self.assertRaisesRegex(
            REISSUE.StatementReceiptReissueError,
            "not current static evidence",
        ):
            REISSUE.materialize_statement_receipt_reissue(
                changed_surface,
                prior,
                plan,
                **historical_replay_materialization_kwargs(
                    bridge=bridge,
                    bridge_bytes=bridge_bytes,
                    carrier=carrier,
                    carrier_bytes=carrier_bytes,
                    authority=authority,
                    authority_bytes=authority_bytes,
                ),
                historical_manifest_replay_recipe_verifier=verified_historical_recipe,
            )

    def test_historical_replay_already_applied_reconstructs_only_from_archive(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        inputs = historical_replay_materialization_kwargs(
            bridge=bridge,
            bridge_bytes=bridge_bytes,
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )
        expected = REISSUE.materialize_statement_receipt_reissue(
            surface,
            prior,
            plan,
            **inputs,
            historical_manifest_replay_recipe_verifier=verified_historical_recipe,
        )
        assert expected.archive is not None

        with tempfile.TemporaryDirectory() as temporary:
            temporary_path = Path(temporary)
            output_path = temporary_path / "statement_match_llm.json"
            archive_path = temporary_path / "prior.json"
            output_path.write_bytes(REISSUE._json_bytes(expected.sidecar))
            archive_path.write_bytes(REISSUE._json_bytes(expected.archive))
            applied = REISSUE.already_applied_statement_receipt_reissue(
                surface,
                REISSUE.load_prior_sidecar(output_path),
                plan,
                archive_path=archive_path,
                **inputs,
                historical_manifest_replay_recipe_verifier=verified_historical_recipe,
            )
            self.assertIsNotNone(applied)
            assert applied is not None
            self.assertTrue(applied.report["already_applied"])
            self.assertEqual(
                applied.report["historical_replay_reused_target_count"], 1
            )

    def test_persisted_historical_replay_gate_reconstructs_transport_without_lean(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        inputs = historical_replay_materialization_kwargs(
            bridge=bridge,
            bridge_bytes=bridge_bytes,
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )
        expected = REISSUE.materialize_statement_receipt_reissue(
            surface,
            prior,
            plan,
            **inputs,
            historical_manifest_replay_recipe_verifier=verified_historical_recipe,
        )
        assert expected.archive is not None

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "papers" / PAPER
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "statement_match_llm.json").write_bytes(
                REISSUE._json_bytes(expected.sidecar)
            )
            (audit / "prior.json").write_bytes(REISSUE._json_bytes(expected.archive))
            (audit / "historical_statement_manifest_replay.json").write_bytes(
                bridge_bytes
            )
            (audit / "historical_manifest_carrier.json").write_bytes(carrier_bytes)
            (audit / "historical_manifest_authority.json").write_bytes(authority_bytes)
            (audit / "current_source_record_audit.json").write_bytes(
                FIXTURE_SOURCE_RECORD_AUDIT_BYTES
            )

            with (
                mock.patch.object(
                    REISSUE, "current_statement_receipt_surface", return_value=surface
                ),
                mock.patch.object(
                    REISSUE,
                    "_validated_current_source_record_closure_authority",
                    side_effect=fixture_source_record_authority,
                ),
                mock.patch.object(
                    REISSUE,
                    "_historical_manifest_replay_cli_recipe_verifier",
                    return_value=verified_historical_recipe,
                ),
                mock.patch.object(
                    HISTORICAL_REPLAY,
                    "validate_historical_statement_manifest_replay_replay",
                    side_effect=AssertionError("persisted gate must not rerun historic Lean"),
                ),
            ):
                self.assertEqual(
                    REISSUE.historical_manifest_replay_persisted_evidence_errors(
                        folder
                    ),
                    [],
                )

            # A byte-identical JSON structure is insufficient: each retrieval
            # coordinate is bound to the raw artifact digest in the sidecar.
            (audit / "historical_manifest_carrier.json").write_bytes(
                carrier_bytes + b"\n"
            )
            with mock.patch.object(
                REISSUE, "current_statement_receipt_surface", return_value=surface
            ):
                errors = REISSUE.historical_manifest_replay_persisted_evidence_errors(
                    folder
                )
            self.assertTrue(
                any("historical manifest carrier bytes differ" in error for error in errors),
                errors,
            )

    def test_persisted_recovered_manifest_store_gate_reconstructs_without_lean(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        legacy_plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        bundle = recovered_manifest_store_bundle(
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )
        plan = recovered_historical_replay_plan(legacy_plan, bundle)
        inputs = recovered_historical_replay_materialization_kwargs(
            bridge=bridge,
            bridge_bytes=bridge_bytes,
            bundle=bundle,
        )
        expected = REISSUE.materialize_statement_receipt_reissue(
            surface,
            prior,
            plan,
            **inputs,
            historical_manifest_replay_recipe_verifier=verified_historical_recipe,
        )
        assert expected.archive is not None

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "papers" / PAPER
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "statement_match_llm.json").write_bytes(
                REISSUE._json_bytes(expected.sidecar)
            )
            (audit / "prior.json").write_bytes(REISSUE._json_bytes(expected.archive))
            (audit / "historical_statement_manifest_replay.json").write_bytes(
                bridge_bytes
            )
            (folder / str(bundle["receipt_path"])).write_bytes(
                bytes(bundle["receipt_bytes"])
            )
            (folder / str(bundle["authority_path"])).write_bytes(
                bytes(bundle["authority_bytes"])
            )
            (folder / str(bundle["carrier_compressed_path"])).write_bytes(
                bytes(bundle["carrier_compressed_bytes"])
            )
            (audit / "current_source_record_audit.json").write_bytes(
                FIXTURE_SOURCE_RECORD_AUDIT_BYTES
            )

            with (
                mock.patch.object(
                    REISSUE, "current_statement_receipt_surface", return_value=surface
                ),
                mock.patch.object(
                    REISSUE,
                    "_validated_current_source_record_closure_authority",
                    side_effect=fixture_source_record_authority,
                ),
                mock.patch.object(
                    REISSUE,
                    "_historical_manifest_replay_cli_recipe_verifier",
                    return_value=verified_historical_recipe,
                ),
                mock.patch.object(
                    HISTORICAL_REPLAY,
                    "validate_historical_statement_manifest_replay_replay",
                    side_effect=AssertionError("persisted recovered gate must not rerun historic Lean"),
                ),
            ):
                self.assertEqual(
                    REISSUE.historical_manifest_replay_persisted_evidence_errors(
                        folder
                    ),
                    [],
                )

            (folder / str(bundle["carrier_compressed_path"])).write_bytes(
                bytes(bundle["carrier_compressed_bytes"]) + b"changed"
            )
            with mock.patch.object(
                REISSUE, "current_statement_receipt_surface", return_value=surface
            ):
                errors = REISSUE.historical_manifest_replay_persisted_evidence_errors(
                    folder
                )
            self.assertTrue(
                any("compressed carrier bytes differ" in error for error in errors),
                errors,
            )

    def test_evidence_integrity_hook_runs_only_for_persisted_transports(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "FixturePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "statement_match_llm.json").write_bytes(
                REISSUE._json_bytes(
                    {
                        "items": {
                            "navigation_only": {
                                REISSUE.HISTORICAL_REPLAY_PROVENANCE_FIELD: {}
                            }
                        }
                    }
                )
            )
            with mock.patch.object(
                PACKAGE_REISSUE,
                "historical_manifest_replay_persisted_evidence_errors",
                return_value=["fixture replay artifact is stale"],
            ) as gate:
                findings = (
                    EVIDENCE_INTEGRITY.historical_statement_manifest_replay_evidence_findings(
                        folder, "paper draft"
                    )
                )
            gate.assert_called_once_with(folder)
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].severity, "ERROR")
            self.assertIn("fixture replay artifact is stale", findings[0].message)

    def test_selected_v11_lane_never_replays_historical_statement_transport(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "FixturePaper"
            context = SimpleNamespace(v11_lean_claim_graph_selected=True)
            with mock.patch.object(
                PACKAGE_REISSUE,
                "historical_manifest_replay_persisted_evidence_errors",
                side_effect=AssertionError("selected v11 must not replay legacy transport"),
            ) as gate:
                findings = (
                    EVIDENCE_INTEGRITY.historical_statement_manifest_replay_evidence_findings(
                        folder,
                        "formalized",
                        context=context,
                    )
                )

            self.assertEqual(findings, [])
            gate.assert_not_called()

    def test_already_applied_requires_exact_post_sidecar_and_archive_bytes(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar(generated_entry(target))
        old_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "fresh",
                    "target": target.descriptor(),
                    "body": fresh_body(),
                    "supersedes_prior_entry_payload_sha256": [old_digest],
                }
            ],
        )
        expected = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)
        self.assertIsNotNone(expected.archive)
        assert expected.archive is not None

        with tempfile.TemporaryDirectory() as temporary:
            temporary_path = Path(temporary)
            output_path = temporary_path / "statement_match_llm.json"
            archive_path = temporary_path / "prior.json"
            output_path.write_bytes(REISSUE._json_bytes(expected.sidecar))
            archive_path.write_bytes(REISSUE._json_bytes(expected.archive))

            applied = REISSUE.already_applied_statement_receipt_reissue(
                surface,
                REISSUE.load_prior_sidecar(output_path),
                plan,
                archive_path=archive_path,
            )
            self.assertIsNotNone(applied)
            assert applied is not None
            self.assertTrue(applied.report["already_applied"])
            self.assertEqual(applied.report["fresh_target_count"], 1)
            with self.assertRaisesRegex(
                REISSUE.StatementReceiptReissueError,
                "stale prior-sidecar raw-byte digest",
            ):
                REISSUE.materialize_statement_receipt_reissue(
                    surface,
                    REISSUE.load_prior_sidecar(output_path),
                    plan,
                )

            # Equivalent JSON with different bytes is not sufficient proof: a
            # later manual edit must remain a stale-plan failure.
            output_path.write_text(
                json.dumps(expected.sidecar, sort_keys=True) + "\n", encoding="utf-8"
            )
            self.assertIsNone(
                REISSUE.already_applied_statement_receipt_reissue(
                    surface,
                    REISSUE.load_prior_sidecar(output_path),
                    plan,
                    archive_path=archive_path,
                )
            )

            output_path.write_bytes(REISSUE._json_bytes(expected.sidecar))
            # The archive is itself part of the immutable proof. Whitespace
            # keeps it parseable but makes it no longer the original artifact.
            archive_path.write_bytes(REISSUE._json_bytes(expected.archive) + b"\n")
            self.assertIsNone(
                REISSUE.already_applied_statement_receipt_reissue(
                    surface,
                    REISSUE.load_prior_sidecar(output_path),
                    plan,
                    archive_path=archive_path,
                )
            )

    def test_already_applied_without_prior_preserves_stale_surface_rejection(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = REISSUE.PriorSidecar(False, b"", "", {}, {})
        plan = base_plan(
            surface,
            prior,
            [{"action": "fresh", "target": target.descriptor(), "body": fresh_body()}],
        )
        expected = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

        with tempfile.TemporaryDirectory() as temporary:
            output_path = Path(temporary) / "statement_match_llm.json"
            output_path.write_bytes(REISSUE._json_bytes(expected.sidecar))
            current = REISSUE.load_prior_sidecar(output_path)
            applied = REISSUE.already_applied_statement_receipt_reissue(
                surface, current, plan
            )
            self.assertIsNotNone(applied)

            stale_surface = copy.deepcopy(surface)
            stale_surface.cache_sha256 = "d" * 64
            self.assertIsNone(
                REISSUE.already_applied_statement_receipt_reissue(
                    stale_surface, current, plan
                )
            )
            with self.assertRaisesRegex(
                REISSUE.StatementReceiptReissueError, "stale `cache_sha256`"
            ):
                REISSUE.materialize_statement_receipt_reissue(
                    stale_surface,
                    REISSUE.PriorSidecar(False, b"", "", {}, {}),
                    plan,
                )

    def test_cli_reports_already_applied_without_rewriting_receipts(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar(generated_entry(target))
        old_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "fresh",
                    "target": target.descriptor(),
                    "body": fresh_body(),
                    "supersedes_prior_entry_payload_sha256": [old_digest],
                }
            ],
        )
        expected = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)
        self.assertIsNotNone(expected.archive)
        assert expected.archive is not None

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            audit = root / "papers" / PAPER / "audit"
            audit.mkdir(parents=True)
            output_path = audit / "statement_match_llm.json"
            archive_path = audit / "prior.json"
            plan_path = audit / "plan.json"
            output_path.write_bytes(REISSUE._json_bytes(expected.sidecar))
            archive_path.write_bytes(REISSUE._json_bytes(expected.archive))
            plan_path.write_bytes(REISSUE._json_bytes(plan))
            output_before = output_path.read_bytes()
            archive_before = archive_path.read_bytes()
            stdout = io.StringIO()

            with (
                mock.patch.object(REISSUE, "ROOT", root),
                mock.patch.object(
                    REISSUE, "current_statement_receipt_surface", return_value=surface
                ),
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "statement_receipt_reissue.py",
                        "--root",
                        str(root),
                        "--paper",
                        PAPER,
                        "--plan",
                        "audit/plan.json",
                        "--out",
                        "audit/statement_match_llm.json",
                        "--archive",
                        "audit/prior.json",
                        "--write",
                    ],
                ),
                redirect_stdout(stdout),
            ):
                self.assertEqual(REISSUE.main(), 0)

            self.assertIn("receipt reissue already applied", stdout.getvalue())
            self.assertEqual(output_path.read_bytes(), output_before)
            self.assertEqual(archive_path.read_bytes(), archive_before)

    def test_cli_treats_all_reuse_plan_as_noop_without_storage_opt_in(self) -> None:
        """Exact semantic reuse must not create a fresh-looking receipt archive."""

        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar(generated_entry(target))
        prior_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "reuse",
                    "target": target.descriptor(),
                    "prior_entry_payload_sha256": prior_digest,
                }
            ],
        )

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            audit = root / "papers" / PAPER / "audit"
            audit.mkdir(parents=True)
            output_path = audit / "statement_match_llm.json"
            plan_path = audit / "plan.json"
            output_path.write_bytes(prior.raw_bytes)
            plan_path.write_bytes(REISSUE._json_bytes(plan))
            output_before = output_path.read_bytes()
            stdout = io.StringIO()

            with (
                mock.patch.object(REISSUE, "ROOT", root),
                mock.patch.object(
                    REISSUE, "current_statement_receipt_surface", return_value=surface
                ),
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "statement_receipt_reissue.py",
                        "--root",
                        str(root),
                        "--paper",
                        PAPER,
                        "--plan",
                        "audit/plan.json",
                        "--out",
                        "audit/statement_match_llm.json",
                        "--write",
                    ],
                ),
                redirect_stdout(stdout),
            ):
                self.assertEqual(REISSUE.main(), 0)

            self.assertIn("no statement receipt or archive was written", stdout.getvalue())
            self.assertEqual(output_path.read_bytes(), output_before)
            self.assertFalse((audit / "unexpected-archive.json").exists())

    def test_cli_loads_only_the_exact_plan_pinned_historical_replay_artifact(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            audit = root / "papers" / PAPER / "audit"
            audit.mkdir(parents=True)
            output_path = audit / "statement_match_llm.json"
            plan_path = audit / "plan.json"
            bridge_path = audit / "historical_statement_manifest_replay.json"
            carrier_path = audit / "historical_manifest_carrier.json"
            authority_path = audit / "historical_manifest_authority.json"
            source_record_path = audit / "current_source_record_audit.json"
            output_path.write_bytes(prior.raw_bytes)
            plan_path.write_bytes(REISSUE._json_bytes(plan))
            bridge_path.write_bytes(bridge_bytes)
            carrier_path.write_bytes(carrier_bytes)
            authority_path.write_bytes(authority_bytes)
            source_record_path.write_bytes(FIXTURE_SOURCE_RECORD_AUDIT_BYTES)
            stdout = io.StringIO()

            with (
                mock.patch.object(REISSUE, "ROOT", root),
                mock.patch.object(
                    REISSUE, "current_statement_receipt_surface", return_value=surface
                ),
                mock.patch.object(
                    REISSUE,
                    "_historical_manifest_replay_cli_recipe_verifier",
                    return_value=verified_historical_recipe,
                ) as recipe_verifier_factory,
                mock.patch.object(
                    REISSUE,
                    "_validated_current_source_record_closure_authority",
                    side_effect=fixture_source_record_authority,
                ),
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "statement_receipt_reissue.py",
                        "--root",
                        str(root),
                        "--paper",
                        PAPER,
                        "--plan",
                        "audit/plan.json",
                        "--out",
                        "audit/statement_match_llm.json",
                        "--archive",
                        "audit/prior.json",
                        "--historical-manifest-replay",
                        "audit/historical_statement_manifest_replay.json",
                        "--historical-manifest-carrier",
                        "audit/historical_manifest_carrier.json",
                        "--historical-manifest-authority",
                        "audit/historical_manifest_authority.json",
                        "--historical-source-record-audit",
                        "audit/current_source_record_audit.json",
                    ],
                ),
                redirect_stdout(stdout),
            ):
                self.assertEqual(REISSUE.main(), 0)

            self.assertIn("1 historically transported", stdout.getvalue())
            recipe_verifier_factory.assert_called_once()
            self.assertEqual(recipe_verifier_factory.call_args.kwargs["root"], root)
            self.assertEqual(
                recipe_verifier_factory.call_args.kwargs["paper_dir"],
                root / "papers" / PAPER,
            )
            self.assertEqual(
                recipe_verifier_factory.call_args.kwargs["current_lean_import_closure"],
                FIXTURE_CLOSURE,
            )
            self.assertEqual(
                recipe_verifier_factory.call_args.kwargs[
                    "current_lean_import_closure_bytes"
                ],
                FIXTURE_CLOSURE_BYTES,
            )

            # A path is a retrieval coordinate only, but it must equal the
            # coordinate that the plan byte-pins; another byte-identical file
            # cannot be substituted silently.
            other_path = audit / "other.json"
            other_path.write_bytes(bridge_bytes)
            stderr = io.StringIO()
            with (
                mock.patch.object(REISSUE, "ROOT", root),
                mock.patch.object(
                    REISSUE, "current_statement_receipt_surface", return_value=surface
                ),
                mock.patch.object(
                    REISSUE,
                    "_historical_manifest_replay_cli_recipe_verifier",
                    return_value=verified_historical_recipe,
                ),
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "statement_receipt_reissue.py",
                        "--root",
                        str(root),
                        "--paper",
                        PAPER,
                        "--plan",
                        "audit/plan.json",
                        "--out",
                        "audit/statement_match_llm.json",
                        "--archive",
                        "audit/prior.json",
                        "--historical-manifest-replay",
                        "audit/other.json",
                        "--historical-manifest-carrier",
                        "audit/historical_manifest_carrier.json",
                        "--historical-manifest-authority",
                        "audit/historical_manifest_authority.json",
                        "--historical-source-record-audit",
                        "audit/current_source_record_audit.json",
                    ],
                ),
                redirect_stdout(io.StringIO()),
                mock.patch.object(sys, "stderr", stderr),
            ):
                self.assertEqual(REISSUE.main(), 1)
            self.assertIn("path does not equal the plan pin", stderr.getvalue())

    def test_cli_accepts_recovered_manifest_store_bundle(self) -> None:
        (
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier,
            carrier_bytes,
            authority,
            authority_bytes,
        ) = historical_replay_fixture()
        legacy_plan = historical_replay_plan(
            surface,
            prior,
            target,
            bridge,
            bridge_bytes,
            carrier_bytes,
            authority_bytes,
        )
        bundle = recovered_manifest_store_bundle(
            carrier=carrier,
            carrier_bytes=carrier_bytes,
            authority=authority,
            authority_bytes=authority_bytes,
        )
        plan = recovered_historical_replay_plan(legacy_plan, bundle)

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            audit = root / "papers" / PAPER / "audit"
            audit.mkdir(parents=True)
            (audit / "statement_match_llm.json").write_bytes(prior.raw_bytes)
            (audit / "plan.json").write_bytes(REISSUE._json_bytes(plan))
            (audit / "historical_statement_manifest_replay.json").write_bytes(
                bridge_bytes
            )
            (root / "papers" / PAPER / str(bundle["receipt_path"])).write_bytes(
                bytes(bundle["receipt_bytes"])
            )
            (root / "papers" / PAPER / str(bundle["authority_path"])).write_bytes(
                bytes(bundle["authority_bytes"])
            )
            (root / "papers" / PAPER / str(bundle["carrier_compressed_path"])).write_bytes(
                bytes(bundle["carrier_compressed_bytes"])
            )
            (audit / "current_source_record_audit.json").write_bytes(
                FIXTURE_SOURCE_RECORD_AUDIT_BYTES
            )
            stdout = io.StringIO()

            with (
                mock.patch.object(REISSUE, "ROOT", root),
                mock.patch.object(
                    REISSUE, "current_statement_receipt_surface", return_value=surface
                ),
                mock.patch.object(
                    REISSUE,
                    "_historical_manifest_replay_cli_recipe_verifier",
                    return_value=verified_historical_recipe,
                ) as recipe_verifier_factory,
                mock.patch.object(
                    REISSUE,
                    "_validated_current_source_record_closure_authority",
                    side_effect=fixture_source_record_authority,
                ),
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "statement_receipt_reissue.py",
                        "--root",
                        str(root),
                        "--paper",
                        PAPER,
                        "--plan",
                        "audit/plan.json",
                        "--out",
                        "audit/statement_match_llm.json",
                        "--archive",
                        "audit/prior.json",
                        "--historical-manifest-replay",
                        "audit/historical_statement_manifest_replay.json",
                        "--historical-manifest-store-recovery-receipt",
                        str(bundle["receipt_path"]),
                        "--historical-manifest-store-recovery-authority",
                        str(bundle["authority_path"]),
                        "--historical-manifest-store-recovery-carrier",
                        str(bundle["carrier_compressed_path"]),
                        "--historical-source-record-audit",
                        "audit/current_source_record_audit.json",
                    ],
                ),
                redirect_stdout(stdout),
            ):
                self.assertEqual(REISSUE.main(), 0)

            self.assertIn("1 historically transported", stdout.getvalue())
            recipe_verifier_factory.assert_called_once()

    def test_fresh_body_transport_pins_are_rebound_from_current_target(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar()
        body = fresh_body()
        body["paper_statement_sha256"] = "f" * 64
        plan = base_plan(
            surface,
            prior,
            [{"action": "fresh", "target": target.descriptor(), "body": body}],
        )

        result = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)
        entry = next(iter(result.sidecar["items"].values()))
        self.assertEqual(entry["paper_statement_sha256"], target.paper_statement_sha256)
        self.assertNotEqual(entry["paper_statement_sha256"], "f" * 64)

    def test_direct_expression_review_is_versioned_per_receipt_surface(self) -> None:
        target = make_target()
        legacy_surface = make_surface(target, source_kind="formula")
        prior = prior_sidecar()
        legacy_plan = base_plan(
            legacy_surface,
            prior,
            [{"action": "fresh", "target": target.descriptor(), "body": fresh_body()}],
        )
        self.assertEqual(
            REISSUE.materialize_statement_receipt_reissue(
                legacy_surface, prior, legacy_plan
            ).report["fresh_target_count"],
            1,
        )

        v1_surface = copy.deepcopy(legacy_surface)
        v1_surface.direct_expression_semantics_review = True
        v1_plan = base_plan(
            v1_surface,
            prior,
            [{"action": "fresh", "target": target.descriptor(), "body": fresh_body()}],
        )
        with self.assertRaisesRegex(
            REISSUE.StatementReceiptReissueError, "source-expression route lacks"
        ):
            REISSUE.materialize_statement_receipt_reissue(
                v1_surface, prior, v1_plan
            )

    def test_reuse_rejects_changed_current_source_route(self) -> None:
        target = make_target()
        old_surface = make_surface(target, source_key="old_source")
        old_entry = generated_entry(
            target, body=fresh_body(source_key="old_source")
        )
        prior = prior_sidecar(old_entry)
        old_digest = next(iter(prior.groups))
        new_surface = make_surface(target, source_key="new_source")
        plan = base_plan(
            new_surface,
            prior,
            [
                {
                    "action": "reuse",
                    "target": target.descriptor(),
                    "prior_entry_payload_sha256": old_digest,
                }
            ],
        )

        # The exact target triple is unchanged, but an old source route is not
        # evidence for the current source map.
        with self.assertRaisesRegex(REISSUE.StatementReceiptReissueError, "source-route"):
            REISSUE.materialize_statement_receipt_reissue(new_surface, prior, plan)
        self.assertNotEqual(old_surface.source_route_inventory, new_surface.source_route_inventory)

    def test_reuse_accepts_exact_current_receipt_with_root_prompt_metadata(self) -> None:
        target = make_target()
        surface = make_surface(target)
        entry = generated_entry(target)
        # v10 permits the sidecar-level prompt field, and many existing
        # receipts use that form. Reuse must validate it without rewriting it.
        entry.pop("prompt_version")
        prior = prior_sidecar(entry)
        old_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "reuse",
                    "target": target.descriptor(),
                    "prior_entry_payload_sha256": old_digest,
                }
            ],
        )

        result = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)
        self.assertEqual(result.report["reused_target_count"], 1)
        reused = next(iter(result.sidecar["items"].values()))
        self.assertNotIn("prompt_version", reused)

    def test_reuse_requires_exact_current_identity(self) -> None:
        target = make_target()
        changed_target = make_target(translation="P x after translation repair")
        surface = make_surface(changed_target)
        prior = prior_sidecar(generated_entry(target))
        old_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "reuse",
                    "target": changed_target.descriptor(),
                    "prior_entry_payload_sha256": old_digest,
                }
            ],
        )

        with self.assertRaisesRegex(REISSUE.StatementReceiptReissueError, "differs"):
            REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

    def test_retire_requires_semantic_antijoin_against_current_class(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar(generated_entry(target))
        old_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "retire",
                    "prior_entry_payload_sha256": old_digest,
                    "reason": (
                        "The old receipt is no longer reachable from any current source or Lean "
                        "semantic class after the reviewed source-map replacement."
                    ),
                }
            ],
        )

        with self.assertRaisesRegex(REISSUE.StatementReceiptReissueError, "semantic anti-join"):
            REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

    def test_orphan_can_retire_only_with_sha_pinned_action_and_full_current_plan(self) -> None:
        target = make_target(translation="current P x")
        surface = make_surface(target)
        orphan_target = make_target(translation="orphan P x")
        prior = prior_sidecar(generated_entry(orphan_target))
        orphan_digest = next(iter(prior.groups))
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "fresh",
                    "target": target.descriptor(),
                    "body": fresh_body(),
                },
                {
                    "action": "retire",
                    "prior_entry_payload_sha256": orphan_digest,
                    "reason": (
                        "The prior Lean signature plus translated proposition class does not occur "
                        "anywhere in the current cache, so it is a verified orphan rather than a rekey."
                    ),
                },
            ],
        )

        result = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)
        self.assertEqual(result.report["retired_prior_payload_group_count"], 1)

    def test_contextual_model_route_cannot_certify_fresh_match(self) -> None:
        target = make_target()
        surface = make_surface(target, source_kind="model", source_key="source_model")
        prior = prior_sidecar()
        plan = base_plan(
            surface,
            prior,
            [
                {
                    "action": "fresh",
                    "target": target.descriptor(),
                    "body": fresh_body(
                        source_key="source_model",
                        route_kind="source_model_convention",
                        relation="shared_model_convention",
                    ),
                }
            ],
        )

        with self.assertRaisesRegex(
            REISSUE.StatementReceiptReissueError,
            "semantic target is not|equivalence-bearing",
        ):
            REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

    def test_stale_surface_pin_and_duplicate_target_actions_fail_before_write(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar()
        action = {"action": "fresh", "target": target.descriptor(), "body": fresh_body()}
        plan = base_plan(surface, prior, [copy.deepcopy(action), copy.deepcopy(action)])
        plan["current_inputs"]["cache_sha256"] = "f" * 64

        with self.assertRaisesRegex(REISSUE.StatementReceiptReissueError, "stale `cache_sha256`"):
            REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

        plan["current_inputs"] = surface.input_pins()
        with self.assertRaisesRegex(REISSUE.StatementReceiptReissueError, "duplicates"):
            REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)

    def test_materialization_is_dry_until_atomic_writer_is_called(self) -> None:
        target = make_target()
        surface = make_surface(target)
        prior = prior_sidecar()
        plan = base_plan(
            surface,
            prior,
            [{"action": "fresh", "target": target.descriptor(), "body": fresh_body()}],
        )
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "audit" / "statement_match_llm.json"
            result = REISSUE.materialize_statement_receipt_reissue(surface, prior, plan)
            self.assertFalse(output.exists())
            REISSUE._atomic_write(output, REISSUE._json_bytes(result.sidecar))
            self.assertEqual(json.loads(output.read_text(encoding="utf-8")), result.sidecar)


if __name__ == "__main__":
    unittest.main()
