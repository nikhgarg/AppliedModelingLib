#!/usr/bin/env python3
"""Explicit lazy boundary for the historical raw source-record protocol.

The current-v11 transaction must not import this module.  Historical receipt
validation loads it on first use and receives the same canonical authorities
that the former eager imports exposed.  This is an import/reachability boundary,
not a compatibility or alternative acceptance lane.
"""

from __future__ import annotations

from scripts.source_record_archived_transports import (
    archived_source_record_transport_artifacts,
    archived_source_record_transport_item_field,
)
from scripts.source_record_auxiliary_routing_supplement import (
    ValidatedAuxiliaryRoutingContext,
    current_auxiliary_routing_context,
)
from scripts.source_record_freshness import source_record_item_judgment_current
from scripts.source_record_integrity import (
    canonical_digest_payload,
    reusable_item_metadata_error,
    source_record_audit_receipt_error,
    source_record_audit_surface_view,
    source_record_item_reuse_eligible,
    source_record_raw_reusable_item_metadata_error,
    source_record_target_route_error,
)
from scripts.source_record_obligation_groups import raw_source_record_obligation_groups
from scripts.source_record_overlay_protocol import (
    serialized_source_record_overlay_labels,
    source_record_overlay_labels_with_artifacts,
)
from scripts.source_record_producer_provenance import (
    fingerprint_without_raw_producer_provenance,
)
from scripts.source_record_projection_contract import (
    checked_projection_result,
    semantic_model_subanalysis_errors,
    source_record_classification,
)
from scripts.source_record_semantic_reuse import (
    load_current_semantic_reuse_authority,
    semantic_fingerprint_matches,
)
from scripts.source_record_target_disposition import (
    approved_source_convention_antecedent_errors,
    load_administrative_projection_rebind_context,
    model_convention_semantic_digest,
    project_source_record_response_association_pins,
    recursive_field_target_disposition_errors,
    semantic_association_record_digest,
    semantic_target_disposition_errors,
    source_contract_association_record_digest,
    source_input_target_disposition_errors,
)


__all__ = (
    "ValidatedAuxiliaryRoutingContext",
    "approved_source_convention_antecedent_errors",
    "archived_source_record_transport_artifacts",
    "archived_source_record_transport_item_field",
    "canonical_digest_payload",
    "checked_projection_result",
    "current_auxiliary_routing_context",
    "fingerprint_without_raw_producer_provenance",
    "load_administrative_projection_rebind_context",
    "load_current_semantic_reuse_authority",
    "model_convention_semantic_digest",
    "project_source_record_response_association_pins",
    "raw_source_record_obligation_groups",
    "recursive_field_target_disposition_errors",
    "reusable_item_metadata_error",
    "semantic_association_record_digest",
    "semantic_fingerprint_matches",
    "semantic_model_subanalysis_errors",
    "semantic_target_disposition_errors",
    "serialized_source_record_overlay_labels",
    "source_contract_association_record_digest",
    "source_input_target_disposition_errors",
    "source_record_audit_receipt_error",
    "source_record_audit_surface_view",
    "source_record_classification",
    "source_record_item_judgment_current",
    "source_record_item_reuse_eligible",
    "source_record_overlay_labels_with_artifacts",
    "source_record_raw_reusable_item_metadata_error",
    "source_record_target_route_error",
)
