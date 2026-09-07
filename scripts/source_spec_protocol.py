"""Historical adapter for selecting raw-source-to-expanded-Spec review.

Current closeout imports ``current_closeout.protocol_selection`` directly and
never consults the historical trust ledger.  This adapter remains for legacy
diagnostics and presentation readers that must interpret papers created before
the explicit graph-native switch.  It performs no Lean elaboration, semantic
judgment, or evidence validation.
"""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path

try:
    from scripts.current_closeout.protocol_selection import (
        current_v11_protocol_selected,
    )
    from scripts.theorem_realization_transition import (
        theorem_realization_reissue_requirement,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script execution.
    from current_closeout.protocol_selection import current_v11_protocol_selected
    from theorem_realization_transition import theorem_realization_reissue_requirement


ROOT = Path(__file__).resolve().parents[1]


def source_spec_correspondence_requested(
    status_payload: object,
    source_map_payload: object | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Return whether the paper selects the strict source-to-Spec protocol.

    Explicit status/map spellings take precedence.  New closeout papers absent
    from the trusted legacy-v10 baseline enter the protocol automatically.  A
    failure to evaluate that automatic boundary fails closed by selecting the
    stricter lane; an isolated test tree without the repository baseline keeps
    explicit-switch semantics.
    """

    if current_v11_protocol_selected(status_payload, source_map_payload):
        return True
    if not isinstance(status_payload, Mapping) or folder is None:
        return False
    try:
        folder.resolve().relative_to((ROOT / "papers").resolve())
    except ValueError:
        return False
    try:
        return theorem_realization_reissue_requirement(
            ROOT, folder, status_payload
        ).required
    except (OSError, RuntimeError, TypeError, ValueError):
        return True


def raw_source_spec_screening_requested(
    status_payload: object,
    source_map_payload: object | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Alias the single effective protocol-selection decision."""

    return source_spec_correspondence_requested(
        status_payload,
        source_map_payload,
        folder=folder,
    )
