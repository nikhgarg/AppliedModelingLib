#!/usr/bin/env python3
"""Separate status configuration from generated paper-display metadata."""

from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any, Mapping

if __package__ in {None, ""}:  # Import the trusted current-closeout package.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.current_closeout.protocol_selection import current_v11_protocol_selected

try:
    from scripts.obligation_routes import EvidenceRouteSet, ObligationRouteError
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from obligation_routes import EvidenceRouteSet, ObligationRouteError


NON_ACCEPTANCE_STATUS_FIELDS = frozenset({"paper_interface", "human_review"})
STATUS_ASSURANCE_CONTROL_SCHEMA = 1


class CloseoutStatusProjectionError(ValueError):
    """Paper status cannot be projected or refreshed safely."""


def _load_status(root: Path, paper: str) -> tuple[Path, dict[str, Any]]:
    path = root / "papers" / paper / "status.json"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CloseoutStatusProjectionError(
            f"could not read paper status for {paper}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise CloseoutStatusProjectionError(
            f"paper status for {paper} is not an object"
        )
    if payload.get("id") != paper:
        raise CloseoutStatusProjectionError(
            f"paper status for {paper} belongs to another paper"
        )
    return path, payload


def paper_status_acceptance_projection(
    root: Path,
    paper: str,
) -> dict[str, Any]:
    """Return status configuration with derived interface counts removed.

    The projection is conservative: every status field remains bound except
    the generated ``paper_interface`` display object and optional human-review
    annotations, which are not release authority. Review-surface membership,
    status, build command, source configuration, caveats, and every other
    policy field therefore remain frozen inputs.
    """

    _path, payload = _load_status(root.resolve(), paper)
    projection = {
        str(key): value
        for key, value in payload.items()
        if str(key) not in NON_ACCEPTANCE_STATUS_FIELDS
    }
    return {
        "schema": 1,
        "paper": paper,
        "status": projection,
    }


def paper_status_assurance_control_projection(
    *,
    paper: str,
    formalization_status: object,
    assumption_policy: object,
) -> dict[str, Any]:
    """Return the status controls that can invalidate terminal assurance.

    Reader prose, repository visibility, generated counts, and other display
    metadata are deliberately outside this projection.  The formalization
    status and the review surface's assumption policy remain acceptance
    controls because changing either changes the claim made by closeout.
    """

    paper_id = str(paper or "").strip()
    status = str(formalization_status or "").strip()
    policy = str(assumption_policy or "").strip()
    if not paper_id:
        raise CloseoutStatusProjectionError(
            "status assurance control has no paper"
        )
    if not status:
        raise CloseoutStatusProjectionError(
            f"paper status for {paper_id} has no formalization status"
        )
    return {
        "schema": STATUS_ASSURANCE_CONTROL_SCHEMA,
        "paper": paper_id,
        "formalization_status": status,
        "assumption_policy": policy,
    }


def paper_status_assurance_control_projection_from_payload(
    paper: str,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    """Project terminal status controls from one already loaded status file."""

    if payload.get("id") != paper:
        raise CloseoutStatusProjectionError(
            f"paper status for {paper} belongs to another paper"
        )
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, Mapping):
        raise CloseoutStatusProjectionError(
            f"paper status for {paper} has no review_surface object"
        )
    return paper_status_assurance_control_projection(
        paper=paper,
        formalization_status=payload.get("status"),
        assumption_policy=review_surface.get("assumption_policy"),
    )


def paper_status_assurance_control_projection_from_repository(
    root: Path,
    paper: str,
) -> dict[str, Any]:
    """Load and project the two terminally material paper-status controls."""

    _path, payload = _load_status(root.resolve(), paper)
    return paper_status_assurance_control_projection_from_payload(paper, payload)


def _atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    data = json.dumps(payload, indent=2, ensure_ascii=False).encode("utf-8") + b"\n"
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_temp = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temp_path = Path(raw_temp)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp_path, path)
    finally:
        if temp_path.exists():
            temp_path.unlink()


def graph_native_human_review_total_from_payload(
    source_map: object,
    status_payload: Mapping[str, Any],
) -> int | None:
    """Return the typed graph-native human-review denominator, when selected."""

    raw_surface = status_payload.get("review_surface")
    if not current_v11_protocol_selected(status_payload, source_map):
        return None
    if not isinstance(raw_surface, Mapping):
        raise CloseoutStatusProjectionError(
            "graph-native review_surface is malformed"
        )
    raw_include = raw_surface.get("include_names")
    raw_conditions = raw_surface.get("source_condition_items", [])
    if not isinstance(raw_include, list) or not all(
        isinstance(name, str) for name in raw_include
    ):
        raise CloseoutStatusProjectionError(
            "graph-native review_surface.include_names is malformed"
        )
    if not isinstance(raw_conditions, list) or not all(
        isinstance(item, str) for item in raw_conditions
    ):
        raise CloseoutStatusProjectionError(
            "graph-native review_surface.source_condition_items is malformed"
        )
    try:
        selected = EvidenceRouteSet.from_source_map(
            source_map
        ).human_review_source_items(
            tuple(raw_include),
            tuple(raw_conditions),
        )
    except ObligationRouteError as exc:
        raise CloseoutStatusProjectionError(str(exc)) from exc
    return len(selected)


def graph_native_human_review_total(
    root: Path,
    paper: str,
    status_payload: Mapping[str, Any],
) -> int | None:
    """Load the typed source ledger and derive its human-review denominator."""

    source_map_path = root / "papers" / paper / "audit" / "paper_statement_map.json"
    try:
        source_map = json.loads(source_map_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        if current_v11_protocol_selected(status_payload):
            raise CloseoutStatusProjectionError(
                f"could not read graph-native statement map for {paper}: {exc}"
            ) from exc
        return None
    return graph_native_human_review_total_from_payload(source_map, status_payload)


def refresh_derived_paper_status_metadata(root: Path, paper: str) -> bool:
    """Refresh only graph-derived or syntax-neutral paper display counts.

    Historical ``declaration_rows`` values are left untouched. They have no
    acceptance role and cannot be recomputed by lexing Lean; a future status
    schema may remove the misleading field or project it from a typed accepted
    graph when a human-facing use actually requires it.
    """

    root = root.resolve()
    status_path, payload = _load_status(root, paper)
    interface_path = root / "papers" / paper / "PaperInterface.lean"
    try:
        interface_text = interface_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise CloseoutStatusProjectionError(
            f"could not read PaperInterface.lean for {paper}: {exc}"
        ) from exc
    raw_interface = payload.get("paper_interface")
    if not isinstance(raw_interface, dict):
        raise CloseoutStatusProjectionError(
            f"paper status for {paper} has no paper_interface object"
        )
    raw_surface = payload.get("review_surface")
    if not isinstance(raw_surface, Mapping):
        raise CloseoutStatusProjectionError(
            f"paper status for {paper} has no review_surface object"
        )
    raw_include = raw_surface.get("include_names")
    if not isinstance(raw_include, list) or not all(
        isinstance(name, str) and name.strip() for name in raw_include
    ):
        raise CloseoutStatusProjectionError(
            f"paper status for {paper} has malformed review_surface.include_names"
        )
    derived = {
        "line_count": len(interface_text.splitlines()),
        "review_rows": len(set(name.strip() for name in raw_include)),
    }
    human_total = graph_native_human_review_total(root, paper, payload)
    raw_human_review = payload.get("human_review")
    human_total_current = human_total is None or not isinstance(
        raw_human_review, Mapping
    ) or (
        raw_human_review.get("total_rows") == human_total
    )
    if (
        all(raw_interface.get(key) == value for key, value in derived.items())
        and human_total_current
    ):
        return False
    updated = dict(payload)
    updated_interface = dict(raw_interface)
    updated_interface.update(derived)
    updated["paper_interface"] = updated_interface
    if isinstance(raw_human_review, Mapping) and human_total is not None:
        updated_human_review = dict(raw_human_review)
        updated_human_review["total_rows"] = human_total
        updated["human_review"] = updated_human_review
    if paper_status_acceptance_projection_from_payload(paper, payload) != (
        paper_status_acceptance_projection_from_payload(paper, updated)
    ):
        raise CloseoutStatusProjectionError(
            "derived metadata refresh changed the status acceptance projection"
        )
    _atomic_write_json(status_path, updated)
    return True


def paper_status_acceptance_projection_from_payload(
    paper: str,
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    """Pure payload variant used to prove a derived refresh is neutral."""

    projection = {
        str(key): value
        for key, value in payload.items()
        if str(key) not in NON_ACCEPTANCE_STATUS_FIELDS
    }
    return {"schema": 1, "paper": paper, "status": projection}
