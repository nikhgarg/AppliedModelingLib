#!/usr/bin/env python3
"""Synchronize aggregate status from paper-local, read-only sidecar evidence.

Default sync and check never build Lean modules or elaborate declarations.
Only an explicit ``--dashboard-audit`` may use the live dashboard audit path.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import quote


_ROOT_PARSER = argparse.ArgumentParser(add_help=False)
_ROOT_PARSER.add_argument("--repo", type=Path)
_ROOT_ARGS, _ROOT_UNKNOWN = _ROOT_PARSER.parse_known_args(sys.argv[1:])
ROOT = (
    _ROOT_ARGS.repo.resolve()
    if _ROOT_ARGS.repo is not None
    else Path(
        os.environ.get("APPLIEDMODELINGLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
    ).resolve()
)
# Cross-checkout release validation executes this trusted private script while
# reading a clean public candidate. Propagate that explicit repository context
# to every trusted helper imported below or lazily during status rendering.
os.environ["APPLIEDMODELINGLIB_REPO_ROOT"] = str(ROOT)

if __package__ in {None, ""}:  # Import the trusted current-closeout package.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.current_closeout.protocol_selection import current_v11_protocol_selected
from scripts.final_validation_report_status import public_display_status

try:
    from root_readme_policy import (
        assert_no_root_readme_outputs,
        assert_root_readme_locked,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports
    from scripts.root_readme_policy import (
        assert_no_root_readme_outputs,
        assert_root_readme_locked,
    )
try:
    from formalization_protocol import (
        IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
        load_formalization_protocol,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports
    from scripts.formalization_protocol import (
        IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
        load_formalization_protocol,
    )
try:
    from theorem_realization_transition import (
        CLOSEOUT_STATUSES,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports
    from scripts.theorem_realization_transition import (
        CLOSEOUT_STATUSES,
    )
try:
    from paper_path_resolution import resolve_paper_folder
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports
    from scripts.paper_path_resolution import resolve_paper_folder
try:
    from legacy_v10_trust_ledger import evaluate_saved_status_reuse
    from saved_status_reuse import (
        SAVED_STATUS_REUSE_RECEIPT_SCHEMA,
        WorktreeImportClosureProvider,
        coverage_disposition,
        statement_disposition,
        validated_coverage_source_bindings,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports
    from scripts.legacy_v10_trust_ledger import evaluate_saved_status_reuse
    from scripts.saved_status_reuse import (
        SAVED_STATUS_REUSE_RECEIPT_SCHEMA,
        WorktreeImportClosureProvider,
        coverage_disposition,
        statement_disposition,
        validated_coverage_source_bindings,
    )
PAPERS = ROOT / "papers"
AGGREGATE_STATUS = PAPERS / "status.json"
HUMAN_STATUS = PAPERS / "human_status.json"
DOCS_PAPER_STATUS = ROOT / "docs" / "PAPER_STATUS.md"
SITE_INDEX = ROOT / "site" / "index.html"
TEMPLATE = PAPERS / "TEMPLATE"
SITE_LIBRARY_BEGIN = "<!-- BEGIN GENERATED LIBRARY COMPONENT ROWS -->"
SITE_LIBRARY_END = "<!-- END GENERATED LIBRARY COMPONENT ROWS -->"
SITE_STATS_BEGIN = "<!-- BEGIN GENERATED PROJECT STATS -->"
SITE_STATS_END = "<!-- END GENERATED PROJECT STATS -->"
SITE_STATUS_BEGIN = "<!-- BEGIN GENERATED PAPER STATUS ROWS -->"
SITE_STATUS_END = "<!-- END GENERATED PAPER STATUS ROWS -->"
SITE_REQUIRED_STATIC_COPY = {
    "maintainer footer": "Applied Modeling Lib is maintained by",
    "project former name": "This project was previously called EconCSLib.",
    "companion paper link": "https://arxiv.org/abs/2606.16144",
    "companion Lean project link": "https://github.com/gametheoryinlean/EconCSLib",
    "hero vision line": "Our vision is to enable researchers who don't know Lean",
}
PAPER_README_BEGIN = "<!-- BEGIN GENERATED PAPER FOLDER README -->"
PAPER_README_END = "<!-- END GENERATED PAPER FOLDER README -->"
LEGACY_README_NOTES = "docs/FORMALIZATION_NOTES.md"
TEMPLATE_README_PLAN = "docs/FORMALIZATION_PLAN.md"
GITHUB_MAIN = "https://github.com/nikhgarg/EconCSLib/blob/main/"
GITHUB_MAIN_TREE = "https://github.com/nikhgarg/EconCSLib/tree/main/"
# The public site links its generated artifacts to the published repository.
# The localhost preview server exposes the same repo-relative files under this
# neutral route, and the small static rewrite below selects it only when the
# page is actually being viewed on localhost.
LOCAL_ARTIFACT_PREFIX = "/artifacts/"
PAPER_FACING_HUMAN_REVIEW_SURFACE = "paper_facing_excluding_deep_audit_v1"
NORMAL_SOURCE_PRESENTATIONS_HUMAN_REVIEW_SURFACE = (
    "normal_source_presentations_v1"
)
SOURCE_CLAIMS_HUMAN_REVIEW_SURFACE = "source_claims_v1"
CATALOG = PAPERS / "catalog.json"
PUBLIC_SOURCE_DISPLAY_PROJECTION_MARKER = "publication_source_display_projection"
PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA = 1
PUBLIC_SOURCE_DISPLAY_MANIFEST = "audit/public_source_display_projection.json"
SHA256_HEX_RE = re.compile(r"[0-9a-f]{64}")

STATUS_LABELS = {
    "formalized": "Formalized",
    "formalized with caveat": "Formalized with caveat",
    "partially formalized": "Partially formalized",
    "conditional": "Partially formalized",
    "paper draft": "Paper draft",
    "scaffold": "Scaffold",
    "not started": "Not started",
    "not formalized": "Not formalized",
}

STATUS_GROUPS = {
    "formalized": 0,
    "formalized with caveat": 0,
    "partially formalized": 1,
    "conditional": 1,
    "paper draft": 2,
}
REPOSITORY_VISIBILITIES = frozenset({"public", "private_only"})
NAME_ONLY_SOURCE_COVERAGE_REASON_RE = re.compile(
    r"exactly matches current dashboard row name|"
    r"exact source-key|"
    r"\bname[-_ ]?match(?:ed|es|ing)?\b|"
    r"\bmatched by name\b",
    re.I,
)


def load_catalog() -> dict[str, Any]:
    if not CATALOG.exists():
        return {}
    payload = json.loads(CATALOG.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{CATALOG.relative_to(ROOT)} should contain a JSON object")
    if payload.get("schema") != 1:
        raise ValueError(f"{CATALOG.relative_to(ROOT)} should use schema 1")
    return payload


def publication_overrides(catalog: dict[str, Any]) -> dict[str, tuple[str, int]]:
    raw = catalog.get("publication_overrides", {})
    if not isinstance(raw, dict):
        raise ValueError("publication_overrides should be an object")
    out: dict[str, tuple[str, int]] = {}
    for paper_id, value in raw.items():
        if not isinstance(value, dict):
            continue
        publication = value.get("publication")
        year = value.get("year")
        if isinstance(publication, str) and isinstance(year, int):
            out[str(paper_id)] = (publication, year)
    return out


def string_map(catalog: dict[str, Any], key: str) -> dict[str, str]:
    raw = catalog.get(key, {})
    if not isinstance(raw, dict):
        raise ValueError(f"{key} should be an object")
    return {
        str(name): value.strip()
        for name, value in raw.items()
        if isinstance(value, str) and value.strip()
    }


def library_components(catalog: dict[str, Any]) -> list[dict[str, Any]]:
    raw = catalog.get("library_components", [])
    if not isinstance(raw, list):
        raise ValueError("library_components should be a list")
    components: list[dict[str, Any]] = []
    for item in raw:
        if not isinstance(item, dict):
            continue
        title = item.get("title")
        examples = item.get("examples")
        raw_paths = item.get("paths", [])
        if not isinstance(title, str) or not isinstance(examples, str):
            continue
        if not isinstance(raw_paths, list):
            continue
        paths = [str(path) for path in raw_paths if str(path).strip()]
        components.append(
            {
                "title": title.strip(),
                "paths": paths,
                "examples": " ".join(examples.split()),
            }
        )
    return components


CATALOG_PAYLOAD = load_catalog()
PUBLICATION_OVERRIDES = publication_overrides(CATALOG_PAYLOAD)
SOURCE_URL_OVERRIDES = string_map(CATALOG_PAYLOAD, "source_url_overrides")
README_TITLE_OVERRIDES = string_map(CATALOG_PAYLOAD, "readme_title_overrides")
LIBRARY_COMPONENTS = library_components(CATALOG_PAYLOAD)


def note_citation(payload: dict[str, Any]) -> dict[str, str] | None:
    raw = payload.get("human_summary_citation")
    if not isinstance(raw, dict):
        return None
    label = raw.get("label")
    url = raw.get("url")
    if not isinstance(label, str) or not isinstance(url, str):
        return None
    label = label.strip()
    url = url.strip()
    if not label or not url:
        return None
    return {"label": label, "url": url}


def all_paper_dirs() -> list[Path]:
    return sorted(
        folder
        for folder in PAPERS.iterdir()
        if folder.is_dir()
        and folder.name != TEMPLATE.name
        and (folder / "status.json").exists()
    )


def tracked_paper_dirs() -> list[Path]:
    """Return paper folders whose status files are tracked in git.

    Defaulting to tracked files keeps local draft paper scaffolds from changing
    generated aggregate status files and matches CI behavior in a clean checkout.
    """

    try:
        result = subprocess.run(
            ["git", "ls-files", "--", "papers/*/status.json"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return all_paper_dirs()

    folders: set[Path] = set()
    for raw in result.stdout.splitlines():
        path = (ROOT / raw.strip()).resolve()
        if (
            path.name == "status.json"
            and path.exists()
            and path.parent.parent == PAPERS
        ):
            if path.parent.name != TEMPLATE.name:
                folders.add(path.parent)
    if not folders:
        return all_paper_dirs()
    return sorted(folders)


def paper_dirs(*, include_untracked: bool = False) -> list[Path]:
    if include_untracked:
        return all_paper_dirs()
    return tracked_paper_dirs()


def load_paper_status(folder: Path) -> dict[str, Any]:
    path = folder / "status.json"
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path} should contain a JSON object")
    if payload.get("schema") != 1:
        raise ValueError(f"{path} should use schema 1")
    if payload.get("id") != folder.name:
        raise ValueError(f"{path} id should be {folder.name!r}")
    return payload


def paper_records(
    *, include_untracked: bool = False
) -> list[tuple[Path, dict[str, Any]]]:
    return [
        (folder, load_paper_status(folder))
        for folder in paper_dirs(include_untracked=include_untracked)
    ]


def repository_visibility(payload: dict[str, Any]) -> str:
    """Return the explicit public-export visibility for one paper record.

    A private-only formalization remains in the aggregate private status index
    but must not appear in public dashboard artifacts.  Absence fails closed:
    academic publication metadata is not repository-export authorization.
    """

    paper_id = str(payload.get("id", "<unknown>"))
    if "repository_visibility" not in payload:
        raise ValueError(
            f"{paper_id}: missing explicit repository_visibility; expected "
            "`public` or `private_only`"
        )
    raw = payload.get("repository_visibility")
    visibility = str(raw).strip().lower()
    if visibility not in REPOSITORY_VISIBILITIES:
        expected = ", ".join(sorted(REPOSITORY_VISIBILITIES))
        raise ValueError(
            f"{paper_id}: repository_visibility must be one of {expected}, got {raw!r}"
        )
    return visibility


def public_dashboard_records(
    records: list[tuple[Path, dict[str, Any]]],
) -> list[tuple[Path, dict[str, Any]]]:
    """Keep only paper records explicitly eligible for public dashboard export."""

    return [
        (folder, payload)
        for folder, payload in records
        if repository_visibility(payload) == "public"
    ]


def aggregate_payload(records: list[tuple[Path, dict[str, Any]]]) -> dict[str, Any]:
    papers = [payload for _folder, payload in records]
    return {
        "schema": 1,
        "description": (
            "Aggregate index generated from papers/<PaperName>/status.json. "
            "Paper-local status files are the source of truth for status, "
            "human summaries, review rows, and PaperInterface metadata."
        ),
        "review_count_policy": (
            "reviewed_rows counts saved human dashboard rows tracked in the public repository. "
            "total_rows counts the configured human source-claim surface; a paired transparent "
            "Spec and proof theorem count once, while the raw declaration surface remains machine-audit metadata. "
            "Agent source audits are not counted as human review."
        ),
        "paper_interface_maintenance_policy": (
            "PaperInterface.lean is the required row-level review surface for every paper. "
            "Keep implementation details and broad proof aliases behind imported modules such as "
            "AuditInterface.lean or implementation files only when PaperInterface.lean still "
            "contains the audited paper-facing statements themselves. Large PaperInterface.lean "
            "surfaces must be marked oversized and sliced for review, not routed through "
            "paper_interface.audit_surface_path, which is obsolete."
        ),
        "papers": papers,
    }


def status_label(status: str) -> str:
    return STATUS_LABELS.get(status, status.capitalize())


def human_status_label(status: str, *, paper_id: str | None = None) -> str:
    """Display checked coverage without changing the paper's audit disposition."""
    return status_label(public_display_status(
        status,
        paper_id=paper_id,
        preserve_partial_status=CATALOG_PAYLOAD.get("preserve_partial_status", []),
    ))


def publication_for(payload: dict[str, Any]) -> tuple[str, int]:
    publication = PUBLICATION_OVERRIDES.get(payload["id"])
    if publication is not None:
        return publication
    # Source-version strings are audit provenance, not public citations: they
    # may contain private filenames, revision IDs, or hashes. Missing display
    # metadata must not expose those fields or invent a venue/date.
    return "Publication details not listed", 9999


def source_url_for(payload: dict[str, Any]) -> str:
    # Only the curated public citation catalog owns website paper links.
    # An intake/source URL can instead identify a private draft or workspace.
    return SOURCE_URL_OVERRIDES.get(payload["id"], "")


def validated_human_review_counts(
    payload: dict[str, Any],
    *,
    expected_total: int | None = None,
) -> dict[str, int]:
    """Validate administrative human counts against semantic receipt totals."""

    raw = payload.get("human_review")
    if raw is None:
        raw = {}
    if not isinstance(raw, dict):
        raise ValueError(
            f"{payload.get('id', 'paper')}: human_review must be an object"
        )
    fields = (
        "reviewed_rows",
        "total_rows",
        "stale_rows",
        "mismatch_rows",
        "uncertain_rows",
    )
    counts: dict[str, int] = {}
    for field in fields:
        value = raw.get(field, 0)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError(
                f"{payload.get('id', 'paper')}: human_review.{field} "
                "must be a nonnegative integer"
            )
        counts[field] = value
    total = counts["total_rows"]
    for field in fields:
        if field != "total_rows" and counts[field] > total:
            raise ValueError(
                f"{payload.get('id', 'paper')}: human_review.{field} "
                "cannot exceed total_rows"
            )
    if expected_total is not None and total != expected_total:
        raise ValueError(
            f"{payload.get('id', 'paper')}: human_review.total_rows={total} "
            f"disagrees with saved semantic review total {expected_total}"
        )
    return counts


def human_review_label(
    payload: dict[str, Any], *, counts: dict[str, int] | None = None
) -> str:
    review = counts or validated_human_review_counts(payload)
    return f"{review['reviewed_rows']}/{review['total_rows']}"


def human_translation_label(
    payload: dict[str, Any], *, counts: dict[str, int] | None = None
) -> str:
    review = counts or validated_human_review_counts(payload)
    reviewed = review["reviewed_rows"]
    total = review["total_rows"]
    stale = review["stale_rows"]
    mismatch = review["mismatch_rows"]
    uncertain = review["uncertain_rows"]
    parts = [f"{reviewed}/{total} reviewed"]
    if mismatch:
        parts.append(f"{mismatch} mismatch")
    if uncertain:
        parts.append(f"{uncertain} uncertain")
    if stale:
        parts.append(f"{stale} needs refresh")
    return "; ".join(parts)


def source_map_deep_only_review_rows(folder: Path, payload: dict[str, Any]) -> set[str]:
    """Return configured review rows that map exclusively to deep audit items.

    The source map, rather than declaration spelling, decides whether a row is
    audit-only.  A row attached to any normal source item remains on the human
    paper-review surface; an explicit human-review override may retain a
    deep-only row when it is deliberately part of that paper's review plan.
    """

    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return set()
    raw_names = review_surface.get("include_names")
    if not isinstance(raw_names, list):
        return set()
    configured_names = {str(name).strip() for name in raw_names if str(name).strip()}
    if not configured_names:
        return set()

    source_map = load_json_object(folder / "audit" / "paper_statement_map.json")
    items = source_map.get("items")
    if not isinstance(items, dict):
        return set()

    def is_deep_item(item: object) -> bool:
        if not isinstance(item, dict):
            return False
        inventory_role = str(item.get("inventory_role") or "").strip().lower()
        coverage_status = str(item.get("coverage_status") or "").strip().lower()
        return "deep" in inventory_role or coverage_status == "deep_audit_material"

    row_scopes: dict[str, set[bool]] = {}

    def record(row: object, *, deep: bool) -> None:
        name = str(row).strip()
        if name in configured_names:
            row_scopes.setdefault(name, set()).add(deep)

    for item in items.values():
        if not isinstance(item, dict):
            continue
        deep = is_deep_item(item)
        declarations = item.get("lean_declarations")
        if not isinstance(declarations, list):
            continue
        for declaration in declarations:
            qualified = str(declaration).strip()
            if qualified:
                record(qualified.rsplit(".", 1)[-1], deep=deep)

    routes = review_surface.get("source_component_statement_routes")
    if isinstance(routes, list):
        for route in routes:
            if not isinstance(route, dict):
                continue
            source_item = items.get(str(route.get("source_item") or "").strip())
            if source_item is not None:
                record(route.get("row"), deep=is_deep_item(source_item))

    raw_human_review = payload.get("human_review")
    raw_overrides = (
        raw_human_review.get("include_deep_audit_rows")
        if isinstance(raw_human_review, dict)
        else None
    )
    included_deep_rows = (
        {str(name).strip() for name in raw_overrides if str(name).strip()}
        if isinstance(raw_overrides, list)
        else set()
    )
    return {
        row
        for row, scopes in row_scopes.items()
        if scopes == {True} and row not in included_deep_rows
    }


def public_display_projection_inventory_pin_matches(
    folder: Path,
    inventory: Mapping[str, Any],
    *,
    public_map_sha256: str,
) -> bool:
    """Recognize a guarded public display projection of a private source map.

    Public releases may intentionally omit the raw source artifact while
    retaining exact quoted anchors.  In that display-only representation the
    paper-local status continues to pin the reviewed *private* map digest; the
    companion manifest binds it to the changed public map bytes.  This helper
    is deliberately only a status-rendering compatibility check.  It does not
    make source bytes locally auditable or relax the strict audit/CLI gates.
    The release-candidate guard independently verifies the private commit and
    every manifest binding.
    """

    map_path = folder / "audit" / "paper_statement_map.json"
    source_map = load_json_object(map_path)
    marker = source_map.get(PUBLIC_SOURCE_DISPLAY_PROJECTION_MARKER)
    if not isinstance(marker, Mapping):
        return False
    if (
        type(marker.get("schema")) is not int
        or marker.get("schema") != PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA
        or marker.get("manifest") != PUBLIC_SOURCE_DISPLAY_MANIFEST
        or marker.get("raw_source_bytes_included") is not False
    ):
        return False
    # A path-preserving private map must use its exact local digest rather than
    # this display-only compatibility lane.
    if str(source_map.get("source_artifact_path") or "").strip():
        return False

    manifest_path = folder / PUBLIC_SOURCE_DISPLAY_MANIFEST
    manifest = load_json_object(manifest_path)
    if type(manifest.get("schema")) is not int or manifest.get("schema") != 1:
        return False
    try:
        expected_manifest_path = manifest_path.relative_to(ROOT).as_posix()
    except ValueError:
        return False
    if manifest.get("public_manifest_path") != expected_manifest_path:
        return False
    if manifest.get("raw_source_artifact_included") is not False:
        return False

    private_map_sha256 = str(manifest.get("private_source_map_sha256") or "").lower()
    recorded_map_sha256 = str(inventory.get("map_sha256") or "").lower()
    manifest_public_map_sha256 = str(manifest.get("public_source_map_sha256") or "").lower()
    if not all(
        SHA256_HEX_RE.fullmatch(value)
        for value in (private_map_sha256, recorded_map_sha256, manifest_public_map_sha256)
    ):
        return False
    if private_map_sha256 != recorded_map_sha256:
        return False
    if manifest_public_map_sha256 != public_map_sha256:
        return False

    map_source_sha256 = str(source_map.get("source_artifact_sha256") or "").lower()
    manifest_source_sha256 = str(manifest.get("source_artifact_sha256") or "").lower()
    return (
        SHA256_HEX_RE.fullmatch(map_source_sha256) is not None
        and map_source_sha256 == manifest_source_sha256
    )


def paper_facing_human_review_total(
    folder: Path, payload: dict[str, Any]
) -> int | None:
    """Return the explicit human paper-review denominator, when opted in.

    Saved agent semantic sidecars remain an audit surface and may include
    deep-only diagnostic rows.  The human-facing count is deliberately a
    smaller, source-mapped surface.  Papers opt in while their status records
    are migrated, so unrelated legacy denominators are left unchanged.
    """

    human_review = payload.get("human_review")
    if not isinstance(human_review, dict):
        return None
    surface = human_review.get("surface")
    if surface not in {
        PAPER_FACING_HUMAN_REVIEW_SURFACE,
        NORMAL_SOURCE_PRESENTATIONS_HUMAN_REVIEW_SURFACE,
        SOURCE_CLAIMS_HUMAN_REVIEW_SURFACE,
    }:
        return None
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        raise ValueError(
            f"{payload.get('id', folder.name)}: human paper-review surface requires review_surface"
        )
    raw_names = review_surface.get("include_names")
    if not isinstance(raw_names, list):
        raise ValueError(
            f"{payload.get('id', folder.name)}: human paper-review surface requires include_names"
        )
    names = [str(name).strip() for name in raw_names if str(name).strip()]
    if len(names) != len(set(names)):
        raise ValueError(
            f"{payload.get('id', folder.name)}: human paper-review surface has duplicate include_names"
        )
    raw_assumptions = review_surface.get("assumption_names")
    if raw_assumptions is not None and not isinstance(raw_assumptions, list):
        raise ValueError(
            f"{payload.get('id', folder.name)}: human paper-review assumptions are malformed"
        )
    assumptions = (
        [str(name).strip() for name in raw_assumptions if str(name).strip()]
        if isinstance(raw_assumptions, list)
        else []
    )
    if len(assumptions) != len(set(assumptions)) or set(names).intersection(assumptions):
        raise ValueError(
            f"{payload.get('id', folder.name)}: human paper-review assumptions are ambiguous"
        )
    if surface == NORMAL_SOURCE_PRESENTATIONS_HUMAN_REVIEW_SURFACE:
        inventory = payload.get("source_inventory")
        if not isinstance(inventory, dict):
            raise ValueError(
                f"{payload.get('id', folder.name)}: normal source-presentation review requires source_inventory"
            )
        expected_map_path = (
            folder / "audit" / "paper_statement_map.json"
        ).relative_to(ROOT).as_posix()
        if str(inventory.get("path") or "").strip() != expected_map_path:
            raise ValueError(
                f"{payload.get('id', folder.name)}: normal source-presentation inventory must pin {expected_map_path}"
            )
        map_sha256 = file_sha256(folder / "audit" / "paper_statement_map.json")
        recorded_map_sha256 = str(inventory.get("map_sha256") or "").strip().lower()
        if (
            recorded_map_sha256 != map_sha256
            and not public_display_projection_inventory_pin_matches(
                folder,
                inventory,
                public_map_sha256=map_sha256,
            )
        ):
            raise ValueError(
                f"{payload.get('id', folder.name)}: normal source-presentation inventory is stale against the current source map"
            )
        normal_total = inventory.get("normal_named_theory_items")
        normal_definitions = inventory.get("normal_definition_items")
        normal_results = inventory.get("normal_named_result_items")
        fields = (normal_total, normal_definitions, normal_results)
        if any(
            not isinstance(value, int) or isinstance(value, bool) or value < 0
            for value in fields
        ):
            raise ValueError(
                f"{payload.get('id', folder.name)}: normal source-presentation inventory counts are malformed"
            )
        if normal_total != normal_definitions + normal_results:
            raise ValueError(
                f"{payload.get('id', folder.name)}: normal source-presentation inventory does not reconcile"
            )
        return normal_total + len(assumptions)

    if surface == SOURCE_CLAIMS_HUMAN_REVIEW_SURFACE:
        source_map = load_json_object(folder / "audit" / "paper_statement_map.json")
        raw_items = source_map.get("items")
        if not isinstance(raw_items, dict) or not raw_items:
            raise ValueError(
                f"{payload.get('id', folder.name)}: source-claim review requires a nonempty paper statement map"
            )

        def is_deep_only(item: object) -> bool:
            if not isinstance(item, dict):
                return False
            return (
                "deep" in str(item.get("inventory_role") or "").strip().lower()
                or str(item.get("coverage_status") or "").strip().lower()
                == "deep_audit_material"
            )

        ordinary_claims = [
            item
            for item in raw_items.values()
            if isinstance(item, dict)
            and item.get("claim_bearing") is True
            and str(item.get("inventory_role") or "").strip()
            != "source_presentation_alias"
            and not is_deep_only(item)
        ]
        if not ordinary_claims:
            raise ValueError(
                f"{payload.get('id', folder.name)}: source-claim review has no ordinary source claims"
            )
        return len(ordinary_claims) + len(assumptions)

    excluded_deep = source_map_deep_only_review_rows(folder, payload)
    return len(set(names) - excluded_deep) + len(assumptions)


def llm_statement_judgments_file(folder: Path) -> Path | None:
    tracked = folder / "audit" / "statement_match_llm.json"
    if tracked.exists() and tracked.is_file():
        return tracked
    tracked = folder / "statement_match_llm.json"
    if tracked.exists() and tracked.is_file():
        return tracked
    traced = folder / ".review_traces" / "statement_match_llm.json"
    if traced.exists() and traced.is_file():
        return traced
    return None


def normalize_llm_judgment(raw: Any) -> str:
    if isinstance(raw, bool):
        return "matches" if raw else "mismatch"
    value = str(raw or "").strip().lower()
    if value in {"match", "matches", "yes", "true", "equivalent", "same"}:
        return "matches"
    if value in {
        "mismatch",
        "does_not_match",
        "does not match",
        "no",
        "false",
        "different",
    }:
        return "mismatch"
    if value in {"uncertain", "unknown", "unsure", "partial", "needs_review"}:
        return "uncertain"
    return value


def load_llm_statement_judgments(folder: Path) -> dict[str, dict[str, Any]]:
    path = llm_statement_judgments_file(folder)
    if path is None:
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, Any]] = {}
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name:
            continue
        if isinstance(raw_value, dict):
            out[name] = dict(raw_value)
        else:
            out[name] = {"judgment": raw_value}
    return out


def load_json_object(path: Path) -> dict[str, Any]:
    if not path.exists() or not path.is_file():
        return {}
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def audit_sidecar_path(folder: Path, basename: str) -> Path | None:
    """Return the paper-local sidecar, preferring ``audit/``.

    Aggregate status must not silently use an older root-level copy when a
    current audit-sidecar path is present.  This is a path choice only; the
    content checks below are what establish freshness.
    """

    for path in (folder / "audit" / basename, folder / basename):
        if path.exists() and path.is_file():
            return path
    return None


def statement_match_sidecar_path(folder: Path) -> Path | None:
    """Return the statement-match sidecar using the dashboard loader's order."""

    tracked = audit_sidecar_path(folder, "statement_match_llm.json")
    if tracked is not None:
        return tracked
    traced = folder / ".review_traces" / "statement_match_llm.json"
    if traced.exists() and traced.is_file():
        return traced
    return None


def file_sha256(path: Path) -> str:
    """Return the raw SHA-256 digest of one pinned local artifact."""

    return hashlib.sha256(path.read_bytes()).hexdigest()


def sidecar_relative_artifact(folder: Path, raw_path: object) -> Path | None:
    """Resolve a sidecar artifact path only when it stays inside the paper.

    The aggregate view should never follow an arbitrary sidecar-provided path
    outside the paper folder merely to decide whether an LLM result is fresh.
    """

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    candidate = Path(raw_path.strip())
    if candidate.is_absolute() or ".." in candidate.parts:
        return None
    resolved_folder = folder.resolve()
    # Old sidecars use both paper-relative paths (``source.txt``) and
    # repository-relative paths (``papers/<Paper>/...``).  Try only bases
    # that can still resolve back into this exact paper folder.
    for base in (folder, folder.parent, folder.parent.parent):
        resolved = (base / candidate).resolve()
        try:
            resolved.relative_to(resolved_folder)
        except ValueError:
            continue
        return resolved
    return None


def cached_current_review_surface_items(
    folder: Path,
    *,
    build_input_provider: Any | None = None,
) -> tuple[Any, list[Any]]:
    """Return canonical rows only from a cache verified against current sources.

    Default aggregate synchronization must be read-only and must not turn a
    status refresh into a repository-wide Lean build.  The public dashboard
    loader verifies the cache's current source hashes before returning its
    row-level signatures, paper text, and context-free TeX text.  A missing or
    stale cache is deliberately unavailable rather than rebuilt here.
    """

    try:
        import review_dashboard
    except ModuleNotFoundError:  # pragma: no cover - module-style import
        from scripts import review_dashboard

    kwargs: dict[str, Any] = {"persist_rebind": False}
    if build_input_provider is not None:
        kwargs["build_input_provider"] = build_input_provider
    rows = review_dashboard.load_cached_review_rows(folder, **kwargs)
    if rows is None:
        raise RuntimeError(f"current dashboard cache is unavailable for {folder.name}")
    return review_dashboard, rows


def explicit_dashboard_review_surface_items(folder: Path) -> tuple[Any, list[Any]]:
    """Build/read dashboard rows only for an explicit dashboard-audit request."""

    try:
        import review_dashboard
    except ModuleNotFoundError:  # pragma: no cover - module-style import
        from scripts import review_dashboard

    rows = review_dashboard.review_items_for_paper(
        folder,
        use_cache=True,
        render_images=False,
    )
    return review_dashboard, rows


@dataclass(frozen=True)
class ReviewSurfaceSnapshot:
    """One memoized dashboard surface for a single status-sync paper row."""

    dashboard: Any | None
    rows: tuple[Any, ...] = ()
    problem: str = ""

    @property
    def available(self) -> bool:
        return self.dashboard is not None and not self.problem


@dataclass(frozen=True)
class SavedSidecarReuseAuthorization:
    """Whether tracked v10 row counts may be reused without a row cache."""

    available: bool
    problem: str = ""
    statement_counts: Any | None = None
    coverage_counts: Any | None = None
    coverage_source_bindings: tuple[Mapping[str, str], ...] = ()
    canonical_source_state: str = ""
    receipt_schema: int | None = None
    receipt_sha256: str = ""


class LazySharedClosureProvider:
    """Create one cheap worktree snapshot; normal sync never invokes Lean."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self._provider: WorktreeImportClosureProvider | None = None
        self._problem: Exception | None = None
        self._attempted = False

    def identity_for_entrypoint(self, entrypoint: str):
        if not self._attempted:
            self._attempted = True
            try:
                self._provider = WorktreeImportClosureProvider(
                    self.root,
                    eager_source_snapshot=False,
                )
            except Exception as exc:
                self._problem = exc
        if self._provider is None:
            raise RuntimeError(
                f"shared worktree import-closure snapshot is unavailable: {self._problem}"
            )
        return self._provider.identity_for_entrypoint(entrypoint)

    def identity_from_saved_closure(self, entrypoint: str, saved_closure: object):
        if not self._attempted:
            self._attempted = True
            try:
                self._provider = WorktreeImportClosureProvider(
                    self.root,
                    eager_source_snapshot=False,
                )
            except Exception as exc:
                self._problem = exc
        if self._provider is None:
            raise RuntimeError(
                f"shared worktree import-closure snapshot is unavailable: {self._problem}"
            )
        return self._provider.identity_from_saved_closure(entrypoint, saved_closure)

    def finalization_problems(self) -> tuple[Any, ...]:
        if not self._attempted:
            return ()
        if self._provider is None:
            return (
                RuntimeError(
                    "shared worktree import-closure snapshot is unavailable: "
                    f"{self._problem}"
                ),
            )
        return self._provider.finalization_problems()


class LazySharedBuildInputSnapshotProvider:
    """Share the legacy Python import parser only when a cache needs it."""

    def __init__(self, root: Path) -> None:
        self.root = root.resolve()
        self._provider: Any | None = None
        self._problem: Exception | None = None
        self._attempted = False

    def _get(self) -> Any:
        if not self._attempted:
            self._attempted = True
            try:
                try:
                    from lean_signature_manifest import (
                        RepositoryBuildInputSnapshotProvider,
                    )
                except ModuleNotFoundError:  # pragma: no cover - module import
                    from scripts.lean_signature_manifest import (
                        RepositoryBuildInputSnapshotProvider,
                    )
                self._provider = RepositoryBuildInputSnapshotProvider(self.root)
            except Exception as exc:
                self._problem = exc
        if self._provider is None:
            raise RuntimeError(
                "shared repository build-input snapshot is unavailable: "
                f"{self._problem}"
            )
        return self._provider

    def snapshot(self, import_module: str) -> str | None:
        return self._get().snapshot(import_module)

    def finalize_unchanged(self) -> bool:
        return not self._attempted or (
            self._provider is not None and self._provider.finalize_unchanged()
        )

    def diagnostics(self) -> dict[str, int]:
        if self._provider is None:
            return {}
        return self._provider.diagnostics()


def saved_sidecar_reuse_authorization(
    folder: Path,
    payload: dict[str, Any],
    *,
    closure_provider: Any | None = None,
) -> SavedSidecarReuseAuthorization:
    """Authorize reuse only when immutable material and reuse receipts are exact."""

    status = str(payload.get("status") or "").strip().lower()
    if status not in CLOSEOUT_STATUSES:
        return SavedSidecarReuseAuthorization(
            False, "paper does not have a completed closeout status"
        )
    current_status = load_json_object(folder / "status.json")
    if not current_status or current_status != payload:
        return SavedSidecarReuseAuthorization(
            False, "status payload is not the exact current paper-local record"
        )
    try:
        protocol = load_formalization_protocol()
        versions = protocol.get("audit_versions")
        realization = (
            versions.get("theorem_realization") if isinstance(versions, dict) else None
        )
        baseline = (
            realization.get("legacy_v10_transition_baseline")
            if isinstance(realization, dict)
            else None
        )
        if (
            not isinstance(baseline, dict)
            or baseline.get("authority")
            != IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY
        ):
            return SavedSidecarReuseAuthorization(
                False,
                "cache-free reuse requires the immutable legacy-v10 trust-ledger authority",
            )
        reuse = evaluate_saved_status_reuse(
            root=ROOT,
            folder=folder,
            baseline=baseline,
            protocol=protocol,
            closure_provider=closure_provider,
        )
    except Exception as exc:
        return SavedSidecarReuseAuthorization(
            False, f"legacy-v10 semantic trust evaluation is unavailable: {exc}"
        )
    current_identity = reuse.current_material_identity_sha256
    baseline_identity = reuse.baseline_material_identity_sha256
    if reuse.required:
        return SavedSidecarReuseAuthorization(False, reuse.reason)
    if (
        not re.fullmatch(r"[0-9a-f]{64}", current_identity)
        or current_identity != baseline_identity
    ):
        return SavedSidecarReuseAuthorization(
            False, "legacy-v10 semantic trust evaluation lacks equal identity receipts"
        )
    if (
        not re.fullmatch(r"[0-9a-f]{64}", reuse.current_receipt_sha256)
        or reuse.current_receipt_sha256 != reuse.baseline_receipt_sha256
    ):
        return SavedSidecarReuseAuthorization(
            False, "saved-status trust evaluation lacks equal identity receipts"
        )
    if not isinstance(reuse.statement_counts, dict) or not isinstance(
        reuse.coverage_counts, dict
    ):
        return SavedSidecarReuseAuthorization(
            False, "saved-status trust evaluation lacks exact saved counts"
        )
    try:
        coverage_source_bindings = validated_coverage_source_bindings(
            reuse.coverage_source_bindings
        )
    except ValueError as exc:
        return SavedSidecarReuseAuthorization(
            False,
            "saved-status trust evaluation lacks valid semantic source bindings: "
            + str(exc),
        )
    coverage_total = reuse.coverage_counts.get("total")
    if (
        not isinstance(coverage_total, int)
        or isinstance(coverage_total, bool)
        or coverage_total != len(coverage_source_bindings)
    ):
        return SavedSidecarReuseAuthorization(
            False,
            "saved-status semantic source bindings disagree with the coverage total",
        )
    return SavedSidecarReuseAuthorization(
        True,
        statement_counts=reuse.statement_counts,
        coverage_counts=reuse.coverage_counts,
        coverage_source_bindings=tuple(
            dict(binding) for binding in coverage_source_bindings
        ),
        canonical_source_state=str(getattr(reuse, "canonical_source_state", "") or ""),
        receipt_schema=SAVED_STATUS_REUSE_RECEIPT_SCHEMA,
        receipt_sha256=str(reuse.current_receipt_sha256),
    )


class ReviewSurfaceProvider:
    """Lazily load one paper surface through exactly one permitted route.

    Default synchronization calls only the non-persisting cache loader.  The
    explicit audit flag selects the dashboard extraction path, which is the
    sole route here that may build a module or invoke Lean.
    """

    def __init__(
        self,
        folder: Path,
        *,
        use_dashboard_audit: bool,
        closure_provider: Any | None = None,
        build_input_provider: Any | None = None,
    ) -> None:
        self.folder = folder
        self.use_dashboard_audit = use_dashboard_audit
        self.closure_provider = closure_provider
        self.build_input_provider = build_input_provider
        self._snapshot: ReviewSurfaceSnapshot | None = None
        self._saved_sidecar_authorization: SavedSidecarReuseAuthorization | None = None
        self._saved_sidecar_status_digest = ""
        self._corrected_scope_current: bool | None = None
        self._corrected_scope_status_digest = ""
        self._v11_source_spec_counts: tuple[dict[str, int] | None, str] | None = None
        self._v11_source_spec_status_digest = ""

    @staticmethod
    def _status_digest(payload: Mapping[str, Any]) -> str:
        return hashlib.sha256(
            json.dumps(
                payload,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()

    def corrected_scope_is_current(self, payload: dict[str, Any]) -> bool:
        """Evaluate one corrected-target contract at most once per paper row."""

        status_digest = self._status_digest(payload)
        if self._corrected_scope_current is None:
            # Most papers have no corrected-target lane. Avoid loading the
            # source-record validator at all for that ordinary case.
            self._corrected_scope_current = bool(
                author_approved_corrected_scope(payload)
                and current_author_approved_corrected_scope(self.folder, payload)
            )
            self._corrected_scope_status_digest = status_digest
        elif self._corrected_scope_status_digest != status_digest:
            return False
        return self._corrected_scope_current

    def authorize_saved_sidecar_reuse(
        self, payload: dict[str, Any]
    ) -> SavedSidecarReuseAuthorization:
        """Memoize one fail-closed transition check for both dashboard labels."""

        if self.use_dashboard_audit:
            return SavedSidecarReuseAuthorization(
                False, "explicit dashboard audit requires the current dashboard surface"
            )
        status_digest = self._status_digest(payload)
        if self._saved_sidecar_authorization is None:
            self._saved_sidecar_authorization = saved_sidecar_reuse_authorization(
                self.folder,
                payload,
                closure_provider=self.closure_provider,
            )
            self._saved_sidecar_status_digest = status_digest
        elif self._saved_sidecar_status_digest != status_digest:
            return SavedSidecarReuseAuthorization(
                False,
                "review-surface provider was reused with a different status payload",
            )
        return self._saved_sidecar_authorization

    def load(self) -> ReviewSurfaceSnapshot:
        if self._snapshot is not None:
            return self._snapshot
        try:
            dashboard, rows = (
                explicit_dashboard_review_surface_items(self.folder)
                if self.use_dashboard_audit
                else cached_current_review_surface_items(
                    self.folder,
                    build_input_provider=self.build_input_provider,
                )
            )
        except Exception:
            self._snapshot = ReviewSurfaceSnapshot(
                dashboard=None,
                problem=(
                    f"current dashboard review surface is unavailable for "
                    f"{self.folder.name}"
                ),
            )
        else:
            self._snapshot = ReviewSurfaceSnapshot(
                dashboard=dashboard,
                rows=tuple(rows),
            )
        return self._snapshot


def review_surface_snapshot(
    folder: Path,
    *,
    use_dashboard_audit: bool,
    provider: ReviewSurfaceProvider | None = None,
) -> ReviewSurfaceSnapshot:
    """Resolve a compatible memoized surface, failing closed on misuse."""

    selected = provider or ReviewSurfaceProvider(
        folder,
        use_dashboard_audit=use_dashboard_audit,
    )
    if (
        selected.folder.resolve() != folder.resolve()
        or selected.use_dashboard_audit != use_dashboard_audit
    ):
        return ReviewSurfaceSnapshot(
            dashboard=None,
            problem="review-surface provider scope does not match the requested paper",
        )
    return selected.load()


def canonical_statement_translation_summary(
    folder: Path,
    *,
    use_dashboard_audit: bool = False,
    review_surface_provider: ReviewSurfaceProvider | None = None,
) -> dict[str, Any]:
    """Evaluate saved statement-match evidence against canonical current rows."""

    snapshot = review_surface_snapshot(
        folder,
        use_dashboard_audit=use_dashboard_audit,
        provider=review_surface_provider,
    )
    if not snapshot.available:
        raise RuntimeError(snapshot.problem)
    return snapshot.dashboard.statement_translation_audit_summary(
        folder,
        list(snapshot.rows),
    )


def statement_match_sidecar_freshness_problem(
    folder: Path,
    *,
    summary: dict[str, Any] | None = None,
    use_dashboard_audit: bool = False,
    review_surface_provider: ReviewSurfaceProvider | None = None,
) -> str | None:
    """Return a fail-closed reason when saved row-translation judgments are stale.

    The statement-match lane is independent of source-record and paper-coverage
    lanes.  Its freshness comes from the canonical dashboard's row-level
    prompt, Lean-signature, paper-statement, and context-free TeX-statement
    checks, not from the spelling of a declaration name in ``status.json``.
    """

    statement_path = statement_match_sidecar_path(folder)
    if statement_path is None:
        return None
    statement_match = load_json_object(statement_path)
    items = statement_match.get("items") if statement_match else None
    if not isinstance(items, dict):
        return "statement-match evidence is unavailable"
    # An empty scaffold has no saved positive count to misrepresent.
    if not items:
        return None
    if statement_match.get("schema") != 1 or statement_match.get("paper") not in {
        None,
        folder.name,
    }:
        return "statement-match evidence is unavailable"

    try:
        current_summary = (
            summary
            if summary is not None
            else (
                canonical_statement_translation_summary(
                    folder,
                    use_dashboard_audit=use_dashboard_audit,
                )
                if review_surface_provider is None
                else canonical_statement_translation_summary(
                    folder,
                    use_dashboard_audit=use_dashboard_audit,
                    review_surface_provider=review_surface_provider,
                )
            )
        )
    except Exception:
        return "statement-match canonical review surface is unavailable"

    if int(current_summary.get("stale_judgment_count", 0)):
        return "statement-match row evidence is stale"
    return None


def coverage_sidecar_freshness_problem(
    folder: Path,
    *,
    use_dashboard_audit: bool = False,
    summary: dict[str, Any] | None = None,
    review_surface_provider: ReviewSurfaceProvider | None = None,
) -> str | None:
    """Return a fail-closed reason when paper-coverage evidence is stale.

    Coverage sidecars pin both the semantic source inventory and the canonical
    dashboard review surface, rather than a list of declaration names. Compare
    those mandatory digests to their current semantic artifacts and, when a
    sidecar also pins a source/map/interface/status artifact, compare the exact
    artifact bytes as well.
    """

    coverage_path = audit_sidecar_path(folder, "paper_coverage_llm.json")
    if coverage_path is None:
        status = (
            str(load_json_object(folder / "status.json").get("status") or "")
            .strip()
            .lower()
        )
        if status.startswith("formalized") or status.startswith("partially formalized"):
            return "paper-coverage evidence is unavailable"
        return None
    coverage = load_json_object(coverage_path)
    items = coverage.get("items") if isinstance(coverage, dict) else None
    if not isinstance(items, dict):
        return "paper-coverage evidence is unavailable"
    # An empty scaffold has no saved positive count to misrepresent.
    if not items:
        return None
    if coverage.get("schema") != 1 or coverage.get("paper") not in {None, folder.name}:
        return "paper-coverage evidence is unavailable"

    try:
        if summary is None:
            snapshot = review_surface_snapshot(
                folder,
                use_dashboard_audit=use_dashboard_audit,
                provider=review_surface_provider,
            )
            if not snapshot.available:
                raise RuntimeError(snapshot.problem)
            coverage_summary = snapshot.dashboard.paper_coverage_audit_summary(
                folder,
                list(snapshot.rows),
            )
        else:
            coverage_summary = summary
    except Exception:
        return "paper-coverage inventory or review surface is unavailable"
    if coverage_summary.get("source_coverage_mode_error"):
        return "paper-coverage source mode is invalid"
    if coverage_summary.get("source_coverage_mode_migration_error"):
        return "paper-coverage source mode has not been explicitly migrated"
    if coverage_summary.get("deep_source_coverage_attestation_error"):
        return "deep paper-coverage inventory attestation is unavailable"
    if coverage_summary.get("source_presentation_classification_error_count", 0):
        return "paper-coverage source inventory has structural or presentation errors"
    if coverage_summary.get("source_named_result_inventory_error_count", 0):
        return "paper-coverage named-result source inventory is incomplete or stale"
    if coverage_summary.get("ambiguous_semantic_item_bindings"):
        return "paper-coverage semantic item rebinding is ambiguous"
    if coverage_summary.get("missing_coverage_count", 0) or coverage_summary.get(
        "extra_coverage_count", 0
    ):
        return "paper-coverage inventory digest is stale"
    if coverage_summary.get("source_coverage_mode_mismatch"):
        return "paper-coverage source mode is stale"
    if coverage_summary.get("stale_source_item_count", 0):
        return "paper-coverage source item evidence is stale"
    if coverage_summary.get("unverified_reused_source_item_count", 0):
        return "paper-coverage reusable source item lacks a byte-verified source anchor"
    if coverage_summary.get("legacy_unpinned_item_count", 0):
        return "paper-coverage legacy item evidence is stale"
    if coverage_summary.get("stale_statement_count", 0):
        return "paper-coverage source statement evidence is stale"
    if coverage_summary.get("coverage_row_signature_error_count", 0):
        return "paper-coverage Lean row signature evidence is stale"
    if coverage_summary.get("invalid_row_link_count", 0):
        return "paper-coverage row link is stale"

    pinned_artifacts = (
        (
            "source artifact",
            coverage.get("source_artifact_path"),
            coverage.get("source_artifact_sha256"),
        ),
        (
            "paper statement map",
            coverage.get("paper_statement_map_path")
            or "audit/paper_statement_map.json",
            coverage.get("paper_statement_map_sha256"),
        ),
        (
            "paper interface",
            "PaperInterface.lean",
            coverage.get("paper_interface_sha256"),
        ),
        ("status JSON", "status.json", coverage.get("status_json_sha256")),
        (
            "review-surface cache",
            coverage.get("review_surface_cache_path"),
            coverage.get("review_surface_cache_sha256"),
        ),
    )
    for label, raw_path, raw_digest in pinned_artifacts:
        digest = str(raw_digest or "").strip()
        if not digest:
            continue
        artifact = sidecar_relative_artifact(folder, raw_path)
        if artifact is None or not artifact.exists() or not artifact.is_file():
            return f"paper-coverage {label} pin is unavailable"
        try:
            current_digest = file_sha256(artifact)
        except OSError:
            return f"paper-coverage {label} pin is unavailable"
        if digest != current_digest:
            return f"paper-coverage {label} pin is stale"
    return None


def stale_unavailable_label(problem: str) -> str:
    """Render a stale sidecar state without presenting old counts as current."""

    return f"stale/unavailable: {problem}"


def current_author_approved_corrected_scope(
    folder: Path, payload: dict[str, Any]
) -> bool:
    """Whether generated status must use the corrected-target evidence lane.

    Historical LLM statement/coverage sidecars compare an archived source
    baseline. They cannot describe an explicitly different, author-approved
    governing target, so only a current pinned semantic contract may replace
    their generated labels.
    """

    try:
        try:
            from audit_evidence_integrity import (
                author_approved_corrected_scope_contract_is_current,
            )
        except ModuleNotFoundError:
            from scripts.audit_evidence_integrity import (
                author_approved_corrected_scope_contract_is_current,
            )
        return author_approved_corrected_scope_contract_is_current(folder, payload)
    except Exception:
        return False


def author_approved_corrected_scope(payload: dict[str, Any]) -> dict[str, Any] | None:
    """Return a declared governing corrected target without inferring one."""

    scope = payload.get("formalization_scope")
    if not isinstance(scope, dict):
        return None
    if str(scope.get("kind") or "").strip() != "author_approved_corrected_model":
        return None
    return scope


def source_condition_rows_for_payload(
    payload: dict[str, Any], statement_total: int
) -> int:
    review_surface = payload.get("review_surface", {})
    assumption_names = (
        review_surface.get("assumption_names")
        if isinstance(review_surface, dict)
        else None
    )
    assumption_count = (
        len([str(name).strip() for name in assumption_names if str(name).strip()])
        if isinstance(assumption_names, list)
        else 0
    )
    # A paper that opts into the smaller human-facing surface may exclude
    # deep-only statement rows while retaining every source-condition row.
    # Its agent-side statement count is still the broad audit count, so do not
    # infer the number of source conditions by subtracting the public total.
    human_review = payload.get("human_review")
    if (
        isinstance(human_review, dict)
        and human_review.get("surface")
        in {
            PAPER_FACING_HUMAN_REVIEW_SURFACE,
            NORMAL_SOURCE_PRESENTATIONS_HUMAN_REVIEW_SURFACE,
            SOURCE_CLAIMS_HUMAN_REVIEW_SURFACE,
        }
    ):
        return assumption_count
    human_total = int(payload.get("human_review", {}).get("total_rows", 0))
    return max(0, min(assumption_count, human_total - statement_total))


def llm_translation_label_from_counts(
    *,
    total: int,
    matches: int,
    mismatch: int = 0,
    formalization_boundary: int = 0,
    source_condition_rows: int = 0,
    uncertain: int = 0,
    unknown: int = 0,
    missing: int = 0,
    stale: int = 0,
) -> str:
    if total <= 0:
        if source_condition_rows:
            label = (
                "source-condition row"
                if source_condition_rows == 1
                else "source-condition rows"
            )
            return f"{source_condition_rows} {label}"
        return "not run"
    if (
        not any(
            [
                matches,
                mismatch,
                formalization_boundary,
                source_condition_rows,
                uncertain,
                unknown,
                stale,
            ]
        )
        and missing >= total
    ):
        return "not run"
    if source_condition_rows:
        parts = [f"{matches}/{total} statement rows match"]
    else:
        parts = [f"{matches}/{total} match"]
    if mismatch:
        parts.append(f"{mismatch} mismatch")
    if formalization_boundary:
        label = (
            "formalization-boundary statement row"
            if formalization_boundary == 1
            else "formalization-boundary statement rows"
        )
        parts.append(f"{formalization_boundary} {label}")
    if source_condition_rows:
        label = (
            "source-condition row"
            if source_condition_rows == 1
            else "source-condition rows"
        )
        parts.append(f"{source_condition_rows} {label}")
    if uncertain:
        parts.append(f"{uncertain} uncertain")
    if unknown:
        parts.append(f"{unknown} unknown")
    if missing:
        parts.append(f"{missing} missing")
    if stale:
        parts.append(f"{stale} stale")
    return "; ".join(parts)


def paper_coverage_label_from_counts(
    *,
    total: int,
    covered: int,
    corrected_target_covered: int = 0,
    conditional_boundary: int = 0,
    support_only: int = 0,
    support_only_required: int = 0,
    out_of_scope: int = 0,
    scope_exclusion: int = 0,
    required_out_of_scope: int = 0,
    partial: int = 0,
    missing: int = 0,
    uncertain: int = 0,
    unknown: int = 0,
    stale: int = 0,
) -> str:
    successful_covered = covered + corrected_target_covered
    if total <= 0:
        return "not run"
    if (
        not any(
            [
                successful_covered,
                conditional_boundary,
                support_only,
                out_of_scope,
                scope_exclusion,
                partial,
                uncertain,
                unknown,
                stale,
            ]
        )
        and missing >= total
    ):
        return "not run"
    if corrected_target_covered:
        target_label = (
            "approved corrected target"
            if corrected_target_covered == 1
            else "approved corrected targets"
        )
        parts = [
            f"{successful_covered}/{total} covered "
            f"({covered} direct; {corrected_target_covered} {target_label})"
        ]
    else:
        parts = [f"{successful_covered}/{total} covered"]
    if conditional_boundary:
        parts.append(f"{conditional_boundary} conditional boundaries")
    if support_only:
        parts.append(f"{support_only} support-only")
    if support_only_required:
        parts.append(f"{support_only_required} required support-only")
    if out_of_scope:
        parts.append(f"{out_of_scope} out of scope")
    if scope_exclusion:
        label = (
            "user-approved scope exclusion"
            if scope_exclusion == 1
            else "user-approved scope exclusions"
        )
        parts.append(f"{scope_exclusion} {label}")
    if required_out_of_scope:
        parts.append(f"{required_out_of_scope} required scoped out")
    if partial:
        parts.append(f"{partial} partial")
    if missing:
        parts.append(f"{missing} missing")
    if uncertain:
        parts.append(f"{uncertain} uncertain")
    if unknown:
        parts.append(f"{unknown} unknown")
    if stale:
        parts.append(f"{stale} stale")
    return "; ".join(parts)


def llm_translation_label_from_dashboard_summary(
    summary: dict[str, Any],
    payload: dict[str, Any],
) -> str:
    """Render one canonical dashboard statement-translation summary."""

    statement_total = int(summary.get("row_count", 0))
    return llm_translation_label_from_counts(
        total=statement_total,
        matches=int(summary.get("matches", 0)),
        mismatch=int(
            summary.get(
                "unresolved_mismatch_count",
                summary.get("mismatch_count", 0),
            )
        ),
        formalization_boundary=int(summary.get("conditional_boundary_count", 0)),
        source_condition_rows=source_condition_rows_for_payload(
            payload, statement_total
        ),
        uncertain=int(summary.get("uncertain_count", 0)),
        unknown=int(summary.get("unknown_count", 0)),
        missing=int(summary.get("missing_judgment_count", 0)),
        stale=int(summary.get("stale_judgment_count", 0)),
    )


def saved_statement_translation_label(
    folder: Path,
    counts: Any | None = None,
) -> str | None:
    """Render counts from the same semantic projection pinned by the ledger."""

    if not isinstance(counts, dict):
        disposition, _problem = statement_disposition(folder)
        if disposition is None:
            return None
        counts = disposition.counts
    total = int(counts["total"])
    return llm_translation_label_from_counts(
        total=total,
        matches=int(counts["matches"]),
        mismatch=int(counts["mismatch"]),
        formalization_boundary=int(counts["formalization_boundary"]),
        source_condition_rows=int(counts["source_condition_rows"]),
        uncertain=int(counts["uncertain"]),
        unknown=int(counts["unknown"]),
    )


def saved_paper_coverage_label(
    folder: Path,
    counts: Any | None = None,
) -> str | None:
    """Render counts from the source/Lean associations pinned by the ledger."""

    if not isinstance(counts, dict):
        disposition, _problem = coverage_disposition(folder)
        if disposition is None:
            return None
        counts = disposition.counts
    return paper_coverage_label_from_counts(
        total=int(counts["total"]),
        covered=int(counts["covered"]),
        corrected_target_covered=int(counts["corrected_target_covered"]),
        conditional_boundary=int(counts["conditional_boundary"]),
        support_only=int(counts["support_only"]),
        out_of_scope=int(counts["out_of_scope"]),
        scope_exclusion=int(counts["scope_exclusion"]),
    )


def _current_v11_status_protocol_selected(
    folder: Path, payload: Mapping[str, Any]
) -> bool:
    """Use the closeout owner's complete status/map protocol selection."""

    if current_v11_protocol_selected(payload):
        return True
    return current_v11_protocol_selected(
        payload, load_json_object(folder / "audit" / "paper_statement_map.json")
    )


def current_v11_source_spec_counts(
    folder: Path,
    payload: dict[str, Any],
    *,
    review_surface_provider: ReviewSurfaceProvider | None = None,
) -> tuple[dict[str, int] | None, str]:
    """Return current direct source-to-Spec counts for an opted-in closeout.

    v11 intentionally replaces the legacy Lean-to-paraphrase sidecar with one
    raw-source/expanded-Spec judgment per human source claim. A normal status
    sync must not silently fall back to the retired lane. For schema 6 it
    projects the explicit human selection and normalized verdicts from the one
    authenticated accepted graph; earlier receipt schemas retain their own
    hash-pinned review ledger. It deliberately does not re-elaborate Lean:
    current closure validation belongs to explicit closeout and release gates,
    not website rendering.
    """

    review_surface = payload.get("review_surface")
    if not _current_v11_status_protocol_selected(folder, payload):
        return None, ""
    if not isinstance(review_surface, dict):
        return None, "current source-to-Spec review_surface is unavailable"
    status_digest = ReviewSurfaceProvider._status_digest(payload)
    if review_surface_provider is not None:
        if (
            review_surface_provider._v11_source_spec_counts is not None
            and review_surface_provider._v11_source_spec_status_digest == status_digest
        ):
            return review_surface_provider._v11_source_spec_counts

    def record(result: tuple[dict[str, int] | None, str]) -> tuple[dict[str, int] | None, str]:
        if review_surface_provider is not None:
            review_surface_provider._v11_source_spec_counts = result
            review_surface_provider._v11_source_spec_status_digest = status_digest
        return result

    def graph_review_source_items(projection: Any) -> tuple[str, ...]:
        """Resolve the explicit human surface to exact source-map item IDs."""

        raw_names = review_surface.get("include_names")
        if not isinstance(raw_names, list) or not raw_names:
            raise ValueError("graph-native human review has no include_names")
        names = [str(name).strip() for name in raw_names]
        if any(not name for name in names) or len(names) != len(set(names)):
            raise ValueError("graph-native human review include_names are malformed")

        source_items_by_review_name: dict[str, set[str]] = {}
        for source_item_id, declarations in (
            projection.review_declarations_by_source_item.items()
        ):
            for declaration in declarations:
                name = str(declaration).strip().rsplit(".", 1)[-1]
                if name:
                    source_items_by_review_name.setdefault(name, set()).add(
                        str(source_item_id)
                    )

        selected: list[str] = []
        for name in names:
            candidates = source_items_by_review_name.get(name, set())
            if len(candidates) != 1:
                raise ValueError(
                    f"human-review row {name!r} does not resolve to one source item"
                )
            selected.append(next(iter(candidates)))

        raw_conditions = review_surface.get("source_condition_items", [])
        if not isinstance(raw_conditions, list):
            raise ValueError("graph-native source_condition_items are malformed")
        condition_items = [str(item).strip() for item in raw_conditions]
        if (
            any(not item for item in condition_items)
            or len(condition_items) != len(set(condition_items))
            or any(
                item not in projection.review_declarations_by_source_item
                for item in condition_items
            )
        ):
            raise ValueError("graph-native source_condition_items are malformed")
        selected.extend(condition_items)
        if len(selected) != len(set(selected)):
            raise ValueError("graph-native human-review source items overlap")

        expected_total = int(payload.get("human_review", {}).get("total_rows", 0))
        if expected_total <= 0 or len(selected) != expected_total:
            raise ValueError(
                "graph-native human-review selection does not equal total_rows"
            )
        return tuple(selected)

    def graph_counts(projection: Any) -> dict[str, int]:
        selected = graph_review_source_items(projection)
        verdicts = projection.source_lean_verdicts_by_source_item
        counts = {
            "total": len(selected),
            "matches": 0,
            "mismatch": 0,
            "uncertain": 0,
            "unknown": 0,
            # Presentation-only provenance. The explicit release/closeout gate,
            # not this projection, establishes current Lean realization.
            "recorded_closeout": 1,
        }
        for source_item_id in selected:
            verdict = str(verdicts.get(source_item_id) or "")
            if verdict == "matches":
                counts["matches"] += 1
            elif verdict == "does_not_match":
                counts["mismatch"] += 1
            elif verdict == "uncertain":
                counts["uncertain"] += 1
            else:
                counts["unknown"] += 1
        return counts

    screening_path = folder / "audit" / "v11_raw_source_spec_screening.json"
    try:
        try:
            from final_closure_receipt import load_final_closure_receipt
        except ModuleNotFoundError:  # pragma: no cover - module-style import
            from scripts.final_closure_receipt import load_final_closure_receipt
        receipt = load_final_closure_receipt(ROOT, folder.name).payload
        if receipt.get("schema") == 6:
            try:
                try:
                    from obligation_closure_credential import (
                        validate_nonaccepting_recorded_graph_projection,
                    )
                except ModuleNotFoundError:  # pragma: no cover - module-style import
                    from scripts.obligation_closure_credential import (
                        validate_nonaccepting_recorded_graph_projection,
                    )
                projection = validate_nonaccepting_recorded_graph_projection(
                    ROOT, folder.name, receipt
                )
                return record((graph_counts(projection), ""))
            except Exception as exc:  # noqa: BLE001 - projection remains fail closed.
                return record(
                    (None, f"recorded accepted graph projection is unavailable: {exc}")
                )
        elif receipt.get("schema") == 5:
            try:
                try:
                    from obligation_evidence_store import load_paper_obligation_bundle
                except ModuleNotFoundError:  # pragma: no cover - module-style import
                    from scripts.obligation_evidence_store import (
                        load_paper_obligation_bundle,
                    )
                loaded_bundle = load_paper_obligation_bundle(ROOT, folder.name)
                bundle_pointer = receipt.get("obligation_bundle")
                if (
                    receipt.get("paper") != folder.name
                    or receipt.get("closure_status") != "current"
                    or not isinstance(bundle_pointer, Mapping)
                    or bundle_pointer.get("bundle_sha256")
                    != loaded_bundle.bundle.bundle_sha256
                    or not loaded_bundle.bundle.acceptance_credential
                ):
                    return record((None, "recorded obligation-graph receipt is not current"))
            except Exception as exc:  # noqa: BLE001 - projection remains fail closed.
                return record((None, f"recorded obligation graph is unavailable: {exc}"))
        else:
            ledger_pin = receipt.get("review_ledger")
            expected_ledger_path = (
                f"papers/{folder.name}/audit/v11_raw_source_spec_screening.json"
            )
            if (
                receipt.get("paper") != folder.name
                or receipt.get("closure_status") != "current"
                or receipt.get("evidence_lane") != "direct-source-row-review"
                or not isinstance(ledger_pin, Mapping)
                or ledger_pin.get("path") != expected_ledger_path
                or ledger_pin.get("sha256") != file_sha256(screening_path)
            ):
                return record((None, "recorded direct source-to-Spec receipt is not current"))
    except Exception as exc:  # noqa: BLE001 - a status projection must fail closed.
        return record((None, f"direct source-to-Spec receipt is unavailable: {exc}"))

    screening = load_json_object(screening_path)
    rows = screening.get("items") if isinstance(screening, dict) else None
    expected_total = int(payload.get("human_review", {}).get("total_rows", 0))
    if (
        not isinstance(rows, dict)
        or screening.get("schema") != 2
        or screening.get("paper") != folder.name
        or not str(screening.get("validator") or "").strip()
        or not str(screening.get("validated_at") or "").strip()
        or expected_total <= 0
        or len(rows) != expected_total
    ):
        return record((None, "direct source-to-Spec ledger is incomplete"))

    counts = {
        "total": expected_total,
        "matches": 0,
        "mismatch": 0,
        "uncertain": 0,
        "unknown": 0,
    }
    for row in rows.values():
        judgment = (
            str(row.get("judgment") or "").strip().lower()
            if isinstance(row, dict)
            else ""
        )
        if judgment == "matches":
            counts["matches"] += 1
        elif judgment == "mismatch":
            counts["mismatch"] += 1
        elif judgment == "uncertain":
            counts["uncertain"] += 1
        else:
            counts["unknown"] += 1
    return record((counts, ""))


def current_v11_source_spec_label(
    folder: Path,
    payload: dict[str, Any],
    *,
    coverage: bool,
    review_surface_provider: ReviewSurfaceProvider | None = None,
) -> str | None:
    """Render the accepted v11 direct-review lane, or its stale reason."""

    counts, problem = current_v11_source_spec_counts(
        folder,
        payload,
        review_surface_provider=review_surface_provider,
    )
    if counts is None:
        if _current_v11_status_protocol_selected(folder, payload):
            return stale_unavailable_label(problem or "direct source-to-Spec evidence is unavailable")
        return None
    total = counts["total"]
    matches = counts["matches"]
    prefix = "accepted closeout: " if counts.get("recorded_closeout") else ""
    if coverage:
        parts = [f"{prefix}{matches}/{total} source claims covered"]
    else:
        parts = [f"{prefix}{matches}/{total} raw-source-to-Spec match"]
    for key, label in (
        ("mismatch", "mismatch"),
        ("uncertain", "uncertain"),
        ("unknown", "unknown"),
    ):
        if counts[key]:
            parts.append(f"{counts[key]} {label}")
    return "; ".join(parts)


def llm_translation_label(
    folder: Path,
    payload: dict[str, Any],
    *,
    use_dashboard_audit: bool = False,
    review_surface_provider: ReviewSurfaceProvider | None = None,
) -> str:
    selected_provider = review_surface_provider or ReviewSurfaceProvider(
        folder,
        use_dashboard_audit=use_dashboard_audit,
    )
    v11_label = current_v11_source_spec_label(
        folder,
        payload,
        coverage=False,
        review_surface_provider=selected_provider,
    )
    if v11_label is not None:
        return v11_label
    if selected_provider.corrected_scope_is_current(payload):
        return "formalized target differs from the pinned archive; semantic contract current"
    authorization = selected_provider.authorize_saved_sidecar_reuse(payload)
    if authorization.available:
        saved_label = saved_statement_translation_label(
            folder, authorization.statement_counts
        )
        if saved_label is not None:
            return saved_label
    statement_path = statement_match_sidecar_path(folder)
    statement_sidecar = load_json_object(statement_path) if statement_path else {}
    raw_statement_items = statement_sidecar.get("items")
    summary: dict[str, Any] | None = None
    if use_dashboard_audit or (
        isinstance(raw_statement_items, dict) and bool(raw_statement_items)
    ):
        try:
            if review_surface_provider is None:
                summary = canonical_statement_translation_summary(
                    folder,
                    use_dashboard_audit=use_dashboard_audit,
                )
            else:
                summary = canonical_statement_translation_summary(
                    folder,
                    use_dashboard_audit=use_dashboard_audit,
                    review_surface_provider=review_surface_provider,
                )
        except Exception:
            if isinstance(raw_statement_items, dict) and raw_statement_items:
                return stale_unavailable_label(
                    "statement-match canonical review surface is unavailable"
                )

    freshness_problem = statement_match_sidecar_freshness_problem(
        folder,
        summary=summary,
        use_dashboard_audit=use_dashboard_audit,
        review_surface_provider=review_surface_provider,
    )
    if freshness_problem:
        return stale_unavailable_label(freshness_problem)
    if audit_sidecar_path(folder, "paper_coverage_llm.json") is None:
        return "not run"
    if summary is not None:
        return llm_translation_label_from_dashboard_summary(summary, payload)

    review_surface = payload.get("review_surface", {})
    include_names = (
        review_surface.get("include_names")
        if isinstance(review_surface, dict)
        else None
    )
    names = (
        [str(name).strip() for name in include_names if str(name).strip()]
        if isinstance(include_names, list)
        else []
    )
    judgments = load_llm_statement_judgments(folder)
    if not names:
        total = int(payload.get("human_review", {}).get("total_rows", 0))
        names = list(judgments)
    else:
        total = len(names)
    source_condition_rows = source_condition_rows_for_payload(payload, total)
    if not judgments:
        return llm_translation_label_from_counts(
            total=total,
            matches=0,
            missing=total,
            source_condition_rows=source_condition_rows,
        )

    matches = mismatch = formalization_boundary = uncertain = unknown = missing = 0
    for name in names:
        judgment = judgments.get(name)
        if judgment is None:
            missing += 1
            continue
        value = normalize_llm_judgment(
            judgment.get("judgment") or judgment.get("matches")
        )
        if value == "matches":
            matches += 1
        elif value == "mismatch":
            if judgment.get("resolution") == "conditional_boundary":
                formalization_boundary += 1
            else:
                mismatch += 1
        elif value == "uncertain":
            uncertain += 1
        else:
            unknown += 1

    return llm_translation_label_from_counts(
        total=total,
        matches=matches,
        mismatch=mismatch,
        formalization_boundary=formalization_boundary,
        source_condition_rows=source_condition_rows,
        uncertain=uncertain,
        unknown=unknown,
        missing=missing,
    )


def llm_paper_coverage_label(
    folder: Path,
    payload: dict[str, Any],
    *,
    use_dashboard_audit: bool = False,
    review_surface_provider: ReviewSurfaceProvider | None = None,
) -> str:
    selected_provider = review_surface_provider or ReviewSurfaceProvider(
        folder,
        use_dashboard_audit=use_dashboard_audit,
    )
    v11_label = current_v11_source_spec_label(
        folder,
        payload,
        coverage=True,
        review_surface_provider=selected_provider,
    )
    if v11_label is not None:
        return v11_label
    if selected_provider.corrected_scope_is_current(payload):
        return "formalized target differs from the pinned archive; semantic contract current"
    authorization = selected_provider.authorize_saved_sidecar_reuse(payload)
    if authorization.available:
        saved_label = saved_paper_coverage_label(folder, authorization.coverage_counts)
        if saved_label is not None:
            return saved_label
    coverage_path = audit_sidecar_path(folder, "paper_coverage_llm.json")
    coverage = load_json_object(coverage_path) if coverage_path is not None else {}
    raw_items = coverage.get("items")
    if coverage_path is None:
        freshness_problem = coverage_sidecar_freshness_problem(
            folder,
            use_dashboard_audit=use_dashboard_audit,
            review_surface_provider=review_surface_provider,
        )
        if freshness_problem:
            return stale_unavailable_label(freshness_problem)
        return stale_unavailable_label(
            "paper-coverage inventory or review surface is unavailable"
        )
    if not isinstance(raw_items, dict) or not raw_items:
        freshness_problem = coverage_sidecar_freshness_problem(
            folder,
            use_dashboard_audit=use_dashboard_audit,
            review_surface_provider=review_surface_provider,
        )
        if freshness_problem:
            return stale_unavailable_label(freshness_problem)
        return "not run"

    # Use the same selected source inventory as the closeout gate without
    # reopening the live dashboard. The default snapshot is accepted only
    # after its source and elaborated-signature pins match current bytes.
    try:
        snapshot = review_surface_snapshot(
            folder,
            use_dashboard_audit=use_dashboard_audit,
            provider=review_surface_provider,
        )
        if not snapshot.available:
            raise RuntimeError(snapshot.problem)
        summary = snapshot.dashboard.paper_coverage_audit_summary(
            folder,
            list(snapshot.rows),
        )
    except Exception:
        return stale_unavailable_label(
            "paper-coverage inventory or review surface is unavailable"
        )
    freshness_problem = coverage_sidecar_freshness_problem(
        folder,
        use_dashboard_audit=use_dashboard_audit,
        summary=summary,
        review_surface_provider=review_surface_provider,
    )
    if freshness_problem:
        return stale_unavailable_label(freshness_problem)

    total = int(summary.get("inventory_count", 0))
    covered = int(summary.get("covered_count", 0))
    if (
        summary.get("inventory_is_scaffold")
        or summary.get("missing_source_grounded_audit")
        or int(summary.get("covered_with_seed_reason_count", 0))
        or int(summary.get("covered_without_source_evidence_count", 0))
    ):
        if total > 0:
            return f"{covered}/{total} scaffold; needs source-grounded audit"
        return "needs source-grounded audit"
    return paper_coverage_label_from_counts(
        total=total,
        covered=covered,
        corrected_target_covered=int(summary.get("corrected_target_covered_count", 0)),
        conditional_boundary=int(summary.get("conditional_boundary_count", 0)),
        support_only=int(summary.get("support_only_count", 0)),
        support_only_required=int(
            summary.get("support_only_required_source_item_count", 0)
        ),
        out_of_scope=int(summary.get("out_of_scope_count", 0)),
        scope_exclusion=int(summary.get("user_approved_scope_exclusion_count", 0)),
        required_out_of_scope=int(summary.get("required_out_of_scope_count", 0)),
        partial=int(summary.get("partial_count", 0))
        + int(summary.get("missing_coverage_count", 0)),
        missing=int(summary.get("missing_count", 0)),
        uncertain=int(summary.get("uncertain_count", 0)),
        unknown=int(summary.get("unknown_count", 0)),
        stale=int(summary.get("stale_statement_count", 0))
        + (1 if summary.get("stale_inventory") else 0)
        + (1 if summary.get("stale_surface") else 0),
    )


def lean_loc(folder: Path) -> int:
    """Count all Lean lines in one paper folder, including proof modules."""

    total = 0
    for path in folder.rglob("*.lean"):
        with path.open(encoding="utf-8") as handle:
            total += sum(1 for _line in handle)
    return total


def component_loc(paths: list[str]) -> int:
    files: set[Path] = set()
    for raw_path in paths:
        path = ROOT / raw_path
        if path.is_dir():
            files.update(path.rglob("*.lean"))
        elif path.is_file() and path.suffix == ".lean":
            files.add(path)
    total = 0
    for path in sorted(files):
        with path.open(encoding="utf-8") as handle:
            total += sum(1 for _line in handle)
    return total


def human_note(payload: dict[str, Any]) -> str:
    # Public copy has a separate maintainer-owned source. A paper closeout or
    # merge may refresh status metadata without replacing that approved prose.
    overrides = CATALOG_PAYLOAD.get("public_summary_overrides", {})
    if not isinstance(overrides, dict) or any(
        not isinstance(value, str) for value in overrides.values()
    ):
        raise ValueError("public_summary_overrides must map paper IDs to exact text")
    if payload.get("id") in overrides:
        return overrides[payload["id"]]
    note = payload.get("human_summary")
    review = human_summary_review(payload)
    # A status record can retain an agent-authored draft for internal editing,
    # but aggregate/public-facing status must not present that draft as a paper
    # summary.  The record itself stays untouched, so changing presentation
    # policy does not invalidate a closeout receipt that pins status bytes.
    # A user-authored status note may predate the current `human_approved`
    # vocabulary.  `human_written` has the same ownership protection: render
    # it verbatim rather than silently falling back to an implementation-facing
    # caveat.  Agent drafts remain private until a human explicitly approves
    # them.
    if isinstance(note, str) and (
        review is None
        or review.get("status", "").lower()
        in {"human_approved", "human_written"}
    ):
        return note
    if payload.get("status") == "formalized":
        return ""
    return str(payload.get("main_caveat", ""))


def human_summary_review(payload: dict[str, Any]) -> dict[str, str] | None:
    raw = payload.get("human_summary_review")
    if not isinstance(raw, dict):
        return None
    status = raw.get("status")
    if not isinstance(status, str) or not status.strip():
        return None
    review: dict[str, str] = {"status": status.strip()}
    note = raw.get("note")
    if isinstance(note, str) and note.strip():
        review["note"] = note.strip()
    return review


def human_status_rows(
    records: list[tuple[Path, dict[str, Any]]],
    *,
    use_dashboard_audit: bool = False,
    dashboard_audit_paper: str | None = None,
    lean_loc_by_folder: Mapping[Path, int] | None = None,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for folder, payload in records:
        publication, year = publication_for(payload)
        audit_this_paper = use_dashboard_audit and (
            dashboard_audit_paper is None or folder.name == dashboard_audit_paper
        )
        # Import-closure identity providers cache every transitive module they
        # inspect.  Status sync spans the whole repository, so sharing one
        # provider across papers can retain an unbounded union of closures.
        # A fresh, frozen provider per paper preserves the no-change check
        # while keeping aggregate-site rendering bounded.
        closure_provider = (
            None
            if use_dashboard_audit and dashboard_audit_paper is None
            else LazySharedClosureProvider(ROOT)
        )
        build_input_provider = LazySharedBuildInputSnapshotProvider(ROOT)
        review_surface_provider = ReviewSurfaceProvider(
            folder,
            use_dashboard_audit=audit_this_paper,
            closure_provider=closure_provider,
            build_input_provider=build_input_provider,
        )
        reuse_authorization = review_surface_provider.authorize_saved_sidecar_reuse(
            payload
        )
        expected_human_total = paper_facing_human_review_total(folder, payload)
        if expected_human_total is None and reuse_authorization.available and isinstance(
            reuse_authorization.statement_counts, dict
        ):
            expected_human_total = int(
                reuse_authorization.statement_counts["total"]
            ) + int(reuse_authorization.statement_counts["source_condition_rows"])
        human_counts = validated_human_review_counts(
            payload,
            expected_total=expected_human_total,
        )
        row = {
            "id": payload["id"],
            "title": payload["title"],
            "authors": payload["authors"],
            "publication": publication,
            "publication_year": year,
            "source_url": source_url_for(payload),
            "paper_info": f"{payload['title']} by {payload['authors']}; {publication}.",
            "status": human_status_label(str(payload["status"]), paper_id=payload["id"]),
            "human_review": human_review_label(payload, counts=human_counts),
            "human_translation": human_translation_label(payload, counts=human_counts),
            "llm_as_judge_translation": llm_translation_label(
                folder,
                payload,
                use_dashboard_audit=audit_this_paper,
                review_surface_provider=review_surface_provider,
            ),
            "llm_as_judge_paper_coverage": llm_paper_coverage_label(
                folder,
                payload,
                use_dashboard_audit=audit_this_paper,
                review_surface_provider=review_surface_provider,
            ),
            "lean_loc": (
                lean_loc_by_folder[folder]
                if lean_loc_by_folder is not None
                else lean_loc(folder)
            ),
            "main_note": human_note(payload),
            "main_note_citation": note_citation(payload),
            "main_note_review": human_summary_review(payload),
            "paper_folder": str(folder.relative_to(ROOT)),
            "review_entrypoint": payload["review_entrypoint"],
            "artifacts": payload.get("artifacts", {}),
        }
        rows.append(row)
        if not build_input_provider.finalize_unchanged():
            raise RuntimeError(
                "repository build inputs changed during cached status rendering; "
                "discarding the run"
            )
        closure_problems = (
            closure_provider.finalization_problems()
            if closure_provider is not None
            else ()
        )
        if closure_problems:
            details = "; ".join(
                problem.format() if hasattr(problem, "format") else str(problem)
                for problem in closure_problems[:3]
            )
            raise RuntimeError(
                "Lean import-closure inputs changed during saved-status rendering; "
                f"discarding the run ({details})"
            )

    rows.sort(
        key=lambda row: (
            STATUS_GROUPS.get(str(row["status"]).lower(), 2),
            int(row["publication_year"]),
            str(row["title"]).lower(),
        )
    )
    return rows


def human_payload(
    records: list[tuple[Path, dict[str, Any]]],
    *,
    use_dashboard_audit: bool = False,
    dashboard_audit_paper: str | None = None,
    lean_loc_by_folder: Mapping[Path, int] | None = None,
) -> dict[str, Any]:
    return {
        "schema": 1,
        "description": (
            "Compact public-facing status generated from public paper-local status.json files. "
            "Use papers/status.json for detailed machine/audit metadata, including private-only papers."
        ),
        "generated_by": "python3 scripts/sync_paper_status.py",
        "sort_policy": (
            "Checked papers normally display as Formalized; designated unfinished papers "
            "retain Partially formalized. Status groups are ordered by publication year. "
            "Internal audit dispositions remain in papers/status.json."
        ),
        "note_policy": (
            "main_note is intentionally sparse. Formalization gap notes identify substantial "
            "extra assumptions, simplifications, or missing conclusions by source result; "
            "ordinary clarifications and minor technical restrictions stay in reports."
        ),
        "review_count_policy": (
            "human_review counts saved human source-claim dashboard rows as reviewed/total. "
            "Paired transparent specifications and their proving theorems count once; agent audits are not human review."
        ),
        "translation_status_policy": (
            "human_translation reports saved human dashboard judgments. "
            "llm_as_judge_translation reports context-free Lean-to-TeX plus "
            "paper-vs-translation LLM-judge counts, including stale/missing/uncertain "
            "flags when available; accepted conditional-boundary mismatches are shown "
            "as formalization-boundary statement rows and explicit assumption/source "
            "conditions are shown as source-condition rows so totals reconcile with "
            "the human-review surface. llm_as_judge_paper_coverage reports the "
            "paper-level source-inventory-to-dashboard-row coverage audit. For an "
            "formalized target that differs from the archive and has a current pinned semantic contract, "
            "both generated labels identify that contract rather than stale archive-only "
            "LLM sidecars."
        ),
        "lean_loc_policy": (
            "lean_loc sums all .lean files under each paper folder, including proof "
            "modules. It is not the PaperInterface.lean line count."
        ),
        "identifier_policy": (
            "Paper IDs and folder names are stable artifact identifiers and may track an arXiv, "
            "conference, or original working-paper year. Publication fields use the published "
            "citation title and year."
        ),
        "papers": human_status_rows(
            public_dashboard_records(records),
            use_dashboard_audit=use_dashboard_audit,
            dashboard_audit_paper=dashboard_audit_paper,
            lean_loc_by_folder=lean_loc_by_folder,
        ),
    }


def md_escape(text: str) -> str:
    return " ".join(text.split()).replace("|", r"\|")


def md_note_with_citation(note: str, citation: dict[str, str] | None) -> str:
    note = md_escape(note)
    if not citation:
        return note
    label = md_escape(citation["label"])
    url = citation["url"]
    rendered_citation = f"[{label}]({url})"
    if note.endswith("."):
        return f"{note[:-1]} {rendered_citation}."
    return f"{note} {rendered_citation}"


def repo_relative_link(path: str) -> str:
    return f"../{path}"


def readme_note(payload: dict[str, Any]) -> str:
    return md_note_with_citation(human_note(payload), note_citation(payload))


def relative_markdown_path(from_dir: Path, repo_relative_path: str) -> str:
    target = (ROOT / repo_relative_path).resolve()
    return os.path.relpath(target, start=from_dir.resolve()).replace(os.sep, "/")


def markdown_file_link(from_dir: Path, repo_relative_path: str, label: str) -> str:
    return (
        f"[{md_escape(label)}]({relative_markdown_path(from_dir, repo_relative_path)})"
    )


def paper_file_if_present(folder: Path, repo_relative_path: str | None) -> str | None:
    if not isinstance(repo_relative_path, str) or not repo_relative_path.strip():
        return None
    candidate = ROOT / repo_relative_path.strip()
    if candidate.exists() and candidate.is_file():
        return repo_relative_path.strip()
    return None


def first_present_artifact(
    folder: Path, payload: dict[str, Any], *keys: str
) -> str | None:
    artifacts = payload.get("artifacts", {})
    if isinstance(artifacts, dict):
        for key in keys:
            path = paper_file_if_present(folder, artifacts.get(key))
            if path:
                return path
    return None


def review_entrypoint_path(folder: Path, payload: dict[str, Any]) -> str | None:
    path = paper_file_if_present(folder, str(payload.get("review_entrypoint", "")))
    if path:
        return path
    return first_present_artifact(folder, payload, "final_validation_report")


def dependency_dag_path(folder: Path, payload: dict[str, Any]) -> str | None:
    configured = first_present_artifact(
        folder, payload, "dependency_dag_pdf", "dependency_dag_tex"
    )
    if configured:
        return configured
    for name in ("DependencyDAG.pdf", "DependencyDAG.tex"):
        default = folder / "docs" / name
        if default.is_file():
            return str(default.relative_to(ROOT))
    return None


def human_review_packet_path(folder: Path, payload: dict[str, Any]) -> str | None:
    """Return the durable, mark-up-friendly review packet when present.

    The status artifact is the release declaration.  The paper-local fallback
    keeps a freshly generated packet visible before the next status sync, but
    never invents a path when the artifact has not actually been generated.
    """

    configured = first_present_artifact(
        folder,
        payload,
        "human_review_packet_pdf",
        "human_review_packet_tex",
    )
    if configured:
        return configured
    default = folder / "docs" / "HUMAN_REVIEW_PACKET.pdf"
    if default.is_file():
        return str(default.relative_to(ROOT))
    return None


def paper_interface_path(folder: Path, payload: dict[str, Any]) -> str | None:
    interface = payload.get("paper_interface", {})
    if isinstance(interface, dict):
        path = paper_file_if_present(folder, interface.get("path"))
        if path:
            return path
    return first_present_artifact(folder, payload, "paper_interface")


def audit_surface_path(folder: Path, payload: dict[str, Any]) -> str | None:
    status = payload.get("status")
    if isinstance(status, str) and status in CLOSEOUT_STATUSES:
        return None
    interface = payload.get("paper_interface", {})
    if isinstance(interface, dict):
        return paper_file_if_present(folder, interface.get("audit_surface_path"))
    return None


def resolve_paper_local_route(folder: Path, raw_path: str) -> Path:
    path = Path(raw_path.strip())
    if path.is_absolute():
        return path
    if len(path.parts) == 1:
        return folder / path
    return ROOT / path


def display_repo_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT.resolve()))
    except ValueError:
        return str(path)


def validate_review_surface_routes(
    records: list[tuple[Path, dict[str, Any]]],
) -> list[str]:
    """Reject stale alternate human-review surfaces before rendering status files."""

    errors: list[str] = []
    for folder, payload in records:
        paper_id = str(payload.get("id", folder.name))
        status = payload.get("status")
        requires_closeout_route = (
            isinstance(status, str) and status in CLOSEOUT_STATUSES
        )
        canonical = folder / "PaperInterface.lean"
        if not canonical.exists():
            errors.append(
                f"{paper_id}: missing canonical review surface {display_repo_path(canonical)}"
            )
        interface = payload.get("paper_interface", {})
        if isinstance(interface, dict):
            raw_interface = interface.get("path")
            if isinstance(raw_interface, str) and raw_interface.strip():
                interface_path = resolve_paper_local_route(folder, raw_interface)
                if interface_path.resolve() != canonical.resolve():
                    errors.append(
                        f"{paper_id}: paper_interface.path must be "
                        f"{display_repo_path(canonical)}, got {display_repo_path(interface_path)}"
                    )
            raw_audit_surface = interface.get("audit_surface_path")
            if (
                requires_closeout_route
                and isinstance(raw_audit_surface, str)
                and raw_audit_surface.strip()
            ):
                errors.append(
                    f"{paper_id}: paper_interface.audit_surface_path is obsolete; "
                    "the review surface must be PaperInterface.lean"
                )

        review_surface = payload.get("review_surface", {})
        if requires_closeout_route and isinstance(review_surface, dict):
            for key in ("source_file", "human_source_file"):
                raw_source = review_surface.get(key)
                if isinstance(raw_source, str) and raw_source.strip():
                    source_path = resolve_paper_local_route(folder, raw_source)
                    if source_path.resolve() != canonical.resolve():
                        errors.append(
                            f"{paper_id}: review_surface.{key} must be "
                            f"{display_repo_path(canonical)}, got {display_repo_path(source_path)}"
                        )
    return errors


def json_surface_paths(folder: Path) -> list[tuple[str, str]]:
    """Link stable reader entrypoints without presenting historical sidecars as current."""
    candidates = [
        ("status.json", folder / "status.json"),
        ("paper statement map", folder / "audit" / "paper_statement_map.json"),
    ]
    seen_labels: set[str] = set()
    out: list[tuple[str, str]] = []
    for label, path in candidates:
        if label in seen_labels:
            continue
        if path.exists() and path.is_file():
            seen_labels.add(label)
            out.append((label, str(path.relative_to(ROOT))))
    return out


def paper_reference_markdown(folder: Path, payload: dict[str, Any]) -> str:
    publication, _year = publication_for(payload)
    title = md_escape(str(payload.get("title", payload["id"])))
    source_url = source_url_for(payload)
    if source_url:
        title = f"[{title}]({source_url})"
    return f"{title} by {md_escape(str(payload.get('authors', '')))}; {md_escape(publication)}."


def generated_paper_readme_block(
    folder: Path,
    payload: dict[str, Any],
    *,
    lean_line_count: int | None = None,
) -> str:
    review_path = review_entrypoint_path(folder, payload)
    dag_path = dependency_dag_path(folder, payload)
    packet_path = human_review_packet_path(folder, payload)
    interface_path = paper_interface_path(folder, payload)
    audit_path = audit_surface_path(folder, payload)
    if folder == ROOT / "papers" / "TEMPLATE":
        notes_path = str((folder / TEMPLATE_README_PLAN).relative_to(ROOT))
        notes_label = "Formalization plan"
        include_notes = (ROOT / notes_path).exists()
    else:
        notes_path = str((folder / LEGACY_README_NOTES).relative_to(ROOT))
        notes_label = "Additional documentation"
        include_notes = (ROOT / notes_path).exists() or legacy_readme_body(
            folder
        ) is not None
    corrected_scope = author_approved_corrected_scope(payload)
    explicit_source_clarifications = first_present_artifact(
        folder, payload, "source_clarifications"
    )
    json_links = [
        markdown_file_link(folder, path, label)
        for label, path in json_surface_paths(folder)
    ]

    link_lines = []
    if review_path:
        review_label = (
            "Agent source audit"
            if str(payload.get("status", "")).strip().lower() == "paper draft"
            else "Final validation report"
        )
        link_lines.append(
            f"- {review_label}: {markdown_file_link(folder, review_path, Path(review_path).name)}"
        )
    else:
        review_label = (
            "Agent source audit"
            if str(payload.get("status", "")).strip().lower() == "paper draft"
            else "Final validation report"
        )
        link_lines.append(f"- {review_label}: not tracked in this folder.")
    source_clarifications = (
        [explicit_source_clarifications]
        if explicit_source_clarifications is not None
        else []
    )
    if not source_clarifications:
        for memo_name in (
            "SOURCE_CLARIFICATIONS.md",
            "SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md",
        ):
            memo_path = folder / "docs" / memo_name
            if memo_path.is_file():
                source_clarifications.append(str(memo_path.relative_to(ROOT)))
    for source_clarification in source_clarifications:
        source_clarifications_label = (
            "Source clarifications and assumptions"
            if explicit_source_clarifications is not None
            and corrected_scope is not None
            else "Source clarifications and formalized scope"
        )
        link_lines.append(
            f"- {source_clarifications_label}: "
            + markdown_file_link(
                folder,
                source_clarification,
                Path(source_clarification).name,
            )
        )
    if dag_path:
        link_lines.append(
            f"- Dependency DAG: {markdown_file_link(folder, dag_path, Path(dag_path).name)}"
        )
    else:
        link_lines.append("- Dependency DAG: not tracked in this folder.")
    if packet_path:
        link_lines.append(
            "- Human review packet: "
            + markdown_file_link(folder, packet_path, Path(packet_path).name)
        )
    if interface_path:
        link_lines.append(
            f"- Compact Lean interface: {markdown_file_link(folder, interface_path, Path(interface_path).name)}"
        )
    else:
        link_lines.append("- Compact Lean interface: not tracked in this folder.")
    if audit_path:
        link_lines.append(
            f"- Audited review surface: {markdown_file_link(folder, audit_path, Path(audit_path).name)}"
        )
    if corrected_scope is not None:
        artifacts = payload.get("artifacts")
        if isinstance(artifacts, dict):
            governing_model = artifacts.get("governing_corrected_model")
            if (
                explicit_source_clarifications is None
                and isinstance(governing_model, str)
                and (ROOT / governing_model).is_file()
            ):
                link_lines.append(
                    "- Governing corrected model: "
                    + markdown_file_link(
                        folder, governing_model, Path(governing_model).name
                    )
                )
            semantic_contract = artifacts.get("corrected_model_semantic_contract")
            if (
                isinstance(semantic_contract, str)
                and (ROOT / semantic_contract).is_file()
            ):
                link_lines.append(
                    "- Corrected-model semantic contract: "
                    + markdown_file_link(
                        folder, semantic_contract, Path(semantic_contract).name
                    )
                )
    link_lines.append("- Source/status JSON: " + "; ".join(json_links) + ".")
    if include_notes:
        link_lines.append(
            f"- {notes_label}: {markdown_file_link(folder, notes_path, Path(notes_path).name)}"
        )

    lines = [
        PAPER_README_BEGIN,
        f"# {str(payload.get('title', payload['id'])).strip()}",
        "",
        "| Field | Value |",
        "|---|---|",
        f"| Final status | {md_escape(status_label(str(payload['status'])))} |",
        *(
            [
                "| Scope note | The formalized model differs from the pinned archive; the report details the changes |"
            ]
            if corrected_scope is not None
            else []
        ),
        f"| Paper reference | {paper_reference_markdown(folder, payload)} |",
        f"| Lines of Code | {(lean_loc(folder) if lean_line_count is None else lean_line_count):,} |",
        "",
        "## Key Links",
        "",
        *link_lines,
        PAPER_README_END,
        "",
    ]
    return "\n".join(lines)


def legacy_readme_body(folder: Path) -> str | None:
    current_path = folder / "README.md"
    if not current_path.exists():
        return None
    current = current_path.read_text(encoding="utf-8")
    start = current.find(PAPER_README_BEGIN)
    stop = current.find(PAPER_README_END)
    if start >= 0 or stop >= 0:
        if start < 0 or stop < 0 or stop < start:
            raise ValueError(
                f"{current_path.relative_to(ROOT)} has malformed generated README markers"
            )
        stop += len(PAPER_README_END)
        body = current[stop:].strip()
    else:
        body = current.strip()
    return body or None


def render_legacy_readme_notes(folder: Path) -> tuple[Path, str] | None:
    notes_path = folder / LEGACY_README_NOTES
    if notes_path.exists():
        return None
    body = legacy_readme_body(folder)
    if body is None:
        return None
    rendered = "\n".join(
        [
            "# Formalization Notes",
            "",
            "This file preserves the previous hand-written paper-folder README content.",
            "The paper-folder `README.md` is now a generated status overview.",
            "",
            body,
            "",
        ]
    )
    return notes_path, rendered


def render_paper_readme(
    folder: Path,
    payload: dict[str, Any],
    *,
    lean_line_count: int | None = None,
) -> str:
    return generated_paper_readme_block(
        folder,
        payload,
        lean_line_count=lean_line_count,
    )


def write_output_if_changed(path: Path, rendered: str) -> bool:
    """Write one generated artifact only when its exact text changed."""

    current = path.read_text(encoding="utf-8") if path.exists() else None
    if current == rendered:
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(rendered, encoding="utf-8")
    return True


def render_paper_status_md(payload: dict[str, Any]) -> str:
    lines = [
        "# Paper Status",
        "",
        "This file is generated by `python3 scripts/sync_paper_status.py` from",
        "paper-local `papers/<PaperName>/status.json` files. Edit those sources",
        "rather than this table.",
        "",
        "The table is intentionally public-facing. `Note` is blank for",
        "formalized papers unless a source-version, proof-route, or remaining-boundary",
        "note is useful to a public reader. For detailed machine-readable metadata,",
        "see [`papers/status.json`](../papers/status.json); for the compact public",
        "JSON, see [`papers/human_status.json`](../papers/human_status.json).",
        "Paper-local records marked `repository_visibility: private_only` remain",
        "in the aggregate private index but are excluded from this public table.",
        "",
        "Human-review counts are dashboard rows saved by a human reviewer; agent",
        "source audits are not counted as human review.",
        "",
        "Paper IDs and folder names are stable artifact identifiers and may track",
        "an arXiv, conference, or original working-paper year. The table below uses",
        "the published citation title and year.",
        "",
        "| Paper, authors, publication | Status | Human review | Paper coverage | Lines of Code | Public note |",
        "|---|---|---:|---:|---:|---|",
    ]
    for row in payload["papers"]:
        paper_href = row["source_url"] or repo_relative_link(row["paper_folder"])
        paper_link = f"[{md_escape(row['title'])}]({paper_href})"
        paper_info = (
            f"{paper_link} by {md_escape(row['authors'])}; "
            f"{md_escape(row['publication'])}."
        )
        status_link = f"[{md_escape(row['status'])}]({repo_relative_link(row['review_entrypoint'])})"
        lines.append(
            "| "
            + " | ".join(
                [
                    paper_info,
                    status_link,
                    md_escape(row["human_review"]),
                    md_escape(row["llm_as_judge_paper_coverage"]),
                    f"{int(row['lean_loc']):,}",
                    md_note_with_citation(
                        row["main_note"], row.get("main_note_citation")
                    ),
                ]
            )
            + " |"
        )
    lines.extend(
        [
            "",
            "For status vocabulary, see [`docs/STATUS.md`](STATUS.md).",
            "",
        ]
    )
    return "\n".join(lines)


def html_escape(text: object) -> str:
    return html.escape(str(text), quote=True)


def github_link(path: str) -> str:
    return GITHUB_MAIN + path


def local_artifact_link(path: str) -> str:
    """Return the localhost-only route for one repo-relative paper artifact."""

    return LOCAL_ARTIFACT_PREFIX + quote(path.lstrip("/"), safe="/")


def artifact_anchor(label: str, path: str) -> str:
    """Render a public link with a localhost-only artifact override."""

    return (
        f'<a href="{html_escape(github_link(path))}" '
        f'data-local-artifact-href="{html_escape(local_artifact_link(path))}">'
        f"{html_escape(label)}</a>"
    )


def html_note_with_citation(note: str, citation: dict[str, str] | None) -> str:
    rendered = html_escape(note)
    if not citation:
        return rendered
    label = html_escape(citation["label"])
    url = html_escape(citation["url"])
    rendered_citation = f'<a href="{url}">{label}</a>'
    if rendered.endswith("."):
        return f"{rendered[:-1]} {rendered_citation}."
    return f"{rendered} {rendered_citation}"


def site_paper_artifact_links(row: dict[str, Any]) -> str:
    repository_url = GITHUB_MAIN_TREE + "papers/" + quote(row["id"], safe="")
    folder = ROOT / "papers" / row["id"]
    links = [artifact_anchor("Report", row["review_entrypoint"])]
    artifacts = row.get("artifacts")
    if isinstance(artifacts, dict):
        interface = artifacts.get("paper_interface")
        if isinstance(interface, str) and interface.strip():
            links.append(artifact_anchor("Lean statements", interface.strip()))
        dag = artifacts.get("dependency_dag_pdf")
        default_dag = folder / "docs" / "DependencyDAG.pdf"
        if not dag and default_dag.is_file():
            dag = str(default_dag.relative_to(ROOT))
        dag = dag or artifacts.get("dependency_dag_tex")
        if isinstance(dag, str) and dag.strip():
            links.append(artifact_anchor("Dependency map", dag.strip()))
        packet = (
            artifacts.get("human_review_packet_pdf")
            or artifacts.get("human_review_packet_tex")
            or human_review_packet_path(folder, row)
        )
        if isinstance(packet, str) and packet.strip():
            links.append(artifact_anchor("Review packet", packet.strip()))
    links.append(f'<a href="{html_escape(repository_url)}">Repo</a>')
    return '<div class="artifact-links">' + " ".join(links) + "</div>"


def render_site_library_block(human: dict[str, Any]) -> str:
    indent = " " * 14
    lines = [f"{indent}{SITE_LIBRARY_BEGIN}"]
    for component in LIBRARY_COMPONENTS:
        title = html_escape(component["title"])
        paths = component["paths"]
        if paths:
            title = f'<a href="{html_escape(github_link(paths[0]))}">{title}</a>'
        lines.extend(
            [
                f"{indent}<tr>",
                f"{indent}  <td>{title}</td>",
                f"{indent}  <td>{html_escape(component['examples'])}</td>",
                f"{indent}  <td>{component_loc(component['paths']):,}</td>",
                f"{indent}</tr>",
            ]
        )
    lines.append(f"{indent}{SITE_LIBRARY_END}")
    return "\n".join(lines)


def render_site_stats_block(payload: dict[str, Any]) -> str:
    indent = " " * 8
    papers = payload["papers"]
    formalized = sum(1 for row in papers if str(row["status"]).startswith("Formalized"))
    partial = sum(1 for row in papers if row["status"] == "Partially formalized")
    partial_noun = "paper" if partial == 1 else "papers"
    partial_text = f" and {partial} partially formalized {partial_noun}" if partial else ""
    lean_loc = sum(int(row["lean_loc"]) for row in papers)
    # Count shared code once at its owner, not once per importing paper.
    # Per-paper row counts omit their sibling root module; include those here.
    lean_loc += component_loc(
        ["AppliedModelingLib", "AppliedModelingLib.lean"]
        + [f"papers/{row['id']}.lean" for row in papers if row.get("id")]
    )
    lines = [
        f"{indent}{SITE_STATS_BEGIN}",
        f'{indent}<p class="project-stats">',
        (
            f"{indent}  Currently, the project contains {formalized} formalized papers{partial_text}, "
            f"with {lean_loc:,} total "
            "lines of Lean code."
        ),
        f"{indent}</p>",
        f"{indent}{SITE_STATS_END}",
    ]
    return "\n".join(lines)


def render_site_status_block(payload: dict[str, Any]) -> str:
    indent = " " * 14
    lines = [f"{indent}{SITE_STATUS_BEGIN}"]
    for row in payload["papers"]:
        paper_href = row["source_url"] or github_link(row["paper_folder"])
        note = html_note_with_citation(row["main_note"], row.get("main_note_citation"))
        notes_cell = site_paper_artifact_links(row)
        if note:
            notes_cell += f'<p class="paper-note">{note}</p>'
        lines.extend(
            [
                f"{indent}<tr>",
                f"{indent}  <td>",
                (
                    f'{indent}    <a class="paper-source" href="{html_escape(paper_href)}">'
                    f"<cite>{html_escape(row['title'])}</cite></a> by"
                ),
                (
                    f"{indent}    {html_escape(row['authors'])}; "
                    f"{html_escape(row['publication'])}."
                ),
                f"{indent}  </td>",
                f"{indent}  <td>{html_escape(row['status'])}</td>",
                f"{indent}  <td>{html_escape(str(row['human_review']))}</td>",
                f"{indent}  <td>{int(row['lean_loc']):,}</td>",
                f"{indent}  <td>{notes_cell}</td>",
                f"{indent}</tr>",
            ]
        )
    lines.append(f"{indent}{SITE_STATUS_END}")
    return "\n".join(lines)


def render_site_index(payload: dict[str, Any]) -> str:
    current = SITE_INDEX.read_text(encoding="utf-8")
    library_block = render_site_library_block(payload)
    library_start = current.find(SITE_LIBRARY_BEGIN)
    library_end = current.find(SITE_LIBRARY_END)
    if library_start >= 0 and library_end >= library_start:
        library_end += len(SITE_LIBRARY_END)
        line_start = current.rfind("\n", 0, library_start) + 1
        line_end = current.find("\n", library_end)
        if line_end < 0:
            current = current[:line_start] + library_block
        else:
            current = current[:line_start] + library_block + current[line_end:]

    stats_block = render_site_stats_block(payload)
    stats_start = current.find(SITE_STATS_BEGIN)
    stats_end = current.find(SITE_STATS_END)
    if stats_start >= 0 and stats_end >= stats_start:
        stats_end += len(SITE_STATS_END)
        line_start = current.rfind("\n", 0, stats_start) + 1
        line_end = current.find("\n", stats_end)
        if line_end < 0:
            current = current[:line_start] + stats_block
        else:
            current = current[:line_start] + stats_block + current[line_end:]

    block = render_site_status_block(payload)
    start = current.find(SITE_STATUS_BEGIN)
    end = current.find(SITE_STATUS_END)
    if start >= 0 and end >= start:
        end += len(SITE_STATUS_END)
        line_start = current.rfind("\n", 0, start) + 1
        line_end = current.find("\n", end)
        if line_end < 0:
            return current[:line_start] + block
        return current[:line_start] + block + current[line_end:]

    tbody_start = current.find("<tbody>")
    if tbody_start < 0:
        raise ValueError(
            f"{SITE_INDEX.relative_to(ROOT)} should contain a paper status <tbody>"
        )
    tbody_open_end = current.find(">", tbody_start)
    tbody_end = current.find("</tbody>", tbody_open_end)
    if tbody_open_end < 0 or tbody_end < 0:
        raise ValueError(
            f"{SITE_INDEX.relative_to(ROOT)} should contain a complete paper status <tbody>"
        )
    return (
        current[: tbody_open_end + 1]
        + "\n"
        + block
        + "\n            "
        + current[tbody_end:]
    )


def assert_required_static_site_copy(rendered: str) -> None:
    missing = [
        label
        for label, required in SITE_REQUIRED_STATIC_COPY.items()
        if required not in rendered
    ]
    if missing:
        joined = ", ".join(missing)
        raise ValueError(
            f"{SITE_INDEX.relative_to(ROOT)} is missing required static site copy: {joined}"
        )


def one_paper_local_status_outputs(
    paper_id: str,
) -> tuple[dict[Path, str], list[str]]:
    """Render and validate one paper-owned status surface.

    Aggregate JSON, Markdown, and site files are deliberately absent. The
    default all-paper sync remains their integration/release authority.
    """

    folder = resolve_paper_folder(ROOT, paper_id)
    if folder is None or not (folder / "status.json").is_file():
        return {}, [f"unknown paper folder: {paper_id}"]
    try:
        payload = load_paper_status(folder)
        repository_visibility(payload)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        return {}, [str(exc)]
    route_errors = validate_review_surface_routes([(folder, payload)])
    if route_errors:
        return {}, route_errors

    problems: list[str] = []
    try:
        validated_human_review_counts(payload)
    except ValueError as exc:
        problems.append(f"invalid target-paper human review counts: {exc}")

    local_outputs: dict[Path, str] = {
        folder / "README.md": render_paper_readme(
            folder,
            payload,
            lean_line_count=lean_loc(folder),
        )
    }
    legacy_notes = render_legacy_readme_notes(folder)
    if legacy_notes is not None:
        local_outputs[legacy_notes[0]] = legacy_notes[1]
    return local_outputs, problems


def check_one_paper_generated_status(
    paper_id: str,
) -> list[str]:
    """Check one paper-owned projection without traversing the inventory."""

    local_outputs, problems = one_paper_local_status_outputs(paper_id)
    for path, rendered in local_outputs.items():
        current = path.read_text(encoding="utf-8") if path.exists() else ""
        if current != rendered:
            problems.append(f"{path.relative_to(ROOT)} is out of sync")
    return problems


def aggregate_only_status_outputs() -> dict[Path, str]:
    """Render exactly the four repository-wide projection files.

    This path intentionally omits every paper README and legacy note. It reads
    accepted paper-local status and saved receipts, but does not build Lean,
    refresh audit evidence, or invoke a dashboard audit.
    """

    records = paper_records()
    route_errors = validate_review_surface_routes(records)
    if route_errors:
        raise ValueError(
            "paper review-surface route validation failed: " + "; ".join(route_errors)
        )
    aggregate = aggregate_payload(records)
    lean_loc_by_folder = {folder: lean_loc(folder) for folder, _payload in records}
    human = human_payload(records, lean_loc_by_folder=lean_loc_by_folder)
    outputs = {
        AGGREGATE_STATUS: json.dumps(aggregate, indent=2, ensure_ascii=False) + "\n",
        HUMAN_STATUS: json.dumps(human, indent=2, ensure_ascii=False) + "\n",
        DOCS_PAPER_STATUS: render_paper_status_md(human),
        SITE_INDEX: render_site_index(human),
    }
    assert_no_root_readme_outputs(outputs)
    assert_required_static_site_copy(outputs[SITE_INDEX])
    return outputs


def run_aggregate_only(*, check: bool) -> int:
    """Check or write only aggregate projections with distinct failure codes."""

    try:
        outputs = aggregate_only_status_outputs()
    except Exception as exc:  # The CLI treats malformed projection inputs uniformly.
        print(f"could not render aggregate status projection: {exc}")
        return 2

    if check:
        stale = [
            path.relative_to(ROOT)
            for path, rendered in outputs.items()
            if (path.read_text(encoding="utf-8") if path.exists() else "") != rendered
        ]
        if stale:
            print(
                "aggregate status projection is out of sync; run "
                "`python3 scripts/sync_paper_status.py --aggregate-only`"
            )
            for path in stale:
                print(f"- {path}")
            return 1
        print("aggregate-only status check passed")
        return 0

    changed = 0
    for path, rendered in outputs.items():
        if write_output_if_changed(path, rendered):
            changed += 1
            print(f"wrote {path.relative_to(ROOT)} from paper-local status files")
    print(f"aggregate-only status sync complete: {changed} changed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=ROOT,
        help="repository checkout to read or check (default: this script's repository)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if generated status files are out of sync",
    )
    parser.add_argument(
        "--include-untracked",
        action="store_true",
        help="also include untracked draft paper folders with status.json",
    )
    parser.add_argument(
        "--dashboard-audit",
        action="store_true",
        help=(
            "derive LLM statement-review counts through review_dashboard.py. "
            "This is slower and is the only mode permitted to invoke Lean; "
            "the default status sync reads tracked sidecars and verified caches only."
        ),
    )
    parser.add_argument(
        "--dashboard-paper",
        metavar="PAPER",
        help=(
            "with --dashboard-audit, re-audit only this paper and read tracked "
            "sidecars for all other aggregate rows"
        ),
    )
    parser.add_argument(
        "--paper",
        metavar="PAPER",
        help=(
            "render or check only this paper's owned README/legacy note and "
            "validate its local status metadata, without traversing or changing "
            "aggregate JSON, Markdown, or site files; this is a closeout mode, "
            "not the release-wide sync gate"
        ),
    )
    parser.add_argument(
        "--aggregate-only",
        action="store_true",
        help=(
            "render or check exactly the aggregate JSON, Markdown, and site "
            "projections; never render paper READMEs or run semantic audits"
        ),
    )
    args = parser.parse_args()

    if args.repo.resolve() != ROOT:
        parser.error("--repo must be resolved during process bootstrap")

    if args.dashboard_paper and not args.dashboard_audit:
        parser.error("--dashboard-paper requires --dashboard-audit")
    if args.paper and args.include_untracked:
        parser.error("--paper cannot be combined with --include-untracked")
    if args.paper and args.dashboard_paper:
        parser.error("--paper cannot be combined with --dashboard-paper")
    if args.paper and args.dashboard_audit:
        parser.error(
            "--paper is a paper-owned rendering mode and cannot run dashboard audits"
        )
    if args.aggregate_only and (
        args.paper
        or args.include_untracked
        or args.dashboard_audit
        or args.dashboard_paper
    ):
        parser.error(
            "--aggregate-only cannot be combined with paper, untracked, or dashboard modes"
        )

    if args.aggregate_only:
        return run_aggregate_only(check=args.check)

    if args.paper:
        if args.check:
            problems = check_one_paper_generated_status(args.paper)
            if problems:
                print(f"paper-local generated status is out of sync for `{args.paper}`")
                for problem in problems:
                    print(f"- {problem}")
                return 1
            print(f"paper-local generated status check passed for `{args.paper}`")
            return 0
        outputs, problems = one_paper_local_status_outputs(args.paper)
        if problems:
            print(f"could not render paper-local status for `{args.paper}`")
            for problem in problems:
                print(f"- {problem}")
            return 1
        changed = 0
        for path, rendered in outputs.items():
            if write_output_if_changed(path, rendered):
                changed += 1
                print(f"wrote {path.relative_to(ROOT)} from paper-local status")
        print(
            f"paper-local status sync complete: {changed} changed; aggregate "
            "status/docs/site deferred to integration or release"
        )
        return 0

    records = paper_records(include_untracked=args.include_untracked)
    if args.dashboard_paper and args.dashboard_paper not in {
        folder.name for folder, _payload in records
    }:
        parser.error(
            f"unknown tracked paper for --dashboard-paper: {args.dashboard_paper}"
        )
    route_errors = validate_review_surface_routes(records)
    if route_errors:
        print("paper review-surface route validation failed:")
        for error in route_errors:
            print(f"- {error}")
        return 1
    aggregate = aggregate_payload(records)
    lean_loc_by_folder = {folder: lean_loc(folder) for folder, _payload in records}
    human = human_payload(
        records,
        use_dashboard_audit=args.dashboard_audit,
        dashboard_audit_paper=args.dashboard_paper,
        lean_loc_by_folder=lean_loc_by_folder,
    )
    outputs = {
        AGGREGATE_STATUS: json.dumps(aggregate, indent=2, ensure_ascii=False) + "\n",
        HUMAN_STATUS: json.dumps(human, indent=2, ensure_ascii=False) + "\n",
        DOCS_PAPER_STATUS: render_paper_status_md(human),
        SITE_INDEX: render_site_index(human),
    }
    for folder, payload in records:
        legacy_notes = render_legacy_readme_notes(folder)
        if legacy_notes is not None:
            path, rendered = legacy_notes
            outputs[path] = rendered
        outputs[folder / "README.md"] = render_paper_readme(
            folder,
            payload,
            lean_line_count=lean_loc_by_folder[folder],
        )
    try:
        assert_no_root_readme_outputs(outputs)
        assert_root_readme_locked()
        assert_required_static_site_copy(outputs[SITE_INDEX])
    except ValueError as exc:
        print(exc)
        return 1
    if args.check:
        stale = []
        for path, rendered in outputs.items():
            current = path.read_text(encoding="utf-8") if path.exists() else ""
            if current != rendered:
                stale.append(path.relative_to(ROOT))
        if stale:
            print(
                "generated status files are out of sync; run `python3 scripts/sync_paper_status.py`"
            )
            for path in stale:
                print(f"- {path}")
            return 1
        return 0
    changed: list[Path] = []
    unchanged = 0
    for path, rendered in outputs.items():
        if write_output_if_changed(path, rendered):
            changed.append(path)
            print(f"wrote {path.relative_to(ROOT)} from paper-local status files")
        else:
            unchanged += 1
    print(f"status sync complete: {len(changed)} changed, {unchanged} unchanged")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
