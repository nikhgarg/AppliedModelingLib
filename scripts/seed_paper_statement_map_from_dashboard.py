#!/usr/bin/env python3
"""Create a self-contained audit/paper_statement_map.json from dashboard rows.

This is a seeding helper, not a substitute for source reading.  It makes the
coverage audit concrete by materializing the current paper-facing review target
inventory with direct statement text, source URL metadata, and row-name aliases.
Agents should then compare this inventory against the actual paper source and
add missing source statements or mark out-of-scope items explicitly.
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import date
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PAPERS_DIR = ROOT / "papers"
CATALOG = PAPERS_DIR / "catalog.json"

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.review_dashboard import (  # noqa: E402
    PAPER_STATEMENT_MAP_FILE,
    review_items_for_paper,
)


def load_catalog_source_urls() -> dict[str, str]:
    if not CATALOG.exists():
        return {}
    payload = json.loads(CATALOG.read_text(encoding="utf-8"))
    raw = payload.get("source_url_overrides", {}) if isinstance(payload, dict) else {}
    if not isinstance(raw, dict):
        return {}
    return {
        str(paper_id): str(url).strip()
        for paper_id, url in raw.items()
        if str(url).strip()
    }


def load_status_title(folder: Path) -> str:
    path = folder / "status.json"
    if not path.exists():
        return folder.name
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return folder.name
    return str(payload.get("title") or folder.name)


def item_statement(item: Any) -> str:
    for value in (item.paper_statement, item.source_note, item.agent_statement, item.lean_statement):
        text = str(value or "").strip()
        if text:
            return text
    return f"Paper-facing dashboard statement for `{item.name}`."


def map_payload(folder: Path) -> dict[str, Any]:
    items = review_items_for_paper(folder, use_cache=True)
    source_url = load_catalog_source_urls().get(folder.name, "")
    return {
        "schema": 1,
        "paper": folder.name,
        "title": load_status_title(folder),
        "generated_at": date.today().isoformat(),
        "source_inventory_kind": "dashboard_seeded_preliminary",
        "source_curated": False,
        "source_coverage_mode": "named_theoretical_statements",
        "source_inventory_policy": (
            "Self-contained source-statement inventory seeded from the current "
            "paper-facing review dashboard after source PDF/text acquisition. "
            "Each row remains subject to the paper-level coverage LLM audit; "
            "add source statements not represented by dashboard rows or mark "
            "them out of scope explicitly. Do not treat this as a source-curated "
            "claim that every named paper statement has been found."
        ),
        "source_url": source_url,
        "items": {
            item.name: {
                "statement": item_statement(item),
                "source_url": source_url,
                "source_location": (
                    item.source_status
                    or item.source_note
                    or "paper-facing review target; exact source location to be refined"
                ),
                "aliases": [item.name],
            }
            for item in items
        },
    }


def paper_folders(paper: str | None) -> list[Path]:
    if paper:
        folder = PAPERS_DIR / paper
        if not folder.is_dir():
            raise SystemExit(f"unknown paper folder: {paper}")
        return [folder]
    return sorted(
        folder
        for folder in PAPERS_DIR.iterdir()
        if folder.is_dir() and folder.name != "TEMPLATE" and (folder / "PaperInterface.lean").exists()
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", default="", help="Optional paper folder to seed.")
    parser.add_argument("--write", action="store_true", help="Write audit/paper_statement_map.json.")
    parser.add_argument("--force", action="store_true", help="Overwrite an existing map.")
    args = parser.parse_args()
    for folder in paper_folders(args.paper or None):
        payload = map_payload(folder)
        path = folder / PAPER_STATEMENT_MAP_FILE
        print(f"{folder.name}: dashboard_rows={len(payload['items'])} map_exists={path.exists()}")
        if not args.write:
            continue
        if path.exists() and not args.force:
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
