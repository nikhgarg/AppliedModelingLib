#!/usr/bin/env python3
"""Load and render the standalone review-dashboard HTML presentation."""

from __future__ import annotations

import html
import json
from pathlib import Path
from typing import Any


TEMPLATE_PATH = Path(__file__).with_name("review_dashboard_template.html")
HTML_PAGE = TEMPLATE_PATH.read_text(encoding="utf-8").strip()


def render_static_html(
    papers: list[dict[str, Any]], user: str, log_path: str
) -> str:
    """Insert the serialized review data into the presentation template."""

    payload = json.dumps(papers)
    return (
        HTML_PAGE.replace("__USER__", json.dumps(user))
        .replace("__LOG_PATH__", json.dumps(log_path))
        .replace("__PAPERS__", payload)
        .replace("{user}", html.escape(user, quote=True))
    )
