#!/usr/bin/env python3
"""Tests for the standalone review-dashboard presentation boundary."""

from __future__ import annotations

import json
import unittest

from scripts import review_dashboard
from scripts import review_dashboard_html


class ReviewDashboardHtmlTests(unittest.TestCase):
    def test_module_loads_the_exact_tracked_template(self) -> None:
        self.assertEqual(
            review_dashboard_html.HTML_PAGE,
            review_dashboard_html.TEMPLATE_PATH.read_text(encoding="utf-8").strip(),
        )
        self.assertNotIn("HTML_PAGE", vars(review_dashboard))

    def test_static_render_replaces_only_declared_inputs(self) -> None:
        papers = [{"name": "Fixture", "claim": "x < y"}]
        rendered = review_dashboard.render_static_html(
            papers,
            'Reviewer <one> "quoted"',
            "audit/reviewer-trace.jsonl",
        )

        for placeholder in ("__USER__", "__LOG_PATH__", "__PAPERS__", "{user}"):
            self.assertNotIn(placeholder, rendered)
        self.assertIn(json.dumps(papers), rendered)
        self.assertIn("Reviewer &lt;one&gt; &quot;quoted&quot;", rendered)
        self.assertIn(json.dumps("audit/reviewer-trace.jsonl"), rendered)

    def test_template_renders_paper_local_prerequisites_with_source_views(self) -> None:
        """The browser must not discard the packet's paper-prerequisite lane."""

        template = review_dashboard_html.HTML_PAGE
        self.assertIn("human_review_paper_prerequisites", template)
        self.assertIn("Paper-specific semantic prerequisites", template)
        self.assertIn('reviewScope: "paper_prerequisite"', template)
        self.assertIn("Verbatim paper-source connection", template)

    def test_template_renders_settled_review_context_beside_source(self) -> None:
        template = review_dashboard_html.HTML_PAGE
        self.assertIn("approved_review_contexts", template)
        self.assertIn("approved_review_context_presentation", template)
        self.assertIn("contextSummaries[context.id]", template)
        self.assertIn("Settled source reading", template)
        self.assertIn("Approved additional assumptions", template)


if __name__ == "__main__":
    unittest.main()
