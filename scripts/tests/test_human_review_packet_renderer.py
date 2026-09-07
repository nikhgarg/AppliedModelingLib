"""Pure packet rendering must not acquire or reinterpret review material."""

from pathlib import Path
from types import SimpleNamespace
from unittest import TestCase, mock

from scripts import human_review_packet_renderer as renderer
from scripts.closeout_document_gates import _packet_tex_currentness_text


class HumanReviewPacketRendererTests(TestCase):
    @staticmethod
    def _prepared_surface(source_url: str):
        row = ({
            "name": "Claim", "full_name": "Fixture.claimSpec",
            "verbatim_source_input": "Every source object has its property.",
            "semantic_expanded_statement": "∀ x, property x",
            "llm_match_current": True, "llm_match_judgment": "matches",
        }, (), "Fixture.claim")
        return SimpleNamespace(
            paper_dir=Path("/missing/papers/Fixture"),
            source_map={"source_url": source_url},
            status={}, surface_error="", claim_rows=(row,),
            claim_sections=(("", (row,)),), paper_prerequisites=(),
            library_prerequisites=(),
        )

    def test_prose_preserves_mathematical_alphabet_glyphs_with_a_capable_font(self):
        rendered = renderer._tex_breakable_text("f: 𝓧→{0,1}; x_1 ∈ ℝ; loss ℓ")
        self.assertIn(r"{\fontspec{Latin Modern Math}𝓧}", rendered)
        self.assertIn(r"{\fontspec{Latin Modern Math}ℓ}", rendered)
        self.assertIn(r"→\{0,1\}", rendered)
        self.assertIn(r"x\_\allowbreak{}1 ∈ ℝ", rendered)
        self.assertNotIn(r"\fontspec{Latin Modern Math}x", rendered)

    def test_long_lean_identifiers_break_at_camel_case_without_changing_text(self):
        name = (
            "Fixture.SLA2026BoroughQueueingInput."
            "taggedAdmittedFiniteGPSHorizonFenceTargetCompletions"
        )
        rendered = renderer._tex_identifier(name)
        self.assertEqual(rendered.replace(r"\allowbreak{}", ""), name)
        self.assertIn(r"Finite\allowbreak{}GPS\allowbreak{}Horizon", rendered)
        self.assertIn(r"SLA2026\allowbreak{}Borough", rendered)
        self.assertNotIn(r"GP\allowbreak{}S", rendered)
        self.assertEqual(
            renderer._tex_identifier("x_1&alpha").replace(r"\allowbreak{}", ""),
            r"x\_1\&alpha",
        )

    def test_identifier_breaks_preserve_whole_input_public_projection(self):
        value = "EconCSLib-private"
        rendered = renderer._tex_identifier(value).replace(r"\allowbreak{}", "")
        self.assertEqual(rendered, renderer._tex_escape(value))
        self.assertEqual(rendered, "the development repository")
        self.assertNotIn("EconCSLib-private", rendered)

    def test_source_version_removes_endorsement_without_mutating_metadata(self):
        source_map = {
            "source_version": (
                "Byte-pinned arXiv 1810.13028 TeX plus the author-approved "
                "finite-chain corrected model recorded 2026-07-24; q > 0"
            ),
            "source_artifact_sha256": "a" * 64,
        }
        original = dict(source_map)

        actual = renderer._packet_source_version({}, source_map)

        self.assertEqual(
            actual,
            "Byte-pinned arXiv 1810.13028 TeX plus the finite-chain corrected "
            "model recorded 2026-07-24; q > 0",
        )
        self.assertEqual(source_map, original)
        self.assertEqual(source_map["source_artifact_sha256"], "a" * 64)

    def test_settled_memo_path_is_breakable(self):
        actual = renderer._approved_review_contexts_tex(
            [
                {
                    "kind": "source_model_convention",
                    "id": "memo-link",
                    "report_summary": (
                        "The result-specific conditions and corrections are stated "
                        "in the [clarification memo](docs/SOURCE_CLARIFICATIONS.md)."
                    ),
                }
            ]
        )

        self.assertIn(
            r"[clarification memo](docs/\allowbreak{}"
            r"SOURCE\_\allowbreak{}CLARIFICATIONS.\allowbreak{}md)",
            actual,
        )
        self.assertNotIn(
            r"[clarification memo](docs/SOURCE\_CLARIFICATIONS.md)",
            actual,
        )

    def test_reader_review_prose_removes_endorsement_without_changing_raw_displays(self):
        item = {
            "name": "Claim",
            "full_name": "Fixture.claimSpec",
            "verbatim_source_input": (
                "ARCHIVAL author-approved SOURCE: q = 1/2."
            ),
            "semantic_expanded_statement": (
                "LEAN owner-approved DISPLAY: q = 1/2."
            ),
            "llm_match_judgment": "matches_approved_corrected_target",
            "llm_match_reason": (
                "Matches the documented formalizer-approved corrected target: "
                "q = 1/2."
            ),
        }
        records = (
            {
                "source_location": "source.tex:10-12",
                "coverage_status": "corrected_source_statement",
                "corrected_target": {
                    "statement": (
                        "For the author-approved corrected finite ordinal IID model, "
                        "q = 1/2."
                    ),
                    "archival_source_locator": "source.tex:10-12",
                },
            },
        )

        actual = renderer._row_tex(item, records, "Fixture.claim", 1)
        readable = actual.replace(r"\allowbreak{}", "")

        self.assertIn("ARCHIVAL author-approved SOURCE: q = 1/2.", actual)
        self.assertIn("LEAN owner-approved DISPLAY: q = 1/2.", actual)
        self.assertIn(
            "For the corrected finite ordinal IID model, q = 1/2.", actual,
        )
        self.assertIn(
            "Matches the documented corrected target: q = 1/2.", readable,
        )
        self.assertNotIn("For the author-approved corrected", actual)
        self.assertNotIn("documented formalizer-approved corrected", actual)

    def test_all_reviewer_reason_paths_remove_endorsement_modifiers(self):
        library = renderer._prerequisites_tex(
            Path("/missing/papers/Fixture"),
            (
                {
                    "lean_name": "Fixture.library",
                    "library_semantic_target": "LibraryTarget",
                    "semantic_reason": (
                        "Uses the owner-approved corrected model with q >= 1/2."
                    ),
                },
            ),
        )
        paper = renderer._paper_prerequisites_tex(
            (
                {
                    "lean_name": "Fixture.paper",
                    "paper_semantic_target": "PaperTarget",
                    "semantic_reason": "Uses the author-approved bound q >= 1/2.",
                },
            )
        )
        readable_library = library.replace(r"\allowbreak{}", "")
        readable_paper = paper.replace(r"\allowbreak{}", "")

        self.assertIn(
            "Uses the corrected model with q >= 1/2.", readable_library,
        )
        self.assertIn("Uses the bound q >= 1/2.", readable_paper)
        self.assertNotIn("owner-approved", library)
        self.assertNotIn("author-approved", paper)

    def test_settled_context_prose_removes_endorsement_and_keeps_conditions(self):
        actual = renderer._approved_review_contexts_tex(
            [
                {
                    "kind": "source_model_convention",
                    "id": "finite-model",
                    "report_summary": (
                        "Uses the owner-approved governing model with q = 1/2."
                    ),
                },
                {
                    "kind": "maintainer_approved_additional_assumptions",
                    "id": "positive-q",
                    "conditions": ["formalizer-approved q > 0"],
                },
            ]
        )
        readable = actual.replace(r"\allowbreak{}", "")

        self.assertIn("Uses the governing model with q = 1/2.", readable)
        self.assertIn(r"\paragraph{Additional assumptions}", actual)
        self.assertIn("q > 0", actual)
        self.assertNotIn("Approved additional assumptions", actual)
        self.assertNotIn("owner-approved", actual)
        self.assertNotIn("formalizer-approved", actual)

    def test_predicative_endorsement_is_replaced_with_neutral_prose(self):
        actual = renderer._neutral_review_prose(
            "This target is author-approved. Its boundary is q = 1/2."
        )

        self.assertEqual(
            actual,
            "This target is formalized. Its boundary is q = 1/2.",
        )
        self.assertEqual(
            renderer._neutral_review_prose("This is an author-approved target."),
            "This is a target.",
        )
        self.assertEqual(
            renderer._neutral_review_prose("This model remains owner approved."),
            "This model remains formalized.",
        )

    def test_economic_owner_approval_is_not_rewritten(self):
        prose = (
            "If the owner approved allocation A, utility is 1. "
            "The owner-approved allocation gives q = 1/2."
        )

        self.assertEqual(renderer._neutral_review_prose(prose), prose)

    def test_ambiguous_owner_compounds_preserve_substantive_conditions(self):
        for prose in (
            "An owner-approved insurance claim has expected value q = 1/2.",
            "The owner-approved allocation target requires utility >= q.",
        ):
            with self.subTest(prose=prose):
                self.assertEqual(renderer._neutral_review_prose(prose), prose)

    def test_unsupported_review_branding_fails_closed(self):
        for prose in (
            "The author approved this corrected target.",
            "The formalizer approved this governing model.",
        ):
            with self.subTest(prose=prose), self.assertRaisesRegex(
                ValueError, "unsupported endorsement wording"
            ):
                renderer._neutral_review_prose(prose)

    def test_rendering_consumes_prepared_cards_without_files_or_discovery(self):
        row = ({
            "name": "Claim", "full_name": "Fixture.claimSpec",
            "verbatim_source_input": "Every source object has its property.",
            "semantic_expanded_statement": "∀ x, property x",
            "llm_match_current": True, "llm_match_judgment": "matches",
        }, (), "Fixture.claim")
        prepared = SimpleNamespace(
            paper_dir=Path("/missing/papers/Fixture"), source_map={}, status={},
            surface_error="", claim_rows=(row,), claim_sections=(("", (row,)),),
            paper_prerequisites=(), library_prerequisites=(),
        )
        with (
            mock.patch.object(Path, "read_text", side_effect=AssertionError("file read")),
            mock.patch("builtins.open", side_effect=AssertionError("file open")),
            mock.patch("subprocess.run", side_effect=AssertionError("producer")),
        ):
            actual = renderer.render_packet(
                prepared, template="@@METADATA@@\n@@ROWS@@", generated_date="2026-09-05",
            )
        self.assertIn("Every source object has its property.", actual)
        self.assertIn("∀ x, property x", actual)
        self.assertIn(r"\textbf{Generated:} 2026-09-05", actual)

    def test_governing_closure_is_linked_once_without_review_rows(self):
        base_name = "AppliedModelingLib.Shared.Base"
        model_name = "Fixture.paperModel"
        row = ({
            "name": "Claim",
            "full_name": "Fixture.claimSpec",
            "verbatim_source_input": "Every source object has its property.",
            "semantic_expanded_statement": "∀ x, paperModel x",
            "llm_match_current": True,
            "llm_match_judgment": "matches",
            "governing_declaration_links": [
                {"lean_name": model_name, "anchor_kind": "governing-declaration"}
            ],
        }, (), "Fixture.claim")
        prepared = SimpleNamespace(
            paper_dir=Path("/missing/papers/Fixture"),
            source_map={},
            status={},
            surface_error="",
            claim_rows=(row,),
            claim_sections=(("", (row,)),),
            paper_prerequisites=(),
            library_prerequisites=(),
            governing_declarations=(
                {
                    "lean_name": base_name,
                    "location": "library",
                    "declaration_kind": "definition",
                    "display": "def Base : Prop := True",
                    "governing_declaration_links": [],
                },
                {
                    "lean_name": model_name,
                    "location": "paper",
                    "declaration_kind": "definition",
                    "display": "def paperModel := Shared.Base",
                    "governing_declaration_links": [
                        {
                            "lean_name": base_name,
                            "anchor_kind": "governing-declaration",
                        }
                    ],
                },
            ),
        )

        actual = renderer.render_packet(
            prepared,
            template=(
                "@@METADATA@@\n@@CONTENTS@@\n@@PREREQUISITES@@\n@@ROWS@@"
            ),
            generated_date="2026-09-06",
        )

        self.assertIn("Governing Lean declarations (2; supporting context)", actual)
        self.assertIn("def Base : Prop := True", actual)
        self.assertIn("def paperModel := Shared.Base", actual)
        self.assertEqual(actual.count("def Base : Prop := True"), 1)
        self.assertIn(
            "\\hypertarget{"
            + renderer._packet_anchor("governing-declaration", model_name)
            + "}{}",
            actual,
        )
        self.assertIn(
            "\\hyperlink{"
            + renderer._packet_anchor("governing-declaration", base_name)
            + "}",
            actual,
        )
        self.assertEqual(actual.count("\\reviewerbox"), 1)
        self.assertEqual(actual.count("\\reviewmatch{"), 1)

    def test_private_git_transport_is_not_rendered_as_official_source(self):
        actual = renderer.render_packet(
            self._prepared_surface("https://git.overleaf.com/private-project"),
            template="@@METADATA@@\n@@ROWS@@", generated_date="2026-09-05",
        )
        self.assertNotIn("git.overleaf.com", actual)
        self.assertNotIn("official source", actual)
        self.assertIn("Every source object has its property.", actual)

    def test_public_web_source_is_retained_as_official_source(self):
        actual = renderer.render_packet(
            self._prepared_surface("https://arxiv.org/abs/2601.00001"),
            template="@@METADATA@@\n@@ROWS@@", generated_date="2026-09-05",
        )
        self.assertIn(
            r"\href{https://arxiv.org/abs/2601.00001}{official source}", actual,
        )

    def test_currentness_ignores_only_date_and_trailing_horizontal_whitespace(self):
        original = "header\n\\textbf{Generated:} 2026-09-04\\\\\n∀ x, property x\n"
        cosmetic = "header \t\n\\textbf{Generated:} 2026-09-05\\\\ \t\n∀ x, property x \t\n"
        self.assertEqual(_packet_tex_currentness_text(original), _packet_tex_currentness_text(cosmetic))
        for changed in (
            original.replace("∀", "∃"),
            original.replace("property x", "property  x"),
            original.replace("header", " header"),
            original + "\n",
        ):
            with self.subTest(changed=changed):
                self.assertNotEqual(_packet_tex_currentness_text(original), _packet_tex_currentness_text(changed))
