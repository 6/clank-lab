"""Regression tests for paper summaries, PDF links and AI disclosures."""

import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from build import AI_CREDIT_HTML, paper_abstract
from check import Page, check_paper_content
from maths import render_html
from summaries import paper_summaries


class PaperContentTests(unittest.TestCase):
    def test_missing_plain_summary_file_fails(self):
        with TemporaryDirectory() as directory:
            checkout = Path(directory)
            with self.assertRaisesRegex(ValueError, r"Missing site/plain_summaries\.json"):
                paper_summaries(checkout, ["example"])

    def test_short_credit_requires_separate_explicit_disclosure_to_be_removed(self):
        credit = f"<p>Checked in Lean. {AI_CREDIT_HTML}</p>"
        prior_work = "<p>A prior AI-generated proof treated a different case.</p>"
        self.assertEqual(paper_abstract(prior_work + credit), (prior_work + credit, True))
        self.assertEqual(paper_abstract(prior_work), (prior_work + f"<p>{AI_CREDIT_HTML}</p>", True))
        for disclosure in (
            "<p>The proofs and text were produced by AI models, working under the author's direction.</p>",
            "<p>This paper was written with AI assistance.</p>",
        ):
            with self.subTest(disclosure=disclosure):
                self.assertEqual(paper_abstract(disclosure + credit),
                                 (disclosure.replace("'", "&#x27;") + "<p>Checked in Lean.</p>", False))

    def test_plain_summary_file_requires_a_nonblank_string_for_each_paper(self):
        with TemporaryDirectory() as directory:
            checkout = Path(directory)
            path = checkout / "site" / "plain_summaries.json"
            path.parent.mkdir()
            path.write_text(json.dumps({"example": " A plain summary. "}), encoding="utf-8")
            self.assertEqual(paper_summaries(checkout, ["example"]), {"example": "A plain summary."})
            with self.assertRaisesRegex(ValueError, "plain_summary for absent"):
                paper_summaries(checkout, ["example", "absent"])
            for entry in (None, " \n ", 17):
                path.write_text(json.dumps({"example": entry}), encoding="utf-8")
                with self.subTest(entry=entry), self.assertRaisesRegex(ValueError, "plain_summary for example"):
                    paper_summaries(checkout, ["example"])

    def test_check_rejects_missing_or_changed_summary_pdf_link_and_abstract_credit(self):
        summary = 'A puzzle for $n^2$ steps.'
        source_abstract = f"<p>We settle the question. {AI_CREDIT_HTML}</p>"
        line = f'<p class="summary-text">{summary}</p>'
        doi = '<a class="paper-doi" href="https://doi.org/10.5281/zenodo.100">DOI</a>'
        pdf = '<a class="paper-pdf" href="sample.pdf">Read the paper (PDF) →</a>'
        source = (f'<body><p class="links">{pdf}</p><p class="links">{doi}</p>'
                  '<section class="paper-summary" aria-labelledby="paper-summary-heading">'
                  f'<h2 id="paper-summary-heading">In short</h2>{line}</section>'
                  '<section aria-labelledby="paper-abstract-heading">'
                  '<h2 id="paper-abstract-heading">Abstract</h2>'
                  f'<div class="abstract-text">{source_abstract}</div></section></body>')
        self.assertTrue(check_paper_content(Page(render_html(source)), summary, source_abstract, "sample"))
        for changed, error in (
            (source.replace(line, ""), "Missing or misplaced DOI link, PDF link, summary"),
            (source.replace("In short", "Summary"), "Incorrect summary or abstract heading"),
            (source.replace("$n^2$", "$n^3$"), "Summary differs from source"),
            (source.replace("steps.", "steps!"), "Summary differs from source"),
            (source.replace(pdf, "", 1), "Missing or misplaced DOI link, PDF link"),
            (source.replace("</body>", f"{pdf}</body>"), "Missing or misplaced DOI link, PDF link"),
            (source.replace(doi, doi * 2), "Missing or misplaced DOI link"),
            (source.replace(">DOI<", ">DOI (v1)<"), "Incorrect DOI link label"),
            (source.replace("Read the paper", "Download", 1), "Incorrect PDF link label"),
            (source.replace(AI_CREDIT_HTML, ""), "Abstract or AI credit differs"),
        ):
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, error):
                check_paper_content(Page(render_html(changed)), summary, source_abstract, "sample")
