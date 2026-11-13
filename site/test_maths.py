"""Regression checks for delimiters, static rendering and citation metadata."""

import html
import unittest

from build import abstract_html, document
from check import Page, check_page, normal
from maths import render_html, split_math


def expressions(source):
    return [(tex, display) for _, tex, display in split_math(source) if tex is not None]


class DelimiterTests(unittest.TestCase):
    def test_inline_and_display_delimiters(self):
        self.assertEqual(expressions(r"$G_1$ $$x^2$$ \(\mu\le5\) \[K_{3,3,1,1}\]"),
                         [("G_1", False), ("x^2", True), (r"\mu\le5", False), ("K_{3,3,1,1}", True)])

    def test_currency_whitespace_and_unmatched_dollars(self):
        for source in ["Costs $5 or $10.", "$5,$10", "A single $ sign", "$ spaced $", "$x$2"]:
            with self.subTest(source=source):
                self.assertEqual(expressions(source), [])
        self.assertEqual(expressions("Costs $5; then $x$ units."), [("x", False)])

    def test_escapes_and_nested_braces(self):
        source = r"\$x\$; $\text{price: \$5 and {a$b}}$; \(x+\text{\)}\)"
        self.assertEqual(expressions(source), [(r"\text{price: \$5 and {a$b}}", False),
                                               (r"x+\text{\)}", False)])
        self.assertEqual("".join(piece for piece, _, _ in split_math(source)), source)


class RenderingTests(unittest.TestCase):
    def page(self, body, title="Example", tags=()):
        page = Page(document(title, body, tags))
        check_page(page, "example")
        return page

    def test_all_delimiters_render_with_mathml_and_no_script(self):
        source = r"$G_1$ $$x^2$$ \(\mu\le5\) \[K_{3,3,1,1}\] $\Delta Y$"
        page = self.page("<p>" + source + "</p>")
        self.assertEqual(page.math_count, 5)
        self.assertEqual(page.annotations, 5)
        rendered = render_html("<p>" + source + "</p>")
        self.assertEqual(rendered.count('<math '), 5)
        self.assertEqual(rendered.count('display="block"'), 2)
        self.assertNotIn("katex-html", rendered)
        self.assertNotIn("katex-mathml", rendered)
        self.assertNotIn("<script", rendered)
        self.assertNotIn("<link", document("Example", "<p>" + source + "</p>"))

    def test_math_in_titles_and_index_links_keeps_citation_text(self):
        title = r"Graphs $G_1$, $\mu\le5$ and \(\Delta Y\)"
        body = '<h1>' + html.escape(title) + '</h1><a href="paper/">' + html.escape(title) + '</a>'
        page = self.page(body, title, [("citation_title", title)])
        self.assertEqual(page.meta["citation_title"], [title])
        self.assertEqual(normal(page.headings[0]), normal(title))
        self.assertEqual(page.math_count, 6)
        self.assertEqual(page.links, ["paper/"])

    def test_text_math_and_attributes_are_escaped_separately(self):
        source = '<p title="$untouched$">&lt;em&gt; &amp; $a&lt;b$</p>'
        rendered = render_html(source)
        self.assertIn('title="$untouched$"', rendered)
        self.assertIn("&lt;em&gt; &amp;", rendered)
        self.assertNotIn("<em>", rendered)
        page = self.page(rendered)
        self.assertIn("a<b", "".join(page.body))

    def test_literal_dollars_remain_visible_without_becoming_math(self):
        page = self.page(r"<p>Costs $5 or $10; write \$x\$ literally, then $y$.</p>")
        self.assertEqual(page.math_count, 1)
        self.assertIn(r"\$x\$", "".join(page.body))
        self.assertIn('class="tex-dollar">$</span>', render_html(r"\$"))
        self.assertEqual(render_html(r"\\$"), r"\\$")

    def test_sanitized_abstract_renders_entities_and_formatting(self):
        source = '<p><em>Bound</em>: $a&lt;b$ &amp; $c$.</p><script>alert(1)</script>'
        page = self.page(abstract_html(source))
        self.assertEqual(page.math_count, 2)
        self.assertEqual(normal("".join(page.body)), normal("Bound: a<b & c."))

    def test_bad_tex_fails_instead_of_leaving_raw_math(self):
        with self.assertRaisesRegex(ValueError, "KaTeX rendering failed"):
            render_html(r"<p>$\unknowncommand{x}$</p>")

    def test_unrendered_math_is_rejected_even_across_formatting(self):
        for source in [r"$G_1$", r"$$x^2$$", r"\(x\)", r"\[x\]", "$<em>x</em>$",
                       '<span aria-hidden="true">$x$</span>']:
            with self.subTest(source=source):
                page = Page(document("Example", "<p>placeholder</p>").replace("placeholder", source))
                with self.assertRaisesRegex(ValueError, "Unrendered math"):
                    check_page(page, "example")

    def test_html_in_any_citation_tag_is_rejected(self):
        for name in ["citation_title", "citation_author", "citation_extra"]:
            page = Page(document("Example", "<p>Example</p>", [(name, '<span class="katex">x</span>')]))
            with self.assertRaisesRegex(ValueError, "HTML in " + name):
                check_page(page, "example")

    def test_scripts_and_stylesheets_are_rejected(self):
        for asset in ['<script src="math.js"></script>', '<link rel="stylesheet" href="math.css">']:
            page = Page(document("Example", "<p>Example</p>").replace('</head>', asset + '</head>'))
            with self.assertRaisesRegex(ValueError, "Unexpected assets"):
                check_page(page, "example")


if __name__ == "__main__":
    unittest.main()
