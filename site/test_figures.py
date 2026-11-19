import contextlib
import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from build import paper_figure
from check import Page
from figures import FIGURE_FILE, verify_figure

SVG = b'<svg xmlns="http://www.w3.org/2000/svg"><circle r="1"/></svg>'


def entry_for(data):
    return {
        "path": "data/approved.svg",
        "sha256": hashlib.sha256(data).hexdigest(),
        "caption": "A circle & its radius.",
        "alt": 'A circle labeled "1".',
    }


class FigureTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.output = self.root / "output"
        self.output.mkdir()
        self.entry = entry_for(SVG)
        self.approved = self.root / "results" / "example" / self.entry["path"]
        self.approved.parent.mkdir(parents=True)

    def render(self, entries):
        with patch("build.FIGURES", entries), contextlib.redirect_stderr(io.StringIO()):
            return paper_figure(self.root, "example", self.output)

    def test_verified_svg_has_exact_bytes_and_accessible_label(self):
        self.approved.write_bytes(SVG)
        page = Page("<body>" + self.render({"example": self.entry}) + "</body>")
        self.assertFalse(page.unsafe)
        self.assertEqual(page.images, [(FIGURE_FILE, self.entry["alt"])])
        self.assertEqual(page.captions, [self.entry["caption"]])
        self.assertEqual((self.output / FIGURE_FILE).read_bytes(), SVG)

    def test_unlisted_svg_is_omitted(self):
        self.approved.write_bytes(SVG)
        self.assertEqual(self.render({}), "")
        self.assertEqual(list(self.output.iterdir()), [])

    def test_missing_svg_is_not_replaced_by_another_file(self):
        self.approved.with_name("other.svg").write_bytes(SVG)
        self.assertEqual(self.render({"example": self.entry}), "")
        self.assertEqual(list(self.output.iterdir()), [])

    def test_checksum_mismatch_is_omitted(self):
        self.approved.write_bytes(SVG + b"\n")
        self.assertEqual(self.render({"example": self.entry}), "")
        self.assertEqual(list(self.output.iterdir()), [])
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            verify_figure(self.approved.read_bytes(), self.entry)

    def test_unsafe_svg_is_rejected_even_with_matching_checksum(self):
        for image in (
            b'<script/>', b'<circle onload=""/>', b'<image href="https://example.org/remote.png"/>',
        ):
            with self.subTest(image=image):
                data = b'<svg xmlns="http://www.w3.org/2000/svg">' + image + b'</svg>'
                with self.assertRaisesRegex(ValueError, "Unexpected"):
                    verify_figure(data, entry_for(data))

    def test_figure_image_requires_alt_and_disallows_other_attributes(self):
        for attributes in ('', ' alt="" srcset="other.svg 2x"', ' alt="" onload=""'):
            with self.subTest(attributes=attributes):
                page = Page(f'<body><figure><img src="{FIGURE_FILE}"{attributes}></figure></body>')
                self.assertTrue(page.unsafe)
