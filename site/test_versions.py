"""Regression checks for Zenodo version selection, display and DOI resolution."""

from types import SimpleNamespace
import unittest
from unittest.mock import patch

from build import displayed_versions, fetch, version_date_line, versions_of
from check import Page, check_versions


def record(record_id, index, is_last, day):
    return {
        "id": record_id,
        "conceptdoi": "10.5281/zenodo.100",
        "doi": f"10.5281/zenodo.{record_id}",
        "created": "2026-01-01T00:00:00+00:00",
        "metadata": {
            "publication_date": day,
            "relations": {"version": [{"index": index, "is_last": is_last}]},
        },
    }


class VersionTests(unittest.TestCase):
    def test_single_version_is_shown_once(self):
        only = record(101, 0, True, "2026-01-02")
        versions = displayed_versions(only, versions_of(only))
        page = Page("<body>" + version_date_line(versions[0]) + "</body>")
        self.assertEqual(page.dates, ["2026-01-02"])
        self.assertEqual([line["text"] for line in page.version_dates], ["Published Jan 2, 2026"])
        check_versions(page, versions, "example")

    def test_selects_first_and_latest_by_version_relation(self):
        first = record(101, 0, False, "2026-01-02")
        middle = record(102, 1, False, "2026-01-03")
        latest = record(103, 2, True, "2026-01-02")
        versions = displayed_versions(latest, [middle, first, latest])
        self.assertEqual(versions, [
            dict(number=1, date="2026-01-02", doi="10.5281/zenodo.101", record_id=101),
            dict(number=3, date="2026-01-02", doi="10.5281/zenodo.103", record_id=103),
        ])
        with self.assertRaisesRegex(ValueError, "Cannot identify first and latest"):
            displayed_versions(latest, [middle, latest])

    def test_checker_rejects_incorrect_visible_version_dates(self):
        first = record(101, 0, False, "2026-01-02")
        latest = record(102, 1, True, "2026-01-03")
        versions = displayed_versions(latest, [first, latest])
        published = version_date_line(versions[0], show_number=True)
        updated = version_date_line(versions[1], updated=True)
        source = f"<body>{published}{updated}</body>"
        page = Page(source)
        self.assertEqual([line["text"] for line in page.version_dates],
                         ["Published Jan 2, 2026 (version 1)", "Updated Jan 3, 2026 (version 2)"])
        check_versions(page, versions, "example")
        for error, original, changed in (
            ("update date line", "version 2", "version 3"),
            ("update date line", "Jan 3, 2026</time>", "Jan 4, 2026</time>"),
            ("update date line", 'datetime="2026-01-03"', 'datetime="2026-01-04"'),
            ("publication date line", " (version 1)", ""),
            ("publication date line", "Jan 2, 2026</time>", "Jan 3, 2026</time>"),
        ):
            with self.subTest(changed=changed), self.assertRaisesRegex(ValueError, f"Incorrect {error}"):
                check_versions(Page(source.replace(original, changed)), versions, "example")
        with self.assertRaisesRegex(ValueError, "Incorrect number of version date lines"):
            check_versions(Page(source.replace(updated, "")), versions, "example")

    @patch("build.urlopen")
    def test_concept_doi_must_resolve_to_latest_record(self, urlopen):
        response = SimpleNamespace(url="https://zenodo.org/records/101", status=200)
        urlopen.return_value.__enter__.return_value = response
        url = "https://doi.org/10.5281/zenodo.100"
        fetch(url, landing_record=101)
        with self.assertRaisesRegex(ValueError, "expected Zenodo record 102"):
            fetch(url, landing_record=102)
