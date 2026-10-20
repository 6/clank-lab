"""Certificate omission/forgery regressions, including the audit reproduction."""
import contextlib
import copy
import io
import json
import shutil
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import inventory
import summary

HERE = Path(__file__).resolve().parent


def records(profile='full'):
    filename = 'w_supp.jsonl' if profile == 'supplementary' else 'w_results.jsonl'
    fixture = HERE.parent / 'acceptance-third/infinite/outputs/check_caseb' / filename
    # The repository verifier copies check_caseb alone before running quick.
    # Its local full-run records are the authoritative initial fixture there.
    if not fixture.exists():
        fixture = HERE / filename
    rows = [json.loads(l) for l in fixture.read_text().splitlines()]
    names, _ = inventory.profile(profile)
    rows = [r for r in rows if r['fan'] in names]
    # Historical bytes predate the additive domain field. Annotate fixtures
    # explicitly; production acceptance never supplies a missing annotation.
    for r in rows:
        r['parameter_domain'] = inventory.obligations(r['fan'])[0]
    return rows


class AcceptanceControls(unittest.TestCase):
    def test_complete_profiles(self):
        for name, count in [('full', 134), ('supplementary', 67), ('quick', 11), ('controls', 4)]:
            with self.subTest(profile=name):
                rows = records(name)
                self.assertEqual(len(rows), count)
                summary.validate_records(rows, name)

    def test_fixture_loader_in_copied_driver(self):
        with tempfile.TemporaryDirectory() as tmp:
            destination = Path(tmp) / 'check_caseb'
            shutil.copytree(HERE, destination, ignore=shutil.ignore_patterns('__pycache__'))
            code = "import test_acceptance as t; import sys; (len(t.records()) == 134 and len(t.records('supplementary')) == 67) or sys.exit('inventory size differs')"
            subprocess.run([sys.executable, '-c', code], cwd=destination, check=True)

    def test_reported_successful_fan_omission(self):
        rows = [r for r in records() if r['fan'] != '(i)(3,3,3)']
        with tempfile.NamedTemporaryFile(mode='w+') as f:
            for row in rows:
                f.write(json.dumps(row) + '\n')
            f.flush()
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaisesRegex(ValueError, 'inventory'):
                summary.main(f.name, sorted(inventory.profile('full')[1]), inventory='full')

    def test_explicit_inventory_required(self):
        with self.assertRaisesRegex(ValueError, 'explicit'):
            summary.main('unused')

    def test_inventory_corruptions_all_profiles(self):
        for profile in ('full', 'supplementary', 'quick', 'controls'):
            rows = records(profile)
            bads = [rows[1:], rows + [copy.deepcopy(rows[0])],
                    rows + [dict(rows[0], fan='unexpected')]]
            for bad in bads:
                with self.subTest(profile=profile), self.assertRaisesRegex(ValueError, 'inventory|duplicate'):
                    summary.validate_records(bad, profile)

    def test_domains_and_kind(self):
        for mutate in (
            lambda r: r.pop('parameter_domain'),
            lambda r: r['parameter_domain'].update(n={'kind': 'integer_point', 'value': 17}),
            lambda r: r['parameter_domain'].update(m=dict(inventory.REAL)),
            lambda r: r['parameter_domain']['n'].update(min=17.0),
            lambda r: r['parameter_domain']['n'].update(includes_infinity=1),
            lambda r: r.update(kind='paired'),
        ):
            rows = records()
            mutate(rows[0])
            with self.assertRaises(ValueError):
                summary.validate_records(rows, 'full')
        rows = records()
        row = next(r for r in rows if '@n=' in r['fan'])
        row['parameter_domain']['n']['value'] += 1
        with self.assertRaises(ValueError):
            summary.validate_records(rows, 'full')

    def test_test_content_corruptions(self):
        def required(row):
            return row['tests']['V:a:+']
        def pair(row):
            return next(iter(row['vertex_pairs'].values()))
        for mutate in (
            lambda r: r['tests'].pop('V:a:+'),
            lambda r: r['tests'].pop('P:+1-1'),
            lambda r: r['tests'].pop('D:+'),
            lambda r: r['tests'].update(extra={'ok': True}),
            lambda r: required(r).update(ok=False),
            lambda r: required(r).update(ok=1),
            lambda r: required(r).update(pending=1),
            lambda r: required(r).pop('unresolved'),
            lambda r: required(r).update(unresolved=True),
            lambda r: r['vertex_pairs'].pop(next(iter(r['vertex_pairs']))),
            lambda r: pair(r).update(ok=False),
            lambda r: pair(r).update(diagonal=True),
            lambda r: r.update(V_ok=False),
            lambda r: r.update(P_ok=False),
            lambda r: r.update(F_ok=False),
            lambda r: r.update(verdict='FAILED'),
            lambda r: r.update(direction_test='not sufficient'),
        ):
            rows = records()
            mutate(rows[0])
            with self.assertRaises(ValueError):
                summary.validate_records(rows, 'full')

    def test_singleton_receipt_and_recomputation(self):
        original = records()
        name = '(i)(38,3,7)'
        for allowed in ([], [['(3, 7)', '38'], ['(3, 7)', '39']], [['(3, 7)', '39']],
                        [['(3, 8)', '38']], [[38]], None):
            rows = copy.deepcopy(original)
            next(r for r in rows if r['fan'] == name)['partner_filter']['allowed'] = allowed
            with self.subTest(allowed=allowed), self.assertRaisesRegex(ValueError, 'singleton|only matching'):
                summary.validate_records(rows, 'full')
        with patch.object(summary.partner, 'allowed', return_value=(0, [((3, 7), 38), ((3, 8), 23)])):
            with self.assertRaisesRegex(ValueError, 'recomputed'):
                summary.validate_records(original, 'full')

    def test_expected_failures_cannot_change_profile(self):
        with self.assertRaisesRegex(ValueError, 'expected failures'):
            summary.validate_records(records(), 'full', [])


if __name__ == '__main__':
    unittest.main()
