"""Runtime acceptance is independent of manuscript/NOTE revisions."""
import contextlib
import copy
import receipt_policy
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import verify_identities


class RuntimeInputs(unittest.TestCase):
    def test_export_and_corruptions(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            here = root / 'independent'
            here.mkdir()
            payloads = {'engine.py': b'# checker', 'certificate.json': b'{}'}
            for name, data in payloads.items():
                (here/name).write_bytes(data)
            (root/'input.json').write_bytes(b'[]')
            manifest = dict(files={name: hashlib.sha256(data).hexdigest()
                                  for name,data in payloads.items()},
                            inputs={'input.json': hashlib.sha256(b'[]').hexdigest()})
            path = here/'runtime-identities.json'
            path.write_text(json.dumps(manifest))
            with patch.object(verify_identities, 'HERE', here), contextlib.redirect_stdout(io.StringIO()):
                verify_identities.main()
                (here/'NOTE.md').write_text('A revised status.')
                (root/'paper').mkdir()
                (root/'paper/main.tex').write_text('A revised proof.')
                verify_identities.main()
                for target in (here/'engine.py', here/'certificate.json', root/'input.json'):
                    original = target.read_bytes()
                    target.write_bytes(original+b'changed')
                    with self.subTest(path=target.name), self.assertRaises(ValueError):
                        verify_identities.main()
                    target.unlink()
                    with self.assertRaises(FileNotFoundError):
                        verify_identities.main()
                    target.write_bytes(original)
                manifest['files']['NOTE.md'] = hashlib.sha256((here/'NOTE.md').read_bytes()).hexdigest()
                path.write_text(json.dumps(manifest))
                with self.assertRaisesRegex(ValueError, 'mutable prose'):
                    verify_identities.main()


class ReceiptPolicy(unittest.TestCase):
    def test_only_named_timings_may_change(self):
        for name in ("stage1-result.json", "stage1-verification.json"):
            path = receipt_policy.TIMINGS[name]
            original = receipt_policy.read_receipt(Path(__file__).resolve().parent/"evidence"/name)
            def change(value):
                bad = copy.deepcopy(original)
                parent = bad
                for key in path[:-1]:
                    parent = parent[key]
                parent[path[-1]] = value
                return bad
            receipt_policy.compare_receipt(change(0), original, name)
            receipt_policy.compare_receipt(change(123.5), original, name)
            for value in (-1, True, "1", None, float("nan"), float("inf")):
                with self.subTest(name=name, value=value), self.assertRaises(ValueError):
                    receipt_policy.compare_receipt(change(value), original, name)
            bad = change(0)
            parent = bad
            for key in path[:-1]:
                parent = parent[key]
            del parent[path[-1]]
            receipt_policy.compare_receipt(bad, original, name)
            reordered = dict(reversed(list(original.items())))
            receipt_policy.compare_receipt(json.loads(json.dumps(reordered, indent=1)), original, name)
            summary = () if name == "stage1-result.json" else ("full_stage1_replay",)
            for field, value in (("cycles", 14964), ("undecided", 1), ("omega_sha256", "0"*64),
                                 ("words", True), ("cycles", 14965.0)):
                bad = copy.deepcopy(original)
                parent = bad
                for key in summary:
                    parent = parent[key]
                parent[field] = value
                with self.subTest(name=name, field=field), self.assertRaises(ValueError):
                    receipt_policy.compare_receipt(bad, original, name)
            bad = copy.deepcopy(original)
            bad["unapproved"] = {"elapsed_seconds": 1}
            with self.assertRaises(ValueError):
                receipt_policy.compare_receipt(bad, original, name)
        with self.assertRaises(ValueError):
            receipt_policy.scientific_receipt({}, "other.json")

    def test_receipts_are_not_hashed_but_certificates_are(self):
        here = Path(__file__).resolve().parent
        manifest = json.loads((here/"runtime-identities.json").read_text())
        for name in ("evidence/stage1-result.json", "evidence/stage1-verification.json",
                     "evidence/comparison.json", "evidence/b2-comparison.json", "library_evidence.jsonl"):
            self.assertNotIn(name, manifest["files"])
        for name in ("library.json", "evidence/omega.json", "evidence/cycles.json.gz",
                     "evidence/b2-full.json"):
            self.assertIn(name, manifest["files"])

    def test_comparison_receipts_timing_key_order_and_mutation(self):
        here = Path(__file__).resolve().parent
        for name in ("comparison.json", "b2-comparison.json"):
            original = receipt_policy.read_receipt(here/"evidence"/name)
            reordered = dict(reversed(list(original.items())))
            reordered["elapsed_seconds"] = 125
            receipt_policy.compare_receipt(json.loads(json.dumps(reordered, indent=1)), original, name)
            bad = copy.deepcopy(original)
            if name == "comparison.json":
                bad["cycles"]["cycle_words"] += 1
            else:
                bad["total_radii"] += 1
            with self.assertRaises(ValueError):
                receipt_policy.compare_receipt(bad, original, name)

    def test_regenerated_certificates_ignore_object_key_order(self):
        import verify_stage1
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            expected = root/"expected.json"
            actual = root/"omega.json"
            expected.write_text('{"intervals":[["1","2",0]],"schema":"x"}')
            actual.write_text('{"schema":"x","intervals":[["1","2",0]]}')
            verify_stage1.equal_file(actual, expected)
            actual.write_text('{"schema":"x","intervals":[["1","3",0]]}')
            with self.assertRaises(ValueError):
                verify_stage1.equal_file(actual, expected)

    def test_duplicate_and_nonfinite_json_reject(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary)/"receipt.json"
            for raw in ('{"cycles":1,"cycles":2}', '{"elapsed_seconds":NaN}'):
                path.write_text(raw)
                with self.assertRaises(ValueError):
                    receipt_policy.read_receipt(path)


if __name__ == '__main__':
    unittest.main()
