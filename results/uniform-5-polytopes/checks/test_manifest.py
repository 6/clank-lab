"""Prose/output serialization is not a byte gate; scientific pins still reject."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from check_manifest import check


class ManifestPolicy(unittest.TestCase):
    def test_prose_and_output_changes_do_not_affect_scientific_pins(self):
        with tempfile.TemporaryDirectory() as work:
            root = Path(work)
            (root/'data').mkdir()
            (root/'checks').mkdir()
            payload = {'checker.py': '# checker\n', 'certificate.json': '{"claim": 1}\n',
                       'NOTE.md': 'old note', 'paper.tex': 'old manuscript',
                       'output.json': '{"count": 1, "elapsed_seconds": 2}\n'}
            for name, data in payload.items():
                (root/name).write_text(data)
            scope = {'checkers': ['checker.py'], 'certificates': ['certificate.json'],
                     'authoritative_inputs': []}
            (root/'data/acceptance-inputs.json').write_text(json.dumps(scope))
            names = sorted([*payload, 'data/acceptance-inputs.json', 'data/PUBLIC.sha256', 'checks/PUBLIC.txt'])
            (root/'checks/PUBLIC.txt').write_text('\n'.join(names)+'\n')
            (root/'data/PUBLIC.sha256').write_text(''.join(
                hashlib.sha256((root/name).read_bytes()).hexdigest()+'  '+name+'\n'
                for name in ('checker.py', 'certificate.json')))
            with contextlib.redirect_stdout(io.StringIO()):
                check(root)
                (root/'NOTE.md').write_text('rewritten note')
                (root/'paper.tex').write_text('rewritten manuscript')
                (root/'output.json').write_text('{"elapsed_seconds": 99, "count": 1}\n')
                check(root)
            for name in ('checker.py', 'certificate.json'):
                original = (root/name).read_bytes()
                (root/name).write_bytes(original+b'corruption')
                with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                    check(root)
                (root/name).write_bytes(original)
            scope['authoritative_inputs'].append('NOTE.md')
            (root/'data/acceptance-inputs.json').write_text(json.dumps(scope))
            with self.assertRaisesRegex(ValueError, 'prose cannot'):
                check(root)


if __name__ == '__main__':
    unittest.main()
