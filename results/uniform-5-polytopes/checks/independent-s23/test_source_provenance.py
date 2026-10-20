"""Source-map corruptions must fail even after all byte links are rebound.

An empty S3 run supplies a real native receipt without geometric replay.
The mathematical audit is isolated here; test_handoff exercises that audit.
"""
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import audit_stage3
from provenance import file_digest, model_data_hashes
import stage3

HERE = Path(__file__).resolve().parent


class SourceProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.classes, self.states, self.known, self.results = [root / name for name in
                                                            ('classes.json', 's2.jsonl', 'known.json', 's3.jsonl')]
        for path in (self.classes, self.states, self.known):
            path.write_text('[]\n')
        self.provenance_path = Path(str(self.states) + '.provenance.json')
        self.provenance = {'input_sha256': file_digest(self.classes),
                           'model_data_sha256': model_data_hashes(),
                           'sources': {p.name: file_digest(p) for p in HERE.glob('*.py')}}
        self.provenance_path.write_text(json.dumps(self.provenance))
        argv = ['stage3.py', '--states', str(self.states), '--models', 'models',
                '--known', str(self.known), '--output', str(self.results)]
        with patch.object(sys, 'argv', argv), redirect_stdout(io.StringIO()):
            stage3.main()
        self.receipt_path = Path(str(self.results) + '.frozen.json')
        self.receipt = json.loads(self.receipt_path.read_text())

    def invoke(self, provenance, receipt):
        self.provenance_path.write_text(json.dumps(provenance))
        receipt = dict(receipt, s2_provenance_sha256=file_digest(self.provenance_path))
        self.receipt_path.write_text(json.dumps(receipt))
        argv = ['audit_stage3.py', '--classes', str(self.classes), '--states', str(self.states),
                '--results', str(self.results), '--models', 'models', '--known', str(self.known),
                '--pmax', '6', '--receipt', str(self.receipt_path)]
        # These fixtures are intentionally small, not authoritative class inputs.
        # The native byte links and source authentication run without mocks.
        with patch.object(sys, 'argv', argv), redirect_stdout(io.StringIO()), \
                patch.object(audit_stage3, 'authenticate', side_effect=lambda path, _: file_digest(path)), \
                patch.object(audit_stage3, 'audit', return_value={'status': 'PASS'}) as mathematical_audit:
            try:
                audit_stage3.main()
            except ValueError:
                mathematical_audit.assert_not_called()
                raise
            mathematical_audit.assert_called_once()

    def test_native_maps_pass(self):
        self.invoke(self.provenance, self.receipt)

    def test_prose_timing_key_order_allowed_but_precision_change_rejected(self):
        provenance=copy.deepcopy(self.provenance)
        receipt=copy.deepcopy(self.receipt)
        provenance['sources']['NOTE.md']='historical prose only'
        receipt['source_sha256']['paper/main.tex']='historical prose only'
        provenance['elapsed_seconds']=9876
        self.invoke(provenance,receipt)
        provenance['bits']=128
        with self.assertRaisesRegex(ValueError,'parsed provenance scientific fields'):
            self.invoke(provenance,receipt)

    def test_rebound_bogus_maps_rejected(self):
        for stage, key in (('S2', 'sources'), ('S3', 'source_sha256')):
            for change in ('missing-map', 'empty', 'wrong-digest', 'missing-entry', 'extra-entry'):
                with self.subTest(stage=stage, change=change):
                    provenance, receipt = copy.deepcopy(self.provenance), copy.deepcopy(self.receipt)
                    document = provenance if stage == 'S2' else receipt
                    if change == 'missing-map':
                        del document[key]
                    elif change == 'empty':
                        document[key] = {}
                    elif change == 'wrong-digest':
                        document[key]['stage3.py'] = '0' * 64
                    elif change == 'missing-entry':
                        del document[key]['stage3.py']
                    else:
                        document[key]['fabricated.py'] = '0' * 64
                    with self.assertRaisesRegex(ValueError, stage + ' source inventory or digest mismatch'):
                        self.invoke(provenance, receipt)

    def test_same_bogus_map_rejected_when_consistently_linked(self):
        for bogus in ({}, {'stage3.py': '0' * 64},
                      dict(self.provenance['sources'], **{'stage3.py': '0' * 64})):
            with self.subTest(entries=len(bogus)):
                provenance, receipt = copy.deepcopy(self.provenance), copy.deepcopy(self.receipt)
                provenance['sources'] = copy.deepcopy(bogus)
                receipt['source_sha256'] = copy.deepcopy(bogus)
                with self.assertRaisesRegex(ValueError, 'S2 source inventory or digest mismatch'):
                    self.invoke(provenance, receipt)

    def test_rebound_forged_module_aliases_rejected(self):
        for key in ('module:models', 'module:geometry', 'module:exact', 's3_radius'):
            with self.subTest(key=key):
                receipt = copy.deepcopy(self.receipt)
                receipt['source_sha256'][key] = '0' * 64
                with self.assertRaisesRegex(ValueError, 'S3 source inventory or digest mismatch'):
                    self.invoke(self.provenance, receipt)

    def test_changed_executable_bytes_rejected(self):
        original = audit_stage3.file_digest
        for name in ('stage2.py', 's3_radius.py'):
            with self.subTest(name=name), patch.object(audit_stage3, 'file_digest',
                    side_effect=lambda path: '0' * 64 if Path(path).name == name else original(path)):
                with self.assertRaisesRegex(ValueError, 'S2 source inventory or digest mismatch'):
                    self.invoke(self.provenance, self.receipt)


if __name__ == '__main__':
    unittest.main()
