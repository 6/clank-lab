"""Frozen S23 scientific output accepts representation changes, not new claims."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from provenance import check_frozen_science, scientific_records


class OutputPolicy(unittest.TestCase):
    def test_result_and_state_scientific_snapshots(self):
        for field in ('scientific_results','scientific_states'):
            with self.subTest(field=field),tempfile.TemporaryDirectory() as temp:
                p=Path(temp)/'output.jsonl'
                row={'index':4,'status':'COMPLETE','statistics':{'cpu_seconds':1.0,'nodes':17},
                     'realisations':[{'status':'KNOWN','names':['control'],'local_uniqueness':{'forced':True}}]}
                p.write_text(json.dumps(row)+'\n');receipt={field:scientific_records(p)}
                reordered=dict(reversed(list(row.items())))
                reordered['statistics']['cpu_seconds']=9876.5
                p.write_text(json.dumps(reordered)+'\n');check_frozen_science(receipt,p,field)
                for mutate in (lambda r:r.update(status='OPEN'),
                               lambda r:r['statistics'].update(nodes=18),
                               lambda r:r['realisations'][0].update(names=['other']),
                               lambda r:r['realisations'][0]['local_uniqueness'].update(forced=1)):
                    bad=copy.deepcopy(reordered);mutate(bad);p.write_text(json.dumps(bad)+'\n')
                    with self.assertRaisesRegex(ValueError,'scientific output differs'):check_frozen_science(receipt,p,field)

    def test_malformed_records_reject(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'output'
            for raw in ('{"index": 1, "index": 2}', '{"index": 1, "elapsed_seconds": NaN}',
                        '{"index": 1, "elapsed_seconds": -1}', '{"index": 1, "elapsed_seconds": true}', '{"index": 1, "witness": 1e999}',
                        '{"index": 1, "elapsed_seconds": 1e999}'):
                p.write_text(raw)
                with self.subTest(raw=raw),self.assertRaises(ValueError):scientific_records(p)

    def test_legacy_byte_pin_is_provenance_only(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'results';p.write_text('{"status":"COMPLETE","index":7}\n')
            receipt={'sha256':'historical','classes':1,'open':0}
            check_frozen_science(receipt,p)
            receipt['classes']=2
            with self.assertRaisesRegex(ValueError,'scientific counts'):check_frozen_science(receipt,p)


if __name__=='__main__':unittest.main()
