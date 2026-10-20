"""Complete fresh reconstruction of every cycle and root, plus corruptions."""
import gzip
import hashlib
import json
from pathlib import Path
import tempfile
from receipt_policy import compare_receipt, read_receipt
from replay import build
from stage1 import run
from compare import compare_omega,compare_cycles,RECORDED_OMEGA

HERE=Path(__file__).resolve().parent


def equal_file(actual,expected,compressed=False):
    # Stored certificates remain byte-authenticated. Regenerated outputs are
    # accepted by parsed scientific values, independent of JSON key ordering.
    a=read_receipt(actual)
    b=json.loads(gzip.decompress(Path(expected).read_bytes())) if compressed else read_receipt(expected)
    compare_receipt(a, b, Path(actual).name)


def main():
    with tempfile.TemporaryDirectory(prefix='independent-s1-') as name:
        work=Path(name)
        records,edges,cells,exact=build()
        result=run(edges,cells,exact,work)
        equal_file(work/'cycles.json',HERE/'evidence/cycles.json.gz',True)
        equal_file(work/'omega.json',HERE/'evidence/omega.json')
        compare_receipt(result, read_receipt(HERE/'evidence/stage1-result.json'),
                        'stage1-result.json')
        compared=compare_omega(work/'omega.json',RECORDED_OMEGA)
        cycle_comparison=compare_cycles(work/'cycles.json')
        compare_receipt({'omega':compared, 'cycles':cycle_comparison},
                        read_receipt(HERE/'evidence/comparison.json'), 'comparison.json')
        original=(work/'omega.json').read_bytes()
        modifications=[]
        for tag,fn in [
            ('missing root',lambda d:d['intervals'].pop()),
            ('shifted root',lambda d:d['intervals'][0].__setitem__(slice(0,2),['2','3'])),
            ('unbounded root',lambda d:d['intervals'][0].__setitem__(1,'inf')),
        ]:
            data=json.loads(original)
            fn(data)
            (work/'bad.json').write_text(json.dumps(data))
            try:
                compare_omega(work/'bad.json',RECORDED_OMEGA)
            except (ValueError,OverflowError):
                modifications.append(tag)
            else:
                raise AssertionError('accepted corrupted Omega: '+tag)
        # Alter a genuine cycle's status; compare the full canonical-word set.
        data=json.loads((work/'cycles.json').read_text())
        data[0]['status']='NO_ROOT'
        (work/'bad-cycle.json').write_text(json.dumps(data))
        try:
            compare_cycles(work/'bad-cycle.json')
        except ValueError:
            modifications.append('altered cycle status')
        else:
            raise AssertionError('accepted corrupted cycle status')
        receipt = {'status':'CERTIFIED', 'full_stage1_replay':result,
                   'comparison':compared, 'corruptions_rejected':modifications}
        compare_receipt(receipt, read_receipt(HERE/'evidence/stage1-verification.json'),
                        'stage1-verification.json')
        print(json.dumps(receipt, sort_keys=True))

if __name__=='__main__':main()
