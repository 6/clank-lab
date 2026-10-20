"""Verify executable/input identities before replay; prose is not a runtime input."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
OUTPUT_RECEIPTS = frozenset({
    'evidence/comparison.json', 'evidence/stage1-result.json',
    'evidence/stage1-verification.json', 'evidence/b2-comparison.json',
    'library_evidence.jsonl',
})


def main():
    data=json.loads((HERE/'runtime-identities.json').read_text())
    for section,base in [('inputs',HERE.parent),('files',HERE)]:
        for name,expected in data[section].items():
            if section == 'files' and name in OUTPUT_RECEIPTS:
                raise ValueError('output receipt is not a byte-pinned input: '+name)
            if Path(name).suffix.lower() in ('.md', '.tex', '.pdf', '.rst'):
                raise ValueError('mutable prose is not a runtime input: '+name)
            path=base/name
            actual=hashlib.sha256(path.read_bytes()).hexdigest()
            if actual!=expected:
                raise ValueError('identity disagreement: '+section+'/'+name)
    print('PASS frozen identities ('+str(sum(len(x) for x in data.values()))+' files)')

if __name__=='__main__':main()
