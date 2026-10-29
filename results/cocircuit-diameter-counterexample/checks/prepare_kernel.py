#!/usr/bin/env python3
"""Apply the exact kernel-reduction transformation to generated proof sources."""
import argparse
from pathlib import Path
import json

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--generated',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--public-export', action='store_true',
                    help='apply the frozen public header/import and control module names')
    a=ap.parse_args();m=json.loads((a.generated/'manifest.json').read_text())
    names=[f'SourceKernelChunk{i}' for i in range(m['chunks'])]+['SourceKernelComplete']
    module_map={n:n+'KernelAsync' for n in names}
    decision=('run_tac Lean.Elab.Tactic.liftMetaTactic fun g => g.withContext do\n'
              '    let pf ← Lean.Meta.mkDecideProof (← g.getType)\n'
              '    g.assign pf\n    pure []')
    a.out.mkdir(parents=True,exist_ok=True)
    for p in sorted(a.generated.glob('*.lean')):
        raw=p.read_text();name=p.name
        if p.stem in module_map:
            raw=raw.replace('by decide','by\n  '+decision).replace('\n  decide\n','\n  '+decision+'\n')
            for before,after in module_map.items():raw=raw.replace('import '+before+'\n','import '+after+'\n')
            name=module_map[p.stem]+'.lean'
        if a.public_export and m['kind']=='control':
            name=name.replace('SourceKernel','ControlKernel')
            raw=raw.replace('import SourceKernel','import ControlKernel')
        (a.out/name).write_text(raw, encoding='utf-8', newline='\n')
if __name__=='__main__':main()
