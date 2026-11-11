#!/usr/bin/env python3
"""GPT-6 Astra, release integration. Replay the two independent witnesses.

The obstruction implementations are unchanged GPT-6.1 Sol programs.
The published minor implementations are pinned by version and SHA-256.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--prior', type=Path, help='local heawood-family-mu5 v1 folder; otherwise fetch pinned files')
    ap.add_argument('--receipts', type=Path, help='save command output and separate CPU/peak-memory receipts here')
    args = ap.parse_args()
    require(sys.version_info >= (3, 12), 'Python 3.12 or later is required')
    require(not sys.flags.optimize, 'run without Python optimization')
    import networkx as nx
    require(nx.__version__ == '3.7', 'install checks/requirements.txt')
    lock = json.loads((ROOT/'checks/prior.json').read_text())
    receipts = args.receipts or Path(tempfile.mkdtemp(prefix='four-flat-receipts-'))
    receipts.mkdir(parents=True, exist_ok=True)
    serial = 0
    with tempfile.TemporaryDirectory(prefix='four-flat-check-') as scratch:
        tmp = Path(scratch)
        prior = args.prior.resolve() if args.prior else tmp/'prior'
        for name, expected in lock['sha256'].items():
            f = prior/name
            if not args.prior:
                f.parent.mkdir(parents=True, exist_ok=True)
                with urllib.request.urlopen(lock['base_url']+name, timeout=30) as response:
                    raw = response.read(2_000_001)
                require(len(raw) <= 2_000_000, 'oversized published dependency')
                f.write_bytes(raw)
            require(digest(f) == expected, 'published dependency hash mismatch: '+name)

        inputs = {str(f.relative_to(ROOT)): digest(f) for d in ('checks','data')
                  for f in (ROOT/d).iterdir() if f.is_file()}
        inputs['paper/paper.tex'] = digest(ROOT/'paper/paper.tex')
        inputs.update({'prior/'+k:v for k,v in lock['sha256'].items()})
        (receipts/'inputs.json').write_text(json.dumps(inputs,sort_keys=True,indent=2)+'\n')

        def run(label, script, *argv, expected=0):
            nonlocal serial
            serial += 1
            stem = receipts/('%02d-%s' % (serial,label))
            output, errors, cost = (Path(str(stem)+s) for s in ('.out','.err','.time'))
            cmd = [sys.executable, '-I', str(script), *map(str,argv)]
            with output.open('wb') as out, errors.open('wb') as err:
                result = subprocess.run(['/usr/bin/time','-f','user=%U system=%S peak_kib=%M',
                                         '-o',str(cost),'timeout','--kill-after=2','600',*cmd],
                                        stdout=out,stderr=err)
            record = {'label':label,'exit':result.returncode,'cost':cost.read_text().strip(),
                      'output_sha256':digest(output),'stderr_sha256':digest(errors)}
            Path(str(stem)+'.json').write_text(json.dumps(record,sort_keys=True)+'\n')
            require(result.returncode == expected, label+' returned unexpected exit status; inspect receipts')
            print(json.dumps(record,sort_keys=True), flush=True)
            return output.read_text()

        docs = {n:json.loads((ROOT/'data'/f'{n}.json').read_text()) for n in ('h','g1','k7')}
        graphs = {}
        for name, doc in docs.items():
            graph = nx.Graph()
            graph.add_nodes_from(range(doc['vertices']))
            graph.add_edges_from(doc['edges'])
            graphs[name] = graph
        refs = dict(line.split() for line in (prior/'data/graphs.g6').read_text().splitlines())
        encode = lambda graph: nx.to_graph6_bytes(graph,header=False).decode().strip()
        require(encode(graphs['g1']) == refs['G1'], 'G1 identity mismatch')
        require(encode(graphs['h']) == 'J?bFF`wN?{?', 'H identity mismatch')
        h_edges = {tuple(e) for e in docs['h']['edges']}
        g_edges = {tuple(e) for e in docs['g1']['edges']}
        require(docs['h']['vertices'] == docs['g1']['vertices'] == 11
                and len(h_edges) == 22 and len(g_edges) == 23
                and (1,10) in g_edges and h_edges == g_edges-{(1,10)}, 'edge deletion mismatch')
        require(docs['k7']['vertices'] == 7 and graphs['k7'].number_of_edges() == 21, 'K7 control mismatch')
        require(len(docs['h']['cycles']) == 46 and len(docs['h']['pairs']) == 79, 'H certificate counts')
        run('appendix',ROOT/'checks/certificate.py')
        for name in ('k7','g1','h'):
            for checker in ('a','b'):
                report = json.loads(run(name+'-'+checker,ROOT/'checks'/f'checker_{checker}.py',ROOT/'data'/f'{name}.json'))
                require(report.get('accepted',report.get('valid')) is True and
                        report.get('intersection',report.get('invariant')) == 1, 'obstruction failed')
        for name in ('g1','h'):
            bad = json.loads((ROOT/'data'/f'{name}.json').read_text())
            bad['pairs'].pop()
            bad_file = tmp/f'{name}-bad.json'
            bad_file.write_text(json.dumps(bad)+'\n')
            for checker in ('a','b'):
                out = run(name+'-corrupt-'+checker,ROOT/'checks'/f'checker_{checker}.py',bad_file,expected=1)
                if checker == 'a':
                    require(out.strip() == 'REJECT: nonzero boundary', 'wrong corruption rejection')
                else:
                    require(json.loads(out) == {'valid':False,'reason':'nonzero boundary at dimension 4'},
                            'wrong corruption rejection')
        # A nonzero cycle with zero boundary but even invariant: two
        # disjoint copies of the known odd K7 cycle. Generate, do not search.
        control = docs['k7']
        n, k = control['vertices'], len(control['cycles'])
        even = {'format': control['format'], 'vertices': 2*n,
                'edges': control['edges'] + [[v+n for v in e] for e in control['edges']],
                'cycles': control['cycles'] + [[v+n for v in c] for c in control['cycles']],
                'pairs': control['pairs'] + [[i+k for i in pair] for pair in control['pairs']]}
        even_file = tmp/'even-cycle.json'
        even_file.write_text(json.dumps(even)+'\n')
        for checker in ('a','b'):
            out = run('even-cycle-'+checker,ROOT/'checks'/f'checker_{checker}.py',even_file,expected=1)
            if checker == 'a':
                require(out.strip() == 'REJECT: even intersection', 'wrong even-cycle rejection')
            else:
                require(json.loads(out) == {'valid':False,'reason':'invariant is zero'},
                        'wrong even-cycle rejection')
        family_file = tmp/'family.json'
        out = run('family',prior/'checks/family.py',family_file)
        require(out.split()[0] == '78' and len(json.loads(family_file.read_text())) == 78, 'family count')
        details = json.loads(run('h-minor-details',ROOT/'checks/minor_details.py',ROOT/'data/h.json',family_file))
        require(details['accepted'] and details['h_and_single_edge_minors_compared'] == 45
                and len(details['proper_minor_apex_witnesses']) == 44, 'direct H minor checks')
        out = run('minor-controls',prior/'checks/minor_exclusion.py',prior/'data/minor-controls.g6',family_file)
        controls = [json.loads(line) for line in out.splitlines()]
        require(len(controls) == 3 and all(r['target_minors_found'] for r in controls), 'minor positive controls')
        g1_file = tmp/'g1.g6'
        g1_file.write_text('G1 '+encode(graphs['g1'])+'\n')
        out = run('minor-a',prior/'checks/minor_exclusion.py',g1_file,family_file)
        rows = [json.loads(line) for line in out.splitlines()]
        require(len(rows) == 1 and rows[0]['graph'] == 'G1' and rows[0]['minors_enumerated'] == 354
                and rows[0]['target_minors_found'] == [], 'minor exclusion A')
        out = run('minor-b',prior/'checks/checker_b.py','minors')
        require('RESULT G1: NO Heawood-family minor' in out.splitlines(), 'minor exclusion B')
    print('PASS: H is not 4-flat and has no Heawood-family minor.')
    print('Two independent obstruction checks and two published minor checks passed; all 44 single-edge minors are 2-apex. No value of mu(H) is checked.')


if __name__ == '__main__':
    main()
