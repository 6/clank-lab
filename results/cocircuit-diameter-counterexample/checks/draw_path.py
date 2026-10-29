#!/usr/bin/env python3
"""Check the supplied factor path and draw its two-factor concatenation."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path)
    args = parser.parse_args()
    if args.certificate:
        raw = gzip.decompress(args.certificate.read_bytes())
    else:
        parts = sorted((root / 'data').glob('source-certificate.json.gz.part*'))
        assert parts, 'missing source-certificate parts'
        raw = gzip.decompress(b''.join(p.read_bytes() for p in parts))
    cert = json.loads(raw)
    path, labels = cert['endpoint_path'], cert['labels']
    assert len(path) == 22
    assert [path[0], path[-1]] == cert['endpoints']
    assert labels[path[0]] == list(range(20))
    assert labels[path[-1]] == list(range(20, 40))
    edges = {tuple(sorted(e)) for e in cert['edges']}
    for step, vertex in enumerate(path):
        assert cert['potential'][vertex] == step
    for u, v in zip(path, path[1:]):
        assert tuple(sorted((u, v))) in edges
        assert len(set(labels[u]) & set(labels[v])) == 19
    product_path = [(i, 0) for i in range(22)] + [(21, j) for j in range(1, 22)]
    zero_sets = [set(labels[path[i]]) | {x + 40 for x in labels[path[j]]}
                 for i, j in product_path]
    assert len(product_path) == 43
    assert all(len(z) == 40 for z in zero_sets)
    assert zero_sets[0].isdisjoint(zero_sets[-1])
    assert len(zero_sets[0] | zero_sets[-1]) == 80
    assert all(len(u & v) == 39 for u, v in zip(zero_sets, zero_sets[1:]))
    plt.rcParams.update({'svg.hashsalt': 'cocircuit-product-path', 'font.size': 14})
    fig, ax = plt.subplots(figsize=(6.5, 2.0))
    x, y = zip(*product_path)
    ax.plot(x, y, '-o', color=(37/255, 94/255, 168/255), markersize=3, linewidth=2)
    ax.set_xlim(-1, 22)
    ax.set_ylim(-1, 22)
    ax.set_xticks([0, 21], ['U', 'V'])
    ax.set_yticks([0, 21], ['U', 'V'])
    ax.set_xlabel('factor 1')
    ax.set_ylabel('factor 2')
    ax.text(10, 3, '21 steps', ha='center')
    ax.annotate('(U,U)', (0, 0), xytext=(3, 8), textcoords='offset points')
    ax.annotate('(V,U)', (21, 0), xytext=(-5, 8), textcoords='offset points', ha='right')
    ax.annotate('(V,V)', (21, 21), xytext=(-8, -4), textcoords='offset points', ha='right')
    ax.text(20, 11, '21 steps', ha='right')
    ax.spines[['top', 'right']].set_visible(False)
    fig.tight_layout(pad=0.5)
    data = root / 'data'
    data.mkdir(exist_ok=True)
    fig.savefig(data / 'product-path.svg', metadata={'Date': None})
    svg = data / 'product-path.svg'
    svg_text = svg.read_text().replace('#{:02x}{:02x}{:02x}'.format(37, 94, 168), 'rgb(37,94,168)')
    svg.write_text('\n'.join(line.rstrip() for line in svg_text.splitlines()) + '\n')
    fig.savefig(data / 'product-path.pdf', metadata={'CreationDate': None, 'ModDate': None})
    plt.close(fig)
    report = {'source_certificate_sha256': hashlib.sha256(raw).hexdigest(),
              'factor_path': path, 'product_path': product_path,
              'factor_edges': 21, 'product_edges': 42,
              'checks': 'source edges, potential increments, complementary endpoints, 39 common product labels',
              'meaning': 'coordinates are positions on the two supplied factor paths; not an embedding of the full graph'}
    (data / 'product-path.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS figure data: two checked 21-edge factor paths, 42 product steps')


if __name__ == '__main__':
    main()
