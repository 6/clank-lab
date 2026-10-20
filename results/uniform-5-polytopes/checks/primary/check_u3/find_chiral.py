"""print CLASS:VF:FACETTYPE for corruption (b): the first vertex figure with a
KNOWN realisation that has a chiral facet (pr-snic preferred)."""
import json
import sys
res = json.load(open(sys.argv[1]))
for want in ('pr-snic', 'pr-snid'):
    for c in res['classes']:
        for k, v in enumerate(c['vfs']):
            if want in v['facets'] and any(r['verdict'] == 'KNOWN' for r in v.get('realisations', [])):
                print('%d:%d:%s' % (c['index'], k, want))
                sys.exit(0)
sys.exit("no chiral facet in a known vertex figure")
