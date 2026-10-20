"""End-to-end snub-prism orientation control, from pinned class144."""
import argparse,json
from pathlib import Path
from unittest.mock import patch
from flint import ctx
import chiral_provider
from stage2 import search_class
from stage3 import check_class
from s3_orient import orientation_options
from s3_stars import model_symmetries


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--class',dest='classes',default='p6-class144-pin.json')
    a=p.parse_args();ctx.prec=320
    rows=json.loads(Path(a.classes).read_text());rows=rows if isinstance(rows,list) else [rows]
    c=next(r for r in rows if r['index']==144)
    ns={n for cy in c['cycles'] for n in cy['facets']}
    ms={n:chiral_provider.facet(n) for n in ns}
    m=ms['pr-snic']
    if not (len(m.stabilizers)==2 and len(model_symmetries(m,m.base_index))==1):
        raise AssertionError()
    if not (len(orientation_options(m))==2):
        raise AssertionError()
    s2=search_class(c,ms)
    if not (not s2.open_reasons and len(s2.states)==8):
        raise AssertionError()
    Q=chiral_provider.known('product-3-snic')
    # The optional separation guard eliminates the wrong orientation before
    # known identification. Logical elimination needs NO full5D orbit.
    def forbidden(_):raise AssertionError('chiral sole route expanded full5D orbit')
    with patch.object(type(Q),'points5',property(forbidden)),patch.object(type(Q),'neighbours',property(forbidden)):
        result=check_class(s2.record(include_states=True),chiral_provider,[Q.name],node_limit=5000)
    if not (result['status']=='COMPLETE'):
        raise AssertionError(result)
    if not (sorted(r['status'] for r in result['realisations'])==['KNOWN','REFUTED']):
        raise AssertionError()
    if not (sum(len(r['states']) for r in result['realisations'])==32):
        raise AssertionError()
    refuted=next(r for r in result['realisations'] if r['status']=='REFUTED')
    if not (refuted['separation_witness']['squared_distance']):
        raise AssertionError()
    known=next(r for r in result['realisations'] if r['status']=='KNOWN')
    if not (known['radius']['status']=='UNIQUE' and known['local_uniqueness']['status']=='FORCED'):
        raise AssertionError()
    if not (result['identification']['known'][0]['checks'][0]['status']=='SOLE-REMAINING'):
        raise AssertionError()
    print('PASS chiral32 orientations->2 exact groups: wrong mirror REFUTED, product-3-snic KNOWN+LU; full5D orbit forbidden')

if __name__=='__main__':main()
