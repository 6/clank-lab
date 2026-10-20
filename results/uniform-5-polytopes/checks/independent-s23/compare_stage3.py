"""Compare frozen S3 conclusions; report raw search multiplicities separately.

The recorded S3 format retains facet multisets and cycle counts, not full
cyclic words. Its per-signature list follows the supplied u3_vfs input
order. Recover words from that pinned input and verify every coarse key.
Complete word signatures are also compared by compare.py independently.
No recorded output is used by either independent proof implementation.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
from combinatorics import signature_key
from provenance import parsed_json, check_frozen_science


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def key(signature):
    return (tuple(sorted(signature['facets'])),
            len(signature['cycles']) if 'cycles' in signature else signature['n_cycles'])


def index(rows):
    answer={}
    for row in rows:
        if row['index'] in answer:raise ValueError('duplicate class index')
        answer[row['index']]=row
    return answer


def conclusions(realisations,independent):
    names=set();counts=Counter();failures=[]
    for r in realisations:
        status=r['status' if independent else 'verdict'];counts[status]+=1
        if status=='KNOWN':
            names.update(r['names' if independent else 'known_names'])
            radius=(r.get('radius',{}).get('status')=='UNIQUE' if independent else r.get('unique_root'))
            forced=(r.get('local_uniqueness',{}).get('status')=='FORCED' if independent else r.get('local_uniqueness',{}).get('forced'))
            if not radius or not forced:failures.append('KNOWN without unique radius and local uniqueness')
        elif status!='REFUTED':failures.append('unresolved verdict '+status)
    if not realisations:failures.append('no realisations')
    return {'names':sorted(names),'wholly_refuted':bool(realisations) and counts['REFUTED']==len(realisations),
            'counts':dict(sorted(counts.items())),'failures':failures}


def compare(ours,reference,reference_signatures):
    ours=index(ours);reference=index(reference['classes']);pins=index(reference_signatures)
    if set(reference)!=set(pins):raise ValueError('recorded class/input coverage mismatch')
    differences=[];multiplicities=[];summaries=[]
    if set(ours)!=set(reference):
        differences.append({'classes_missing':sorted(set(reference)-set(ours)),
                            'classes_extra':sorted(set(ours)-set(reference))})
    for i in sorted(set(ours)&set(reference)):
        row=ours[i];ref=reference[i];groups=defaultdict(list)
        if row['status']!='COMPLETE':differences.append({'index':i,'status':row['status']})
        for r in row['realisations']:
            groups[signature_key(r['signature'])].append(r)
        refs={}
        for v,s in zip(ref['vfs'],pins[i]['vfs'],strict=True):
            if key(v)!=key(s):raise ValueError(f'class {i}: recorded signature order differs from pinned input')
            k=signature_key(s)
            if k in refs:raise ValueError(f'class {i}: duplicate recorded signature')
            refs[k]=v['realisations']
        if set(groups)!=set(refs):
            differences.append({'index':i,'signatures_missing':sorted(set(refs)-set(groups)),
                                'signatures_extra':sorted(set(groups)-set(refs))})
        for k in sorted(set(groups)&set(refs)):
            a=conclusions(groups[k],True);b=conclusions(refs[k],False)
            description={'index':i,'facets':list(k[0]),'cycles':k[1],'n_cycles':len(k[1])}
            if a['failures'] or b['failures'] or (a['names'],a['wholly_refuted'])!=(b['names'],b['wholly_refuted']):
                differences.append(dict(description,independent=a,recorded=b))
            if a['counts']!=b['counts']:
                multiplicities.append(dict(description,independent=a['counts'],recorded=b['counts']))
            summaries.append(dict(description,names=a['names'],wholly_refuted=a['wholly_refuted'],
                                  independent_counts=a['counts'],recorded_counts=b['counts']))
    return {'classes':len(ours),'vertex_figures':len(summaries),
            'known_signatures':sum(bool(s['names']) for s in summaries),
            'wholly_refuted_signatures':sum(s['wholly_refuted'] for s in summaries),
            'conclusion_differences':differences,'raw_multiplicity_differences':multiplicities,
            'signatures':summaries}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('independent',type=Path);p.add_argument('reference',type=Path)
    p.add_argument('--reference-signatures',type=Path,required=True)
    p.add_argument('--receipt',type=Path,required=True);p.add_argument('--output',type=Path)
    a=p.parse_args();receipt=parsed_json(a.receipt.read_text())
    check_frozen_science(receipt,a.independent)
    if receipt.get('comparison_performed') is not False:raise ValueError('missing pre-comparison freeze')
    own=[parsed_json(t) for t in a.independent.read_text().splitlines() if t.strip()]
    result=compare(own,parsed_json(a.reference.read_text()),parsed_json(a.reference_signatures.read_text()))
    result.update(independent_sha256=digest(a.independent),reference_sha256=digest(a.reference))
    result['reference_signatures_sha256']=digest(a.reference_signatures)
    if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('signatures','raw_multiplicity_differences')},indent=2))
    print('Raw multiplicity differences:',len(result['raw_multiplicity_differences']))
    return int(bool(result['conclusion_differences']))


if __name__=='__main__':raise SystemExit(main())
