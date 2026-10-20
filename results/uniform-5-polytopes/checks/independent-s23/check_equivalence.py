"""Check exact option coverage independently of the gluing/enumeration module."""


def check(model, certificate):
    count=len(model.vf_points)
    options=[]
    for rid,r in enumerate(model.ridges):
        a=list(r['vertices'])
        for row in (a,list(reversed(a))):
            for shift in range(len(row)):
                option = [rid,row[shift:]+row[:shift]]
                if option not in options:
                    options.append(option)
    if certificate['options']!=options:
        raise ValueError('correspondence coverage/order')
    retained=certificate['retained']
    if retained!=sorted(set(retained)) or any(i<0 or i>=len(options) for i in retained):
        raise ValueError('invalid retained indices')
    records=certificate['records']
    if len(records)!=len(options): raise ValueError('missing correspondence witness')
    for i,row in enumerate(records):
        if row['option']!=i or row['representative'] not in retained:
            raise ValueError('invalid representative')
        j=row['representative'];p=row['permutation']
        if sorted(p)!=list(range(count)): raise ValueError('not a permutation')
        if not model.verify_stabilizer(tuple(p)):
            raise ValueError('not an exact symmetry')
        r,source=options[j];s,target=options[i]
        if [p[x] for x in source]!=target:
            raise ValueError('wrong ordered correspondence')
        if model.ridges[r]['label']!=model.ridges[s]['label']:
            raise ValueError('wrong label')
        faces={(tuple(sorted(f['vertices'])),f['label']) for f in model.ridges}
        for f in model.ridges:
            if (tuple(sorted(p[x] for x in f['vertices'])),f['label']) not in faces:
                raise ValueError('labelled face not preserved')
            vertices=f['vertices'];mapped=[p[x] for x in vertices]
            targetface=next(g['vertices'] for g in model.ridges if set(g['vertices'])==set(mapped))
            variants=[]
            for v in (list(targetface),list(reversed(targetface))):
                variants.extend(v[k:]+v[:k] for k in range(len(v)))
            if mapped not in variants: raise ValueError('cyclic order not preserved')
        for (a,b),size in model.edge_p.items():
            if model.edge_p.get(tuple(sorted((p[a],p[b]))))!=size:
                raise ValueError('polygon type not preserved')
        if i in retained and (j!=i or p!=list(range(count))):
            raise ValueError('retained option not its own identity representative')
    return len(records)


def main():
    import argparse,json
    from pathlib import Path
    from models import facet
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('classes',type=Path);p.add_argument('certificate',type=Path)
    a=p.parse_args();classes=json.loads(a.classes.read_text())
    wanted={name for c in classes for cy in c['cycles'] for name in cy['facets']}
    certificates=json.loads(a.certificate.read_text())
    if set(certificates)!=wanted:raise ValueError('facet model coverage mismatch')
    count=sum(check(facet(n),certificates[n]) for n in sorted(wanted))
    print(json.dumps({'status':'PASS','models':len(wanted),'ordered_options_checked':count}))


if __name__=='__main__':main()
