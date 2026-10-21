"""Compare actual compiled option dumps with all independent, ordered definitions."""
import itertools
from pathlib import Path
import json

def expected():
    data=Path(__file__).resolve().parent.parent/'data'
    enc=lambda x,y,z:81*(x%3)+9*(y%9)+z%9
    dec=lambda a:(a//81,a//9%9,a%9)
    sm=lambda a:enc(*(61*x for x in dec(a)))
    orbits=sorted({tuple(sorted({a,sm(a),sm(sm(a))})) for a in range(243)})
    cell=lambda a:9*(a//81)+3*(a//9%3)+(a%3)
    cases=[list(map(int,l.split()))[1:] for l in (data/'cases.txt').read_text().splitlines()]
    table=[]
    for r in cases:
        positions=[q for am in (6,3) for q in range(27) if q%9 and r[q]==am]
        assert len(positions)==24
        rows=[]
        for q in positions:
            os=[o for o in orbits if len(o)==3 and cell(o[0])==q]
            assert len(os)==3
            ordered=[sorted(e for j,o in enumerate(os) if (r[q]==3)==(a==j) for e in o) for a in range(3)]
            family={tuple(sorted(e for o in cmb for e in o)) for cmb in itertools.combinations(os,r[q]//3)}
            assert set(map(tuple,ordered))==family and len(family)==3
            rows.append(ordered)
        table.append(rows)
    return table

def check(dump,data=None):
    data=data or Path(__file__).resolve().parent.parent/'data'
    orbits=[list(map(int,l.split()))[1:] for l in (data/'p243.txt').read_text().splitlines()[2:] if l.strip()]
    tab=json.loads(Path(dump).read_text())
    points=[[[sorted(e for j in opt for e in orbits[j]) for opt in pos] for pos in case] for case in tab]
    if points!=expected():
        raise ValueError('compiled option family/order differs from independent definitions')
    return points
