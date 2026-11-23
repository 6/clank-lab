"""Tallies asked for by review round 56. Not part of the frozen test; reads units files only.

usage: tallies.py OUT.json units-DAY.npz ...

With the real labels, per sample date and in total: scored link-slots; link-slots with labels;
covered ones (coverage mask), crossed (covered, high-track distance <= 5 km) and uncrossed
(covered, high-track distance >= 25 km and any-airborne distance >= 5 km); the planted
link-slots (the units file's plant mask), how many of them are crossed with labels, and how
many are covered and crossed; and the median great-circle length of covered crossed and of
covered uncrossed link-slots, each link-slot weighted once.
"""
import sys, json
import numpy as np

def main(out, paths):
    per, Lc, Lu = {}, [], []
    tot = {}
    for p in sorted(paths):
        D = np.load(p, allow_pickle=False)
        have, cov, dh, da, L, plant = D["have"], D["cov"], D["dh"], D["da"], D["length"], D["plant"]
        base = have & cov
        cr = base & (dh <= 5.0); un = base & (dh >= 25.0) & (da >= 5.0)
        r = dict(scored=int(len(L)), labeled=int(have.sum()), covered=int(base.sum()), crossed=int(cr.sum()),
                 uncrossed=int(un.sum()), crossed_labeled=int((have & (dh <= 5.0)).sum()),
                 planted=int(plant.sum()), planted_covered_crossed=int((plant & cr).sum()))
        per[str(D["day"])] = r
        for k, v in r.items():
            tot[k] = tot.get(k, 0) + v
        Lc.append(L[cr].astype(np.float32)); Lu.append(L[un].astype(np.float32))
    Lc, Lu = np.concatenate(Lc), np.concatenate(Lu)
    tot.update(median_length_crossed_km=round(float(np.median(Lc)), 1),
               median_length_uncrossed_km=round(float(np.median(Lu)), 1),
               planted_share_of_crossed_labeled=round(tot["planted"] / tot["crossed_labeled"], 5))
    json.dump(dict(total=tot, per_date=per), open(out, "w"), indent=1)
    print(json.dumps(tot))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
