"""Write corrupted copies of certificate.json, one per kind, to DIR."""
import copy, json, os, sys

src, outdir = sys.argv[1], sys.argv[2]
c = json.load(open(src))
os.makedirs(outdir, exist_ok=True)


def save(name, d):
    with open(os.path.join(outdir, name + ".json"), "w") as f:
        json.dump(d, f)


d = copy.deepcopy(c); d["pieces"][2]["vertices"][3][0] = "4/5"; save("vertex-moved", d)
d = copy.deepcopy(c); d["phi"][0][1] = "2"; save("phi-not-similarity", d)
d = copy.deepcopy(c); d["pieces"][3] = copy.deepcopy(d["pieces"][1]); save("piece-duplicated", d)
d = copy.deepcopy(c); d["pieces"] = d["pieces"][:3]; d["separators"] = [s for s in d["separators"] if 3 not in s["pair"]]; save("piece-dropped", d)
d = copy.deepcopy(c); d["separators"][5]["offset"] = "3/2"; save("separator-shifted", d)
d = copy.deepcopy(c); d["pieces"][1]["M"][0][1] = "1/2"; save("M-not-orthogonal", d)
