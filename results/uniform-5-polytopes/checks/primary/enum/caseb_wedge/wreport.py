"""Markdown tables for RESULT.md from results.jsonl (wrun.py) and
floats.jsonl (wfloat.py witnesses).

    python3 wreport.py results.jsonl floats.jsonl > tables.md
"""
import json
import sys


def load(path):
    out = {}
    try:
        with open(path) as fh:
            for line in fh:
                if line.strip():
                    d = json.loads(line)
                    out[d["fan"]] = d
    except FileNotFoundError:
        pass
    return out


def family(fid):
    k = fid.split(":")[0]
    return {"i": "type (i)", "ii": "type (ii)", "iii": "type (iii)", "pi": "paired type (i)",
            "pii": "paired type (ii)", "pnc": "paired type (i), not closable"}[k]


def main():
    res = load(sys.argv[1])
    flo = load(sys.argv[2]) if len(sys.argv) > 2 else {}
    import wrun
    order = wrun.fan_ids()
    tot = sum(r.get("cpu", 0) for r in res.values())
    counts = {}
    for fid in order:
        r = res.get(fid)
        st = r["status"].split(" (")[0] if r else "MISSING"
        counts[st] = counts.get(st, 0) + 1
    print("Fans: %d; %s.  Total CPU %.0f s (%.1f min)." % (
        len(order), ", ".join("%s %d" % kv for kv in sorted(counts.items())), tot, tot / 60))
    print()
    print("| fan | family | status | param boxes | finest s-box | s-boxes | pair tests | CPU s | max fan-vertex dist |")
    print("|---|---|---|---|---|---|---|---|---|")
    for fid in order:
        r = res.get(fid)
        if r is None:
            print("| %s | %s | MISSING | | | | | | |" % (fid, family(fid)))
            continue
        if "boxes" not in r:
            print("| %s | %s | %s | | | | | %s | |" % (fid, family(fid), r["status"], r.get("cpu", "")))
            continue
        sw = "1/%d" % round(1 / r["finest_s"]) if r["boxes"] else ""
        vm = "%.6f" % r["vmax"] if r.get("vmax") else ""
        print("| %s | %s | %s | %d | %s | %d | %d | %.1f | %s |" % (
            fid, family(fid), r["status"], r["boxes"], sw, r["nodes"], r["pairtests"], r["cpu"], vm))
    failed = [fid for fid in order if fid in res and res[fid]["status"] == "FAILED"]
    print()
    print("FAILED fans (%d), with the first undecided parameter box and a float witness:" % len(failed))
    print()
    print("| fan | undecided at | float max pair | float max p-vertex | witness parameter |")
    print("|---|---|---|---|---|")
    for fid in failed:
        f = res[fid]["failures"][0] if res[fid]["failures"] else {}
        where = "%s, P = %s" % (f.get("kind", ""), [[round(a, 5), round(b, 5)] for a, b in f.get("P", [])])
        fl = flo.get(fid)
        if fl:
            print("| %s | %s | %.4f | %.4f | %s |" % (fid, where, fl["max_pair"], fl["max_vert"],
                                                 [round(t, 4) for t in fl["best"]["P"]]))
        else:
            print("| %s | %s | | | |" % (fid, where))


if __name__ == "__main__":
    main()
