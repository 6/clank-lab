"""unit_recheck: a second, separately written implementation of the per-unit filter and join.

Usage: python3 -I unit_recheck.py n m datadir receiptdir (--all | --units i,j,... | --sample K SEED) [--threads T]

For each unit it rebuilds the four row lists from rows.bin (own kernel-minimal test, by
permuting entries of full +-1 rows), computes the spectra with numpy (own cosine matrix,
own summation), applies the two-sided pair test described in ../paper/paper.tex with its own
quantization, and joins the surviving pairs on the exact PAF-sum vectors (through an
independent 64-bit linear hash, every candidate verified exactly; the product theorem is
not used). It reports, per unit: list sizes against the receipt, survivor counts against
the receipt (skipped when a quantized value is within 1e-7 of a rounding boundary, where
two correct implementations may differ), key matches and exact solutions found.
Shares no code with search.c. Exit 0 iff every size and every comparable survivor count
agrees and every unit's solution count agrees with the receipt."""
import os, sys
from math import gcd
from concurrent.futures import ProcessPoolExecutor
import numpy as np

PAIRS = [(0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2)]
G = {}


def setup(n, m, dd, rd):
    H, L = (n - 1) // 2, n // m
    G.update(n=n, m=m, H=H, L=L)
    G["rows"] = np.memmap(os.path.join(dd, "rows.bin"), dtype="<u4", mode="r")
    G["cls"] = [(int(f[4]), int(f[5])) for f in (l.split("\t") for l in open(os.path.join(dd, "classes.tsv")))]
    G["units"] = [tuple(int(v) for v in l.split()[1:5]) for l in open(os.path.join(dd, "units.tsv"))]
    rec = {}
    for fn in os.listdir(rd):
        if fn.startswith("batch_") and fn.endswith(".tsv"):
            for line in open(os.path.join(rd, fn)):
                f = line.rstrip("\n").split("\t")
                if f[0] == "U":
                    rec[int(f[1])] = [int(v) for v in f[1:19]]
    G["rec"] = rec
    i = np.arange(H + 1)[:, None]; k = np.arange(1, H + 1)[None, :]
    C = 2.0 * np.cos(2.0 * np.pi * ((i * k) % n) / n)
    C[0, :] = 1.0
    G["C"] = C
    G["K"] = [u for u in range(2, n) if gcd(u, n) == 1 and u % L == 1]
    rng = np.random.default_rng(20261022)
    G["W"] = rng.integers(0, 2 ** 63, size=H, dtype=np.int64).astype(np.uint64) * np.uint64(2) + np.uint64(1)


def full_rows(masks):
    n, H = G["n"], G["H"]
    bits = ((masks[:, None] >> np.arange(H, dtype=np.uint32)[None, :]) & 1).astype(np.int8)
    half = 1 - 2 * bits  # x_1..x_H
    x = np.ones((len(masks), n), dtype=np.int8)
    x[:, 1:H + 1] = half
    x[:, n - H:] = half[:, ::-1]  # x_{n-i} = x_i
    return x


def to_mask(x):
    H = G["H"]
    b = (x[:, 1:H + 1] < 0).astype(np.uint64)
    return (b << np.arange(H, dtype=np.uint64)[None, :]).sum(axis=1).astype(np.uint32)


def kmin(masks):
    n = G["n"]
    x = full_rows(masks)
    keep = np.ones(len(masks), dtype=bool)
    for u in G["K"]:
        img = x[:, (u * np.arange(n)) % n]
        keep &= to_mask(img) >= masks
    return masks[keep]


def rowdata(masks):
    n, H = G["n"], G["H"]
    x = full_rows(masks)
    lam = x[:, :H + 1].astype(np.float64) @ G["C"]
    q = 64.0 * lam * lam
    lo = np.maximum(0, np.floor(q - 0.01)).astype(np.int32)
    hi = np.ceil(q + 0.01).astype(np.int32)
    amb = bool(np.any(np.abs((q - 0.01) - np.round(q - 0.01)) < 1e-7) or np.any(np.abs((q + 0.01) - np.round(q + 0.01)) < 1e-7))
    xi = x.astype(np.int32)
    paf = np.stack([(xi * np.roll(xi, -s, axis=1)).sum(axis=1) for s in range(1, H + 1)], axis=1)
    h = (paf.astype(np.int64).astype(np.uint64) * G["W"][None, :]).sum(axis=1, dtype=np.uint64)
    return dict(mask=masks, lo=lo, hi=hi, amb=amb, paf=paf, h=h)


def side_pairs(X, Y, Z, W):
    T = 64 * 4 * G["n"]
    U = np.maximum(0, T - Z["lo"].min(axis=0) - W["lo"].min(axis=0)) if len(Z["mask"]) and len(W["mask"]) else np.zeros(G["H"], dtype=np.int64)
    Lb = np.maximum(0, T - Z["hi"].max(axis=0) - W["hi"].max(axis=0)) if len(Z["mask"]) and len(W["mask"]) else np.zeros(G["H"], dtype=np.int64)
    order = np.argsort(U - Lb)  # any order gives the same survivors; tight frequencies first
    out_a, out_b = [], []
    loY, hiY = Y["lo"], Y["hi"]
    for a in range(len(X["mask"])):
        cand = np.arange(len(Y["mask"]))
        la, ha = X["lo"][a], X["hi"][a]
        for k in order:
            if not len(cand):
                break
            sel = (loY[cand, k] + la[k] <= U[k]) & (hiY[cand, k] + ha[k] >= Lb[k])
            cand = cand[sel]
        if len(cand):
            out_a.append(np.full(len(cand), a, dtype=np.int64)); out_b.append(cand)
    if out_a:
        return np.concatenate(out_a), np.concatenate(out_b)
    return np.zeros(0, dtype=np.int64), np.zeros(0, dtype=np.int64)


def one(u):
    rec = G["rec"].get(u)
    c4 = G["units"][u]
    if rec is None:
        return (u, "NO_RECEIPT")
    p, d = rec[5], rec[6]
    sizes_r = rec[7:11]
    lists = []
    for r, c in enumerate(c4):
        cnt, off = G["cls"][c]
        ms = np.array(G["rows"][off:off + cnt], dtype=np.uint32)
        if r == d:
            ms = kmin(ms)
        lists.append(rowdata(ms))
    sizes = [len(Lr["mask"]) for Lr in lists]
    q = PAIRS[p]
    A, B, Cc, D = (lists[i] for i in q)
    la, lb = side_pairs(A, B, Cc, D)
    ra, rb = side_pairs(Cc, D, A, B)
    # receipt survivors are (store, probe): store is the right pair when its product is not larger
    pl, pr = sizes_r[q[0]] * sizes_r[q[1]], sizes_r[q[2]] * sizes_r[q[3]]
    s_store, s_probe = rec[14], rec[15]  # rec = receipt fields 2..19: unit, c1..c4, pairing, desig, s1..s4, npass, pairs_store, pairs_probe, surv_store, surv_probe, matches, sols
    rl, rr = (s_probe, s_store) if pr <= pl else (s_store, s_probe)
    amb = any(Lr["amb"] for Lr in lists)
    keyl = A["h"][la] + B["h"][lb]
    keyr = (np.uint64(0) - (Cc["h"][ra] + D["h"][rb])).astype(np.uint64)
    common = np.intersect1d(keyl, keyr)
    matches, sols = 0, 0
    if len(common):
        il = np.nonzero(np.isin(keyl, common))[0]; ir = np.nonzero(np.isin(keyr, common))[0]
        for i in il:
            for j in ir[keyr[ir] == keyl[i]]:
                matches += 1
                tot = A["paf"][la[i]] + B["paf"][lb[i]] + Cc["paf"][ra[j]] + D["paf"][rb[j]]
                sols += int(not tot.any())
    return (u, sizes == sizes_r, sizes, sizes_r, (len(la), len(ra)), (rl, rr), amb, matches, sols, rec[17])


def main():
    n, m, dd, rd = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    a = sys.argv[5:]
    setup(n, m, dd, rd)
    if a[0] == "--all":
        us = sorted(G["rec"])
    elif a[0] == "--units":
        us = [int(v) for v in a[1].split(",")]
    else:
        rng = np.random.default_rng(int(a[2]))
        us = sorted(int(v) for v in rng.choice(sorted(G["rec"]), size=int(a[1]), replace=False))
    T = int(a[a.index("--threads") + 1]) if "--threads" in a else os.cpu_count()
    ok = True; tot_pairs = 0; tot_sols = 0; n_amb = 0
    with ProcessPoolExecutor(T, initializer=setup, initargs=(n, m, dd, rd)) as ex:
        for res in ex.map(one, us, chunksize=1):
            if res[1] == "NO_RECEIPT":
                print("FAIL unit %d has no receipt" % res[0]); ok = False; continue
            u, size_ok, sizes, sizes_r, surv, surv_r, amb, matches, sols, sols_r = res
            surv_ok = amb or tuple(surv) == tuple(surv_r)
            n_amb += amb
            good = size_ok and surv_ok and sols == sols_r
            ok &= good
            tot_sols += sols
            print("%s unit=%d sizes=%s survivors=%s receipt=%s%s matches=%d solutions=%d receipt_solutions=%d" % (
                "PASS" if good else "FAIL", u, sizes, list(surv), list(surv_r), " (ambiguous quantization: not compared)" if amb else "", matches, sols, sols_r), flush=True)
    print("%s unit_recheck n=%d m=%d units=%d solutions=%d survivor_comparisons_skipped=%d" % ("PASS" if ok else "FAIL", n, m, len(us), tot_sols, n_amb))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
