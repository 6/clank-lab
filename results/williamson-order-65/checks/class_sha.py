"""Append the SHA-256 of each class's ascending uint32-LE masks to classes.tsv rows (stdout)."""
import hashlib, sys
import numpy as np
d = sys.argv[1]
rows = np.memmap(d + "/rows.bin", dtype="<u4", mode="r")
for line in open(d + "/classes.tsv"):
    f = line.split("\t")
    c, o = int(f[4]), int(f[5])
    seg = np.asarray(rows[o:o + c])
    assert c == 1 or bool(np.all(seg[1:] > seg[:-1]))
    print(line.rstrip("\n") + "\t" + hashlib.sha256(seg.tobytes()).hexdigest())
