#!/usr/bin/env python3
"""Filipi checker F2 (pure Python on the operation table; imports nothing
from the other checkers).

Input: the conjugation table of a finite conjugacy-closed set C, written by
checks/build_table.py: n*n little-endian uint16, T[x, y] = index of y x y^-1.
Column y is the permutation R_y : x -> y x y^-1 of C.

For c, z in C and an integer k, c^k z c^-k = R_c^k(z), so
  - c^k commutes with z  iff  R_c^k(z) = z  iff  l_c(z) divides k,
    where l_c(z) is the length of the cycle of R_c through z;
  - c^k is central in G = <C>  iff  it commutes with every element of C
    iff  ord(R_c) divides k.
So Filipi's Conjecture 4.1 (arXiv 2503.22377) holds at c iff some z in C has
l_c(z) = ord(R_c), and it fails at c iff R_c has no cycle of length
ord(R_c) = lcm of its cycle lengths.

The checker verifies that every column is a permutation of C, that <C> is
transitive on C (orbit of element 0 under all columns), so C is one
conjugacy class of G = <C>, and that the conclusion fails at every c in C.
Exit 0 (ACCEPT) only then.

usage: check_filipi_table.py N TABLE.bin
"""
import resource, sys, time
from array import array
from math import gcd

t0 = time.process_time()
n = int(sys.argv[1])
T = array("H")
with open(sys.argv[2], "rb") as f:
    T.frombytes(f.read())
if sys.byteorder != "little":
    T.byteswap()
if len(T) != n * n:
    print("REJECT: table size %d is not %d^2" % (len(T), n)); sys.exit(1)
cols = [T[y::n] for y in range(n)]  # cols[y][x] = T[x, y] = R_y(x)
for y in range(n):
    if sorted(cols[y]) != list(range(n)):
        print("REJECT: R_%d is not a permutation of C" % y); sys.exit(1)

types = set()
for c in range(n):
    R = cols[c]; seen = bytearray(n); lens = set()
    for x in range(n):
        if seen[x]:
            continue
        L = 0; y = x
        while not seen[y]:
            seen[y] = 1; y = R[y]; L += 1
        lens.add(L)
    o = 1
    for L in lens:
        o = o * L // gcd(o, L)
    types.add((o, max(lens)))
    if o in lens:
        print("REJECT: at c = %d, R_c has a cycle of length ord(R_c) = %d: the conjecture's z exists" % (c, o))
        sys.exit(1)
print("every c in C: (ord(R_c), longest cycle) in", sorted(types), "-> no cycle of length ord(R_c)")

orbit = bytearray(n); orbit[0] = 1; front = [0]; size = 1
while front:
    new = []
    for x in front:
        for y in range(n):
            z = cols[y][x]
            if not orbit[z]:
                orbit[z] = 1; new.append(z); size += 1
    front = new
print("orbit of element 0 under all R_y: %d of %d" % (size, n))
if size != n:
    print("REJECT: <C> not transitive on C"); sys.exit(1)
print("ACCEPT: C is a conjugacy class of G = <C>; Filipi's Conjecture 4.1 fails at every c in C")
print("CPU %.1f s, peak %d MB" % (time.process_time() - t0,
      resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024))
