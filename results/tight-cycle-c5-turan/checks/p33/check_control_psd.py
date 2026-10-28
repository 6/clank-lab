#!/usr/bin/env python3
"""Standalone exact PSD/sign checker for the compact published control.

Fraction-free Schur elimination; imports no exporter, generator, search,
or optimizer. The companion C++ program checks all semantic identities.
"""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
try:
    from gmpy2 import mpz as integer
except ImportError:
    integer = int


def psd(A):
    n = len(A); previous = integer(1); rank = 0
    for i in range(n):
        pivot = A[i][i]
        if pivot < 0:
            raise ValueError('negative fraction-free Schur pivot')
        if pivot == 0:
            if any(A[i][j] for j in range(i + 1, n)):
                raise ValueError('zero Schur diagonal with nonzero off-diagonal')
            continue
        rank += 1
        for j in range(i + 1, n):
            for k in range(j, n):
                value, remainder = divmod(pivot*A[j][k] - A[i][j]*A[i][k], previous)
                if remainder:
                    raise ValueError('fraction-free division not exact')
                A[j][k] = A[k][j] = value
        previous = pivot
    return rank


def main():
    start=time.monotonic();raw=Path(sys.argv[1]).read_bytes()
    if raw[:2]==b'\x1f\x8b':raw=gzip.decompress(raw)
    data=iter(map(integer,raw.split()))
    scale,den,nb,ng,nh=[int(next(data)) for _ in range(5)]
    if (scale,den,nb,ng,nh)!=(230400,829440000,33,9,28080):raise ValueError('header')
    ranks=[]
    for _ in range(nb):
        n,k,typ,d=[int(next(data)) for _ in range(4)]
        flags=[int(next(data)) for _ in range(d)]
        if len(set(flags))!=d or n*2-k!=6:raise ValueError('flag basis')
        A=[[next(data) for _ in range(d)] for _ in range(d)]
        if any(A[i][j]!=A[j][i] for i in range(d) for j in range(i)):raise ValueError('asymmetric block')
        ranks.append(psd(A))
    multipliers=0
    for group in range(ng):
        n,k,typ,d=[int(next(data)) for _ in range(4)]
        flags=[int(next(data)) for _ in range(d)];values=[next(data) for _ in range(d)]
        sign=-1 if group in (3,5,7) else 1
        if any(sign*v<0 for v in values):raise ValueError('negative original multiplier')
        multipliers+=d
    for _ in range(nh):
        e,c,slack=[next(data) for _ in range(3)]
        if slack<0:raise ValueError('negative slack')
    try:next(data)
    except StopIteration:pass
    else:raise ValueError('trailing records')
    if multipliers!=302:raise ValueError('multiplier count')
    print(json.dumps({'status':'EXACT_PSD_AND_SIGNS','ranks':ranks,'multipliers':multipliers,'classes':nh,
                      'integer_export_sha256':hashlib.sha256(raw).hexdigest(),
                      'wall_seconds':time.monotonic()-start}),flush=True)


if __name__=='__main__':main()
