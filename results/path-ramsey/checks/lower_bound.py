#!/usr/bin/env python3
"""The classical (P_10,P_10,P_10)-colouring of K_17 (blow-up of K_4): parts
A (5 vertices), B, C, D (4 each).  Colour 0: inside A u B and inside C u D;
colour 1: A-C and B-D; colour 2: A-D and B-C.  Each colour class splits
into components on at most 9 vertices, so none has a path on 10 vertices.
Writes lines "i j c"; check with check_colouring.py 17 10."""
part = [0] * 5 + [1] * 4 + [2] * 4 + [3] * 4          # A B C D
col = {frozenset((0, 1)): 0, frozenset((2, 3)): 0,
       frozenset((0, 2)): 1, frozenset((1, 3)): 1,
       frozenset((0, 3)): 2, frozenset((1, 2)): 2}
for i in range(17):
    for j in range(i + 1, 17):
        a, b = part[i], part[j]
        c = 0 if a == b else col[frozenset((a, b))]
        print(i, j, c)
