# Checks

Run from the folder above this one:

```sh
python3 checks/verify.py         # a few seconds
python3 checks/verify.py --n6    # adds the search on six vertices, about four minutes
```

`verify.py` compiles the C programs with `cc -O2`, runs every check below and prints `PASS` or the failures; its exit status is 0 only when every check passes. It needs Python 3.10 or later (standard library only) and a C compiler. It was run with Python 3.14 and GCC 15.2.

## The programs

- `check_a.py` (Python) reads a digraph file, or builds the family $F_{n-4}$, and tests conditions (i) and (ii) in their sorted-sequence form, condition (iii), strong connectivity by graph search in both directions, and Hamiltonicity by the Held–Karp dynamic program over vertex subsets.
- `check_b.c` (C) does the same with the counting form of the conditions (at most $i-1$ degrees are at most $i$; at least $i+1$ degrees are at least $n-i$), Warshall's transitive closure, and depth-first search over paths from vertex 0.
- `enum_a.c` and `enum_b.c` visit every labeled digraph on $n$ vertices, with no loops and at most one arc in each direction between two vertices: `enum_a` assigns each pair of vertices one of four states, and `enum_b` runs through bit words over the $n(n-1)$ ordered pairs. They use the same two methods as the checkers and print the number of digraphs, of digraphs satisfying (i) and (ii), and of counterexamples to each conjecture.

The four programs were written independently of each other and of the Lean proof. `verify.py` runs the checkers on `data/G6.txt`, `data/G7.txt` and the family ($8 \le n \le 18$ in `check_a`, $8 \le n \le 14$ in `check_b`, where depth-first search becomes slow), requires condition (iii) for `G7` and the family, and requires both checkers to reject four altered inputs: `G6` with the arc 2→3 added and `G7` with 0→2 added, which are Hamiltonian; `G6` without 4→3, which violates (ii); and `G6` with a loop. It then compares both enumerators' output with the expected lines:

```
n=3 digraphs=64 nw_hypothesis=7 nw_counterexamples=0 kot6_counterexamples=0
n=4 digraphs=4096 nw_hypothesis=186 nw_counterexamples=0 kot6_counterexamples=0
n=5 digraphs=1048576 nw_hypothesis=40140 nw_counterexamples=0 kot6_counterexamples=0
n=6 digraphs=1073741824 nw_hypothesis=44387496 nw_counterexamples=1080 kot6_counterexamples=0
```

`nw_counterexamples` counts strongly connected digraphs satisfying (i) and (ii) with no Hamilton cycle. `kot6_counterexamples` counts digraphs satisfying (i), (ii) and, for even $n$, (iii), with no Hamilton cycle. On six vertices `enum_a` takes about 2.5 minutes and `enum_b` about 1.5 minutes on one core, with under 10 MB of memory.

Digraph files list one vertex per line, `v: out-neighbors`, with `#` comments.

## Further credits

Nash-Williams' conjecture appears as Conjecture 1 of Kühn, Osthus and Treglown, *Hamiltonian degree sequences in digraphs* ([arXiv:0807.1827](https://arxiv.org/abs/0807.1827)), as Conjecture 6 of Kühn and Osthus, *A survey on Hamilton cycles in directed graphs* ([arXiv:1006.0590](https://arxiv.org/abs/1006.0590)), and as Conjecture 1 of Christofides, Keevash, Kühn and Osthus, *A semi-exact degree condition for Hamilton cycles in digraphs* ([arXiv:1002.3910](https://arxiv.org/abs/1002.3910)). The conjecture of Kühn, Osthus and Treglown refuted here is Conjecture 6 in the first arXiv version of their paper and Conjecture 8 in the second. The survey and the paper also record the question about cycles through pairs of vertices, citing Bermond and Thomassen's survey *Cycles in digraphs* (1981).

Gabriel C. Drummond-Cole compared the statement with Nash-Williams' 1975 chapter on MathOverflow. Louis DeBiasio's 2020 answer there related the 2013 example to a theorem of Amar and Manoussakis on bipartite digraphs (J. Combin. Theory Ser. B 50 (1990), [doi:10.1016/0095-8956(90)90081-A](https://doi.org/10.1016/0095-8956(90)90081-A); see Theorem 1.7 of Adamus, Adamus and Yeo, [doi:10.46298/dmtcs.1264](https://doi.org/10.46298/dmtcs.1264)), and his comments on question 369168 verified the 2020 examples. In MathOverflow question [369235](https://mathoverflow.net/questions/369235) Guninski proposed an infinite family of symmetric digraphs and withdrew it as the result of a program bug; DeBiasio noted that symmetric digraphs cannot be counterexamples.

Nearby work: Samvel Kh. Darbinyan, *On three conjectures of Thomassen and the extremal digraphs for two conjectures of Nash-Williams*, J. Graph Theory 109 (2025), 412–425 ([doi:10.1002/jgt.23233](https://doi.org/10.1002/jgt.23233)), constructs, in the words of its abstract, “infinitely many k-strong, where k ≥ 2, digraphs which show that two famous conjectures of Nash-Williams and a conjecture of Kühn et al. for Hamiltonicity of digraphs are best possible in the sense that they become false if exactly one of the degree conditions is not valid”. Digraphs that violate a condition are not counterexamples. The full text is behind the publisher's paywall, and only its abstract and reference list could be consulted. Louis DeBiasio, *Inheritance of expansion and oriented Hamilton cycles in robust expanders: a regularity-free proof* ([arXiv:2610.09072](https://arxiv.org/abs/2610.09072), October 2026), concerns robust expanders and does not address the degree-sequence conjectures.
