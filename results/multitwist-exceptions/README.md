# Fathi's consecutive-integers bound does not extend to multitwists

[![Checks](https://github.com/6/clank-lab/actions/workflows/multitwist-exceptions.yml/badge.svg)](https://github.com/6/clank-lab/actions/workflows/multitwist-exceptions.yml)

A [Dehn twist](https://en.wikipedia.org/wiki/Dehn_twist) $T_\gamma$ cuts a
surface along a simple closed curve $\gamma$ and reglues it after a full
turn; a multitwist composes twists about disjoint curves.
[Pseudo-Anosov](https://en.wikipedia.org/wiki/Pseudo-Anosov_map) maps are
the generic elements of the
[mapping class group](https://en.wikipedia.org/wiki/Mapping_class_group).
In 1987 Albert Fathi proved, for a closed surface, that if the orbit of
$\gamma$ under a mapping class $f$ fills the surface, then $T_\gamma^n f$ is
pseudo-Anosov except for at most 7 consecutive values of $n$. Fathi
presents his paper as generalizing a 1986 theorem of D. D. Long and H. R.
Morton, who had shown, for pseudo-Anosov $f$, that only finitely many $n$
are exceptions; Yohsuke Watanabe
([2016, §1.1](https://arxiv.org/abs/1611.05119)) describes Fathi's theorem
as making their result effective. Its hypothesis is only that the orbit of
$\gamma$ fills, so $f$ itself may be reducible; María Cumplido and Bert
Wiest ([2017, Theorem 3](https://arxiv.org/abs/1703.05044)) state it for
any mapping class.

Nikolai V. Ivanov asked, as
[Problem 5](https://arxiv.org/abs/math/0608325) of his 2006 list and of an
earlier problem list dated 1994–1998 on his website, whether
Fathi's theorem extends to a multitwist $t$: if the orbits under $f$ of all
the curves of $t$ together fill the surface $S$, must the integers $j$ with
$t^j \circ f$ not pseudo-Anosov lie among $N_S$ consecutive integers, for a
constant $N_S$ depending only on $S$? He noted that Fathi's theorem gives
$N_S = 7$ for a single twist, and separately called a weaker version, which
bounds only the number of exceptions, "still interesting".

We show that Fathi's consecutive-integers bound does not extend to
multitwists: in the orbit-filling form Ivanov states, with reducible base
maps, no constant $N_S$ exists for the sphere with five boundary
components, which answers Ivanov's Problem 5 negatively; the weaker count
version is untouched. For every $k \ge 1$ there are a mapping class $f_k$
and a two-component multitwist $t$ satisfying Ivanov's hypothesis such
that $t^0 f_k$ and $t^{-k} f_k$ each fix an essential curve, so neither is
pseudo-Anosov: two exceptional exponents arbitrarily far apart. The base
maps $f_k$ are themselves reducible, so it gives no counterexample with a
pseudo-Anosov base map, the setting of Long and Morton, and says nothing
about that version. The counterexample is on the five-holed sphere only;
we claim nothing about other surfaces, closed or with boundary.

In short: a counterexample for reducible base maps on the five-holed
sphere, not for pseudo-Anosov ones. The proof is a short written argument.
Lean checks its braid and free-group
algebra for every $k$, and two independent programs check the same curve
facts in two different models; the surface topology is the written proof.

Written proof, with Lean and computer checks; not yet reviewed by experts.

The proofs, the Lean formalization, the checking programs and the text were produced by AI models (from OpenAI and Anthropic), working under the author's direction.

[Read the paper](paper/paper.pdf) · [LaTeX source](paper/paper.tex)

Archived on Zenodo: [doi:10.5281/zenodo.23582026](https://doi.org/10.5281/zenodo.23582026)

## Check it

What Lean covers: the Lean proof works in the free group $F_4$, the
fundamental group of the five-holed sphere, with the half twists acting by
the Artin automorphisms. For every $k$ and both signs it proves the five
finite facts the written proof uses, as statements about these
automorphisms and conjugacy: each twist fixes its own curve; the pentagon
pattern of which curves meet; the two twists of $t$ commute; $t^0 f_k$ and
$t^{-k} f_k$ fix the curves $C'$ and $C$; and $f_k(a)$ meets $a$ and $c$.

What Lean does not cover: the surface topology. That the Artin
automorphisms are the twists' actions on the fundamental group, that curves
correspond to conjugacy classes up to inversion, that a twist fixes a curve
exactly when the two are disjoint, the exact intersection numbers, the
argument that the orbits fill the surface, and that a mapping class fixing
an essential curve is not pseudo-Anosov are all proved in writing in the
paper, from standard facts it cites.

Install [elan](https://github.com/leanprover/elan), then check the Lean
proof, which takes a few minutes once the Mathlib cache is downloaded:

```sh
cd lean
lake exe cache get
lake build
```

The build also checks each statement's exact type, a negative control (with
$C$ and $C'$ exchanged the statement is false) and the axioms used.
[Lean documentation](lean/README.md) lists the statements.

What the programs check: two independent Python programs, exact and with no
third-party packages, check the same five facts for $k = 1, \dots, 30$ and
both signs. Checker A (`checks/check_free_group.py`) uses the free-group
model, comparing curves by cyclic words up to inversion. Checker B
(`checks/check_dynnikov.py`) was written separately, without seeing checker
A or the Lean proof, and uses a different model: Dynnikov coordinates of
curves in the four-punctured disk, with exact intersection numbers. It also
checks the exact values $i(a, f_k(a)) = i(c, f_k(a)) = 4$ and runs with
every twist reversed. Both must reject four corrupted versions of the
curves. Like the Lean proof, the programs check the combinatorial core,
not the surface topology. With Python 3.10 or later, this runs in about a
second:

```sh
python3 checks/check.py
```

[Checker documentation](checks/README.md) describes both models and the
corruptions.

## Credits

Nikolai V. Ivanov posed the question, with the weaker count version, as
Problem 5 of
[Fifteen problems about the mapping class groups](https://arxiv.org/abs/math/0608325)
(2006) and of his earlier *Ten problems on the mapping class groups*,
headed "1994–1998, 2014" on his website. Albert Fathi's theorem
([Invent. Math. 1987](https://doi.org/10.1007/BF01389156)) is the
single-twist case the question extends, and D. D. Long and H. R. Morton's
finiteness theorem
([Topology 1986](https://doi.org/10.1016/0040-9383(86)90033-9)) preceded
it; S. Boyer, C. McA. Gordon and X. Zhang later improved Fathi's 7 to 6.
Yohsuke Watanabe restated the question in
[2016](https://arxiv.org/abs/1611.05119). Chaohui Zhang discussed the
multitwist extension, citing Ivanov's 1998 manuscript *Mapping class
groups*, in a
[2007 preprint](https://arxiv.org/abs/0708.0804v1), since withdrawn, which
claimed that no exceptions occur for a special class of pseudo-Anosov maps,
and proved related positive results for pseudo-Anosov maps in
[Kodai Math. J. 2011](https://doi.org/10.2996/kmj/1320935547). Mark Bell's
programs [flipper](https://github.com/MarkCBell/flipper) and
[curver](https://github.com/MarkCBell/curver) were used for preliminary
checks of the example; neither the proof nor the final checkers depend on
them. Checker B uses I. A. Dynnikov's
coordinates, with the update rules of Toby Hall and S. Öykü Yurttaş and
the intersection formula of Yurttaş and Hall. Lean, Mathlib and their
contributors supplied the formal-proof infrastructure.

Apache-2.0 (see the repository's LICENSE), except the third-party material listed in [THIRD_PARTY.md](THIRD_PARTY.md).

## Cite

```bibtex
@misc{GrahamMultitwistExceptions2026,
  author       = {Graham, P.},
  title        = {{Fathi's consecutive-integers bound does not extend to multitwists}},
  year         = {2026},
  howpublished = {\url{https://github.com/6/clank-lab/tree/multitwist-exceptions-v1/results/multitwist-exceptions}},
  doi          = {10.5281/zenodo.23582026}
}
```
