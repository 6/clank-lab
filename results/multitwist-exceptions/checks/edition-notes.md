# Background and checking notes

October 25, 2026. These documentary notes retain the source qualifications
and contextual statements of the previous edition. The mathematics and
checking artifacts are unchanged.

Bibliographic keys below refer to [the paper's reference list](../paper/paper.pdf).

## Prior-work details

Let $`S`$ be a compact orientable surface, possibly with boundary, and let
$`\mathrm{Mod}_S=\pi_0(\mathrm{Diff}(S))`$ be its mapping class group. A mapping
class is *pseudo-Anosov* if it is neither periodic nor reducible
(it fixes no finite set of disjoint essential curves); see  [FM,FLP].
Many pseudo-Anosov classes come from Dehn twists. Long and
Morton  [LM] and then Fathi  [Fathi] studied the sequence
$`T_\gamma^j f`$, $`j\in\mathbb{Z}`$, where $`T_\gamma`$ is the Dehn twist about a curve
$`\gamma`$. Fathi proved, for a closed surface $`M`$:


*Theorem 0.1 of  [Fathi].* Let $`f`$ be in $`\pi_0(\mathrm{Diff}(M))`$ and let $`\gamma`$ be in $`\mathcal{S}(M)`$. If the orbit of $`\gamma`$ under $`f`$ fills $`M`$, then $`T_\gamma^n f`$ is a pseudo-Anosov class except for at most 7 consecutive values of $`n`$.


 Here $`\mathcal{S}(M)`$ is the set of isotopy classes of simple closed
curves. Long and Morton's Theorem A  [LM] gives, for a
pseudo-Anosov $`f`$ and one twist about an essential curve, finitely many
exceptional exponents and eventual pairwise nonconjugacy separately in
the two tails. Their Section 1 works with closed orientable surfaces;
on p. 9 of the author-accepted scan they leave the bounded-surface
versions of results 1.2 and 1.4 unproved, while saying that this presents
no difficulty. We use neither a bounded-surface extension of their theorem
nor a multitwist version of it. Fathi's summary says: we generalize a
theorem of Long and Morton to obtain that if $`f`$ is a pseudo-Anosov
diffeomorphism of an oriented surface and $`T_\gamma`$ is the Dehn twist
around the simple closed curve $`\gamma`$, then the isotopy class of
$`T_\gamma^nf`$ contains a pseudo-Anosov diffeomorphism except for at most 7
consecutive values of $`n`$  [Fathi], and Watanabe writes that Fathi
effectivised the above result of Long–Morton  [Watanabe , §1.1].
Theorem 0.1 itself assumes only that the $`f`$-orbit of $`\gamma`$ fills, so $`f`$
may be reducible; Cumplido and Wiest state it in this form, for any mapping
class  [CW , Theorem 3]. Boyer, Gordon and Zhang later improved the constant $`7`$ to
$`6`$  [BGZ], as recorded by Watanabe  [Watanabe , §1.1].
The BGZ abstract states this refinement for a pseudo-Anosov base.

Ivanov asked whether Fathi's theorem extends to multitwists, with a
constant depending only on the surface  [Ivanov94,Ivanov06]. Let $`t`$ be
a Dehn multitwist $`T_{\alpha_1}^{\pm1}\cdots T_{\alpha_n}^{\pm1}`$ about disjoint
curves $`\alpha_1,\dots,\alpha_n`$, and suppose that the curves $`f^m(\alpha_i)`$,
$`1\le i\le n`$, $`m\in\mathbb{Z}`$, together fill $`S`$, that is, every essential curve
has nonzero geometric intersection number with one of them. His *consecutive-integers*
question asks whether the $`j`$ with $`t^j\circ f`$ not pseudo-Anosov always lie
among $`N_S`$ consecutive integers, for a constant $`N_S`$ depending only on
$`S`$; for a single twist on a closed surface this is Fathi's theorem with
$`N_S=7`$. His weaker *count* question asks only that at most $`N_S`$ of
the $`t^j\circ f`$ fail to be pseudo-Anosov. Both were posed as Problem 5
of his 2006 list and of an earlier list  [Ivanov94], for compact
orientable surfaces possibly with boundary; the full question is quoted below. We answer the first question, for one surface,
and say nothing about the second. All curves below are essential in the
usual sense (the paper, Conventions and standard facts).

### Ivanov's question in full

Ivanov's list concerns a compact orientable surface, possibly with
boundary, with $`\mathrm{Mod}_S=\pi_0(\mathrm{Diff}(S))`$ including
orientation-reversing classes  [Ivanov06 , p. 1]. We quote Problem 5
exactly, from the arXiv version  [Ivanov06 , pp. 4–5] (version 1,
posted August 14, 2006, the only version). He writes $`t_\alpha`$ for the
left Dehn twist along $`\alpha`$.


> *5. Dehn multitwists.* For a nontrivial circle $`\alpha`$ on $`S`$ (i.e. a submanifold $`\alpha`$ of $`S`$ diffeomorphic to the standard circle $`S^1`$) let us denote by $`t_\alpha`$ the (left) Dehn twist along $`\alpha`$; $`t_\alpha\in\mathrm{Mod}_S`$. A Dehn multi-twist is any composition of the form $`t_{\alpha_1}^{\pm1}\circ t_{\alpha_2}^{\pm1}\circ\cdots\circ t_{\alpha_n}^{\pm1}`$ for disjoint circles $`\alpha_1,\alpha_2,\ldots,\alpha_n`$.
>
> *Question.* Is there a constant $`N_S`$, depending only on $`S`$, such that the following holds? Let $`f\in\mathrm{Mod}_S`$ and let $`t=t_{\alpha_1}^{\pm1}\circ t_{\alpha_2}^{\pm1}\circ\cdots\circ t_{\alpha_n}^{\pm1}`$ be a Dehn multi-twist. If $`A=\{f^m(\alpha_i):1\le i\le n,\ m\in\mathbb{Z}\}`$ fills $`S`$ (i.e. for any nontrivial circle $`\gamma`$ there exists an $`\alpha\in A`$ such that the geometric intersection number $`i(\gamma,\alpha)\ne0`$), then only a finite number of elements of the form $`t^j\circ f`$, $`j\in\mathbb{Z}`$, are not pseudo-Anosov, and the corresponding $`j`$ are among some $`N_S`$ consecutive integers.
>
> By a theorem of A. Fathi [Fath], if $`t`$ is a Dehn twist, then this is true for $`N_S=7`$. This theorem of A. Fathi was preceded by a theorem of D. Long and H. Morton [LM] to the effect that for a Dehn twist $`t`$, only a finite number of element $`t^j\circ f`$ are not pseudo-Anosov under the above assumptions, without a uniform bound on the number of exceptions.
>
> A weaker version of this question is still interesting: under the same conditions, is it true that no more than $`N_S`$ of $`t^j\circ f`$ are not pseudo-Anosov?

 Long and Morton's theorem, as noted above, assumes that $`f`$ is
pseudo-Anosov, which is stronger than the filling hypothesis in Ivanov's
summary of it. Ivanov goes on to call Fathi's paper one of the deepest and the
most underappreciated works in the theory of the mapping class groups and
adds: The above question may be considered as a test of our
understanding of Fathi's ideas  [Ivanov06 , p. 5]. The question already
appears, in essentially the same words, as Problem 5 of his earlier
list  [Ivanov94], which also states the weaker version. That list is
headed 1994–1998, 2014; Ivanov writes there that its original version
was written in early 1994 and that updates were added until 1998, marked
as such, and Problem 5 carries no update, but we have not seen the 1994
original. Watanabe
restated it in 2016, describing it as a Long's and Penner's like extension on
Fathi's theorem  [Watanabe , §1.1]. Zhang discussed whether the twist can be replaced by a multitwist at a
cost of replacing the number 7 by an undetermined but universal number,
citing Ivanov's manuscript *Mapping class groups* of December 21,
1998, in a preprint first posted August 6, 2007  [Zhang07].
For a special class of pseudo-Anosov maps (those that become trivial when a
chosen puncture is filled in) and multitwists satisfying a
non-compressibility condition, it claimed that every composition is
pseudo-Anosov, so that no exceptions occur; the author withdrew the
preprint in January 2008. In a later paper  [Zhang11], Zhang showed
that for any Dehn twist $`t_c`$ on a punctured surface there are
pseudo-Anosov maps $`f_m`$ with $`f_m\circ t_c^k`$ pseudo-Anosov for all $`k`$
once $`m`$ is large, and deduced a corollary for multitwists on two curves.
Both works concern pseudo-Anosov base maps and give positive results; our
example is of a different kind. So there are two questions: the
*consecutive-integers* question, which asks for Fathi's conclusion
with $`N_S`$ in place of $`7`$, and the weaker *count* question. We answer
the first, for one surface, and say nothing about the second.

### What is new, and the key verification. The mechanism is
simple. Since $`T_a`$ and $`T_c`$ commute,
$`t^jf_k=T_a^{k+j}T_c^{\varepsilon j}T_d`$, and the two components of $`t`$
have exponents that vanish at different values of $`j`$: at $`j=-k`$ the twist
about $`a`$ disappears and at $`j=0`$ the twist about $`c`$ does. Each vanishing
leaves a product of twists about two curves of the pentagon of
Figure (paper label fig:curves), and such a product fixes the curve of the pentagon
disjoint from both. The key verification is the hypothesis: Ivanov's
filling condition is on the union of the orbits of all components of $`t`$,
and we must check that $`a`$, $`c`$ and $`f_k(a)`$ already fill. This is
consistent with Fathi's theorem for several curves  [Fathi , Theorem
0.2]: for curves whose $`f`$-orbits are distinct and fill a closed
surface, it gives a pseudo-Anosov class once *every* exponent has
absolute value at least some $`n`$, and it gives no window in which the
exceptions must lie. We
know of no earlier written account of this example or of an answer to the
consecutive-integers question; given how short it is, a specialist may well
have known it informally.

### Pseudo-Anosov bases and limits.
Theorem (paper label thm:pa) below strengthens the example by replacing the
reducible base $`f_k`$ with a pseudo-Anosov base $`g_k`$, retaining a fixed
positive multitwist and two exceptions distance $`k`$ apart. Penner's
construction  [Penner] supplies the new base assertion; the same pants
argument verifies Ivanov's union-filling hypothesis directly. This concerns
a multitwist on this bordered surface. It contradicts no single-twist
conclusion of Long and Morton. The count question is untouched: we make
no claim about the number or finiteness of exceptions for a fixed base.
Closed surfaces and other surfaces with boundary are also outside the
claim. The proof uses filling of the union; no assertion about individual
component orbits is needed.

## Reproduction and axioms

The recorded command `python3 checks/check.py` runs both checkers and all
corruptions in about a second. This edition does not repeat that computation.
The Lean axiom audits use only `propext`, `Classical.choice` and `Quot.sound`;
the integer group identity uses `propext` and `Quot.sound`. The original
formal statements, exact-type audits and false variants remain in `lean/`.
See [the reproduction instructions](../README.md#check-it) and
[the Lean documentation](../`lean/`README.md).

## Detailed algebraic and finite checks

### The model. The fundamental group of $`S`$ (the disk with four
punctures) is free on loops $`x_1,\dots,x_4`$ around $`p_1,\dots,p_4`$, with
$`x_1x_2x_3x_4`$ parallel to $`\partial D`$. Choosing a basepoint and representatives gives the Artin
automorphisms for half twists

$$

\sigma_i:\ x_i\mapsto x_ix_{i+1}x_i^{-1},\quad x_{i+1}\mapsto x_i,\quad
x_m\mapsto x_m\ (m\ne i,i+1),

$$

and the twists about the round curves are the full twists of the enclosed
strands  [FM, Ch. 9]: $`T_a=\sigma_1^2`$, $`T_d=\sigma_2^2`$, $`T_c=\sigma_3^2`$,
$`T_{C'}=(\sigma_1\sigma_2)^3`$, $`T_C=(\sigma_2\sigma_3)^3`$, up to one global
choice of handedness. The canonical fundamental-group action is only defined up to inner
automorphism; this ambiguity disappears on conjugacy classes. The five
curves are represented, up to conjugacy and inversion, by the words $`x_1x_2`$, $`x_2x_3`$, $`x_3x_4`$, $`x_1x_2x_3`$, $`x_2x_3x_4`$. In this
model the theorem rests on five finite facts:

- **F0.** Each of $`T_a,T_d,T_c,T_{C'},T_C`$ fixes its own curve.
- **F1.** The pentagon pattern of the pentagon-pattern lemma: $`T_u(v)=v`$ for
  the ten ordered disjoint pairs and $`T_u(v)\ne v`$ for the ten ordered
  meeting pairs.
- **F2.** $`T_aT_c=T_cT_a`$.
- **F3.** For every $`k`$ and both signs, $`T_a^kT_d`$ fixes $`C'`$ and
  $`t^{-k}f_k=T_c^{-\varepsilon k}T_d`$ fixes $`C`$.
- **F4.** For every $`k`$, $`T_a(f_k(a))\ne f_k(a)`$ and $`T_c(f_k(a))\ne f_k(a)`$,
  that is, $`f_k(a)`$ meets $`a`$ and $`c`$.


### Lean. The file `lean/Multitwist.lean` (Lean 4 with Mathlib)
proves F0–F4 for every $`k\in\mathbb{N}`$ and both signs, as statements about
the Artin automorphisms of the free group $`F_4`$ and conjugacy in it. For
disjoint pairs it gives explicit conjugators. For meeting pairs it gives a
homomorphism $`F_4\to\mathrm{Sym}(3)`$ that sends exactly one of $`T_u(v)`$ and
$`v`$ to the identity, so $`T_u(v)`$ is conjugate neither to $`v`$ nor to
$`v^{-1}`$. For every $`k`$, F3 follows by commuting and canceling twists (F2), and F4
by applying the automorphism $`T_a^k`$, which preserves conjugacy, to the case
$`k=0`$. The file
`lean/Check.lean` restates each fact with its exact type, checks that
exchanging $`C`$ and $`C'`$ makes the $`j=0`$ statement false, and checks which
axioms each statement uses: only the standard `propext`,
`Classical.choice` and `Quot.sound`.

What Lean does *not* check is the surface topology, which is the
written proof above: that the Artin automorphisms are the maps the twists
induce on $`\pi_1`$; that essential simple-curve classes inject into conjugacy classes up
to inversion, so that $`T_u(v)=v`$ in the model means that the curves are
equal; that $`T_u(v)=v`$ if and only if $`i(u,v)=0`$; the exact values
$`i=2`$ and $`i=4`$; the pants argument for filling; and that a class fixing an
essential curve is not pseudo-Anosov. This development does not formalize mapping class groups or isotopy
classes of curves, so these steps remain written arguments.

### New algebra and topology certificates.
The additional file `lean/V2.lean` proves the generic integer group
identity under commutation, the concrete fixed-word identities for every
$`k\in\mathbb N`$, and both nonconjugacy counterparts for $`g_k(a)`$.
`lean/V2Check.lean` checks their exact types, concrete false variants,
and the axioms used. No Lean theorem asserts filling or pseudo-Anosovness.
Penner's theorem and its application, the diagram-to-surface
identification, the intersection formulas, pants classification and
Nielsen–Thurston implications remain the written bridge.

The programs in `checks/extension/` transport the two independent
exact models to the new endpoints, testing $`k=1,\dots,12`$ in the free-group
model and $`k=1,\dots,8`$ in Dynnikov coordinates, with both global twist
directions. Negative tests change order, exponents or curves. These are
finite controls; the all-$`k`$ algebra is the Lean proof and the all-$`k`$
surface argument is the written proof. Two further exact implementations
check the rational embedding: one constructs a grid of cells and the other
reconstructs split edges, rotations and directed facial walks. They check
the complete facial certificate, the pants decomposition and the five
curves, including $`C'=[-2,11]\times[-6,6]`$ and
$`C=[3,16]\times[-8,8]`$. Both reject the same planted geometry
corruptions; the second also detects a removed crossing occurrence.
These computations certify finite diagram data, not Penner's theorem or
a fully formalized surface theory.

### Checker A. The program `checks/check_free_group.py` works in
the same free-group model: it computes the Artin action on reduced words
and compares curves by a canonical form of their cyclic words up to
inversion. It verifies F0–F4 for $`k=1,\dots,30`$ and both signs, $`327`$
checks in all. It is exact and uses only the Python standard library.

### Checker B. The program `checks/check_dynnikov.py` was
written separately, from the statement of the facts alone and without
seeing checker A or the Lean file. It uses a different model: curves in the
four-punctured disk are encoded by their Dynnikov coordinates  [Dynnikov]
in $`\mathbb{Z}^4`$, a bijective encoding of multicurves, and the half twists act by
the piecewise-linear update rules of Hall and Yurttaş  [HY].
Intersection numbers with round curves are computed exactly by the formula
of Yurttaş and Hall  [YH, Lemma 9] and, independently, by the twist test
$`i(u,v)=0\iff T_u(v)=v`$. Before checking F0–F4 it validates the model on
known facts: inverses, the braid relations, triviality of the full twist,
and the identity (I1) on random curves. It verifies F0–F4 for
$`k=1,\dots,30`$ and both signs, also with every twist reversed, and confirms
the exact values $`i(a,f_k(a))=i(c,f_k(a))=4`$. It is exact (integers only)
and uses only the Python standard library.

### Corruptions. Both checkers must reject four corrupted inputs:
$`C`$ replaced by $`T_a(C)`$; $`C'`$ replaced by $`T_c(C')`$; $`C`$ and $`C'`$
exchanged; and $`c`$ replaced by $`T_{C'}^{-1}(c)`$. Each corruption breaks the
pentagon pattern and the fixed-curve facts, and both checkers reject all
four. The command `python3 checks/check.py` runs both checkers and
all corruptions in about a second.

The two programs implement one list of facts in two models, so they guard
against errors of computation, not against an error in the topology above;
like the Lean proof, they check the combinatorial core, while the step from
it to the theorem is the written proof.

The precise efficiency, essentiality, nonparallelism
and filling hypotheses have all been checked.

No inference from
pseudo-Anosov dynamics or individual-orbit filling is needed.

This is a separation statement; it neither counts nor
classifies the full exceptional set.

## Preliminary checks

Before the checkers of the computational-verification section were
written, `flipper` was used to check the two exceptional members for
$k\le5$ and both signs, on two different triangulations, and `curver`
to cross-check the curve facts F0–F4 computed by the Dynnikov-coordinate checker.

The computational-verification section describes two independent exact
checks of the pattern, in the form $`i(u,v)=0\iff T_u(v)=v`$ (which follows
from (D) and (I1)).

These checks
are not part of the argument: neither the proof nor the final checkers,
which use only the Python standard library, depend on them.
