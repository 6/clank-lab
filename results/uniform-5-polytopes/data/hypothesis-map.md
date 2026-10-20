# External hypothesis evidence map

This table maps the twelve declarations printed in the paper's Appendix A
([verbatim source](core-hypotheses.txt)) to the written argument and the
executable evidence. Section numbers refer to the accompanying paper;
paragraphs are identified by their opening words, named result or numbered
step. Commands C1–C11 are given below, with their expected outputs. All paths
are relative to the bundle root unless a command changes directory.

The table specifies expected results. The [completed v2 replay receipt](replay-v2-referee.json)
records four independent standalone full shares and seven post-review checks
on retained fresh outputs, all passing. The search kernels are unchanged
between those phases; the receipt identifies the changed acceptance checks.
It does not claim a single end-to-end run of the final wrapper. The earlier
[October 20 receipt](replay-v2.json) remains as a historical execution record.

Version 2 corrects an evidence omission in version 1: programs named in
the proof route and the source of the Lean report were absent from the
bundle. They are now shipped under `checks/primary/` and `data/`, with
explicit replay commands. C10 regenerates the entire 629-row Lean file
and compares every logical row with fresh independent stage-3 output.
This closes the executable table correspondence, not the remaining
external interpretation of exact geometry as Lean data.

“External” means a written argument together with certified computation,
not a Lean instance. None of these twelve hypotheses is discharged for a
common concrete numerical instance inside Lean. A successful build proves
the implication from them, not their truth or joint satisfiability. The two
cited lower-dimensional classifications are additional external premises;
no executable enumeration here re-proves them.

| Hypothesis | Written argument: section and paragraph | Executable command and expected output | Scope and remaining limitation |
|---|---|---|---|
| LIB | §3.2, LIB and LINK, paragraphs “What is computed” and “What is checked”; “A word determines its angle” proof; §3.3 construction paragraphs. | C1: `library_verify.py`, `library.py`, `parabolic.py`, `exceptional.py`; 181 types, 558 words, 1,277 polygon occurrences, containment and corruption checks pass. Exceptional models also run in C7. | External model/geometry correspondence. Construction proofs and cited 4-D classification remain premises; matching inventory counts alone is insufficient. |
| S1 | §4.1, S1 and “What is computed”, then “Proof route”; exact exclusions in §3.2, “Exact inputs of the exclusions”. | C1: `stage1.py`, `verify_stage1.py`, `compare.py`; 14,965 cycles, 7,080 flat, 57 degenerate, 537 rootless, 7,291 retained roots; full canonical-word comparison and corruptions pass. | Coverage on the extended domain, not a bound of 10^-20 on merged intervals. The stopping tolerance applies to leaves only. |
| S2 | §4.2, S2, paragraph “Why such a search is exhaustive”, and “Exact equivalence of placements” proof. | C2: `stage2.py`, `run.py`, `check_equivalence.py`; 563 complete classes, 629 signatures; 181 models and 5,108 ordered equivalences checked. Class 25 alone has no signature. | Coverage of all actual figures at every radius in each class; retained encodings need not be realizable. Uncertain predicates must remain OPEN. |
| ROOT | §4.4.1, ROOT and paragraph “Proof route”; §4.5.3, step 2. | C2: `s3_cycles.py`, `s3_radius.py`; Whole-class UNIQUE witnesses cover all 629 signatures, including the refuted signature. C6 tests wide intervals and corrupt closure constants. | Endpoint signs, derivative exclusion and continuity supply uniqueness. The final JSON audit checks coverage, not the derivative proof by itself. |
| DEV | §4.4.3, opening paragraph, DEV and “What is checked”; §4.5.3, step 5. | C2: `s3_develop.py`; extra radius-one signature REFUTED, zero OPEN; C6 recovers a known radius-one control and refutes the extra star, with uncertainty controls OPEN. | Refutes a full actual incident-facet star with the same root and center, conditional on the written geometry-to-encoding correspondence. C9 replays the primary encoding and C10 binds the same extra candidate to Lean row 12 by full cycle-word signature; the exact-star interpretation remains the external U3Realizations obligation. Neither existence of the extra encoding nor exclusion based on an unlabeled figure alone is asserted. |
| B2 | §5.2, cycle-types proof; §5.3, three type-radius derivations; §5.4, “Reduction to a finite check”, “Proof route”, “Second implementation”, “Input identity”. | C1: `b2.py`, `verify_b2.sh`; 496,824 / 150,495 / 1,905 radii of types i/ii/iii, zero coincidences or undecided cases. `check_result.py`: 649,224 total, cutoff 398, disagreements 0. | Covers all integer n ≥ 17 using the written tail bound r_398 > max Ω and all polynomial roots in (-1,1). A finite loop without that reduction is insufficient. |
| P1 | §5.3, Type-(i) radius and closed-forms proofs; §5.6.1, P1 and paragraph “Hence the 67 configurations”. | C3: `p1check.py`; 168 configurations, 137 closable, 28 nonclosable, 3 degenerate, 83 family, 67 excluded, 16 survivors. C4: `p1_literal_contract.py`; all 67 literal rational-range separations > 1/2000. | C4 closes an evidence omission: the earlier program could use tighter discrete/tail bounds instead of the literal wider intervals in P1Separated. Universal delta ranges use the written monotonicity proof, not samples of n. |
| W | §5.6.2, W; paragraphs “Scope of the two implementations”, “Parameter domains”, “Finite geometric realizations and the chart”, “What is computed”, “Completeness of computed results”; W-use proof. | C3: `fans.py`, `wcheck.py`, `w_bound.py` installed as `bnb.py`, `summary.py`; 127 full-domain fans, 120 certified, seven expected full-domain failures with seven certified n=m repairs. C5: `chartcheck.py`, four chart families and four rejected corruptions. | Finite geometric realizations only. New explicit chart paragraph supplies the coordinate-independent correspondence. Bounded partner parameters are 36 integer slices, not a real interval; seven exceptional fans are restricted to n=m. |
| PartnerRadiusFilter | §5.6.2, “The seven exceptional fans”, Partner-radius filter lemma and proof beginning “From F”. | C3: `summary.py` calls `partner.allowed`; all seven exceptional slices have exactly the matching singleton partner, and the full summary is ACCEPTED. | Both type-II exclusion and equality forcing use the radius equation, interval separation and written infinite-tail bounds. Running `partner.py` alone produces no audit. |
| U3Realizations | §4.5.3, Rooted determinism proof and step 1 “Realization coverage”; §4.5.4, “Stages 2 and 3”. | C2 + C9 + C10 + C11: `stage3.py`, primary `search.py` and `canon.py`, and `report_bridge.py`; 629 signatures and 657 independent realization groups, including 28 additional mirror placements excluded by separation; no OPEN. | C9 regenerates the primary signatures and raw encoding report; C10 checks its class/signature row correspondence with C2. Geometry-to-encoding completeness and fixed-radius rigidity remain written arguments, not concrete Lean instances. |
| U3Identification | §3.3, construction paragraphs; §4.5.3, step 3 “Identification by elimination”, and “stage 3, proof route” proposition proof. | C2 + C9 + C10: `s3_identify.py`, `models.py`, primary `identify.py` and the report bridge; 628 known signatures, 890 matched construction names, one wholly refuted signature, no OPEN. C6 rejects incomplete coverage. | Exact neighbor counts or exhaustive strict frame exclusions justify NO. POSSIBLE/MATCH interval overlap is not equality; existence of known constructions plus exhaustive elimination supplies identification. C10 checks all 890 MATCH, 230 NO-COUNT and 32 NO row/name pairs. Their exact-geometric soundness remains the written argument. |
| U3Forcing | §4.5.3, step 4 “Local uniqueness”, with Rooted determinism; independently §4.4.2, Coset comparison proof. | C2 + C9 + C10: `s3_stars.py` and primary `locuniq.py`; surviving known realizations have FORCED local uniqueness. C6 tests complete matching, symmetry and uncertainty controls. | The primary anchored-code route and independent coset route both run. C10 compares their FORCED flags for all 629 primary-corresponding rows, including the extra candidate; the 28 additional mirror placements are separate exclusions. Exact universal geometric meaning is supplied externally, not by the flags alone. |

The following four rows spell out the remaining classification burdens;
they are not four additional Lean assumptions.

| Burden | Written argument: section and paragraph | Executable command and expected output | Limit |
|---|---|---|---|
| Exhaustiveness of local enumeration | §3.1 Library completeness; §4.1 complete closed walks and angle bound; §4.2 exhaustive opposite-hinge search; §4.5.3 step 1 and rooted rigidity. | C1 + C8 + C2 + C9 + C10 + C11, including equivalence/orientation coverage: 14,965 cycles → 563 classes → 629 signatures, no OPEN. | Enumerating known constructions alone would not prove completeness. Classification inputs, pruning soundness and geometry-to-encoding proofs remain external. |
| Identification and exclusion of retained signatures | §4.5.3 steps 2–4 and proposition proof; §4.6 proof of Case A. | C2: 628 known signatures, 890 names; 28 extra mirror realizations excluded by separation; all surviving known continuations forced. | Do not identify interval overlap with exact congruence or confuse 890 construction names with 628 objects. C9 and C10 now connect both executable routes to the Lean table; exact geometric soundness remains external. |
| Extra candidate | §4.4.3 DEV and “What is checked”; §4.5.3 step 5. | C2 + C6: the radius-one, eight-vertex figure's actual-star continuations all die; limits and uncertain identities remain OPEN. | C2 is required for full P16 coverage, beyond the small radius-one control. C10 checks the full signature and binds the extra candidate to Lean row 12; C9 replays its primary development. |
| At least 17 sides; unbounded parameters | §5.4 B2 corollary; §5.5 exactly-one-large-face product proof; §5.6.3 reduction to two paired faces; §5.6.4 paired theorem; §5.7 proof of Case B. | C1 + C3 + C4 + C5; optional Lean build checks their conditional geometric composition. | All-parameter coverage comes from the tail inequalities, finite charts, integer exceptions and structural product proof. Neither P=16 enumeration nor sampled large parameters supplies it. |

## Commands and expected output

Install `checks/requirements.txt`. Let `PY` be the absolute path to that
Python interpreter and `OUT` a fresh absolute output directory. Shell
commands below start at the bundle root. These are replay instructions;
the table does not assert that mere inspection of a saved report is a fresh run.

C1 — independent library, stage one, B2 and corruptions:

```sh
PYTHON="$PY" bash checks/independent-s1-b2/verify.sh
```

Expected: CERTIFIED library and complete stage-one receipts with the counts
in the table; B2 has zero coincidences and undecided cases, then
`status=CERTIFIED, total_radii=649224, cutoff=398, disagreements=0`.
The final count/cutoff check alone does not replay all B2 radii.

C2 — complete P16 signatures, exact equivalences, realizations and coverage:

```sh
mkdir -p "$OUT"
(cd checks/independent-s23
 "$PY" unpack_inputs.py "$OUT/input" --pmax 16
 "$PY" run.py "$OUT/input/u2_classes_p16.json" "$OUT/s2.jsonl" --states
 "$PY" check_equivalence.py "$OUT/input/u2_classes_p16.json" certificates/equivalences-p16.json
 "$PY" stage3.py --states "$OUT/s2.jsonl" --models models \
   --known "$OUT/input/u3_known_p16.json" --output "$OUT/s3.jsonl" --jobs 2
 "$PY" audit_stage3.py --classes "$OUT/input/u2_classes_p16.json" \
   --states "$OUT/s2.jsonl" --results "$OUT/s3.jsonl" --models models \
   --known "$OUT/input/u3_known_p16.json" --pmax 16 \
   --receipt "$OUT/s3.jsonl.frozen.json")
"$PY" checks/count_convention.py "$OUT/s3.jsonl" \
  --known "$OUT/input/u3_known_p16.json" --classes "$OUT/input/u2_classes_p16.json"
"$PY" checks/test_v2_outcomes.py "$OUT/s3.jsonl"
```

Require every command to exit zero. The final S3 audit prints `status=PASS`, `classes=563`, `signatures=629`, `realisations=657`,
`historical_comparison=false`.
Of those groups, 628 are known, 28 mirror alternatives are excluded by
strict full-star separation, and the additional candidate is refuted by
development. The raw schema uses REFUTED for both kinds of exclusion;
their geometric reasons are different. The count check prints
`PASS finite convention: 19 + 31 + 8 + 47 - 1 = 104; sole finite-list overlap is the 5-cube`.
It is bookkeeping on the audited equivalence classes, not another congruence proof.
It also prints `PASS ROOT coverage: all 629 signatures have a whole-class UNIQUE witness`.

C3 — full W, P1, partner filter and corruption controls:

```sh
# The W checker uses this import name in a disposable copy.
mkdir -p "$OUT/caseb"
cp -R checks/check_caseb "$OUT/caseb/check_caseb"
cp checks/w_bound.py "$OUT/caseb/check_caseb/bnb.py"
PYTHON="$PY" bash "$OUT/caseb/check_caseb/run.sh" full
```

Expected: P1 counts as above, all required W rows covered, exactly seven
expected full-domain failures repaired at n=m; summary `ACCEPTED` and
final `ALL OK`. Expected failure witnesses must not be silently changed
into unrestricted successes. Quick mode samples W and is not proof coverage.

C4 — the literal P1 hypothesis (added to both wrapper modes):

```sh
"$PY" checks/p1_literal_contract.py
```

Expected: `PASS literal P1Separated: 67 configurations, 36 bounded tails; every selected separation > 1/2000`.

C5 — independent free-box chart bound and corruptions:

```sh
"$PY" checks/check_caseb/chartcheck.py checks/repair-caseb-w/chart-certificate.json
```

Expected: four certified families (333, 36, 44, ii), `corruptions_rejected=4`.
This does not replace full W.

C6 — small positive/negative controls, not the complete P16 replay:

```sh
(cd checks/independent-s23
 "$PY" test_r1_stage3.py
 "$PY" test_stage3.py)
```

Expected: radius-one known/refuted control PASS with uncertainty OPEN;
`PASS complete matching vs brute force: 74963`; simplex root,
identification, local uniqueness and corruption controls PASS.

C7 — all public computational obligations together (C1–C6 and C8–C11):

```sh
PYTHON="$PY" bash checks/verify-public.sh full
```

Expected final line: `uniform-5-polytopes public full: PASS`. This runs
C1–C6 and C8–C11, including exact outcomes and both report bridges on freshly generated P16 output. It does not
execute Lean or automatically verify the prose. For the conditional Lean
composition, run `lake exe cache get`, `lake build`, then
`lake env lean Audit.lean` from `lean/`; the audit allows only `propext`,
`Classical.choice` and `Quot.sound`, and still assumes the twelve inputs.

C8 — class and interval bridge (also included in C7):

```sh
mkdir -p "$OUT/filter"
cp -R checks data "$OUT/filter/"
"$PY" "$OUT/filter/checks/check_filter.py"
```

Run C1 before C8, then C2. C1's `verify_stage1.py/equal_file` compares the
complete freshly regenerated parsed cycle records with
`checks/independent-s1-b2/evidence/cycles.json.gz`. C8 reads exactly that
authenticated file. Thus fresh equality followed by recomputation connects
the two commands without passing an ephemeral output path. C2 alone is
not full acceptance; all C7 parts must pass.
C8 recomputes the closure filter from those authenticated records, checks
all deletion certificates, and compares the full surviving cycle sets to
the packed C2 inputs. It now also checks, with exact rational endpoints,
that each C2 interval contains the regenerated surviving S1 root intervals.
Expected: PASS; 4,224 initial P16 classes, 563 survivors; interval coverage
counts P6/P10/P16 = 136/278/563; three semantic filter corruptions rejected
by both checks, narrowed consumer intervals rejected, and pairwise disjoint consumer class hulls checked at all three cutoffs. Thus C2 does use
shared packed inputs, but their entire class inventory and radius coverage
are checked rather than trusted as an unexplained 563-row list.

C9 — primary proof-route replay (four independent parts):

```sh
"$PY" checks/replay_primary.py --part all --jobs 2 --out "$OUT/primary"
```

The parts `library`, `s23`, `caseb`, and `wedge` may instead run separately
with distinct output directories. Expected: 181 models, 14,965 cycles and
563 surviving classes; 629 primary encodings (633 search states), 628
KNOWN, one REFUTED, 890 names, every ROOT and forcing check passed;
primary B2/P1 and seven partner repairs; 228 primary W rows with 184
certified, 31 nonclosable, three degenerate and ten explicitly expected
unrestricted failures. Seven exceptional admissible slices are repaired
at n=m; the other three failure rows are supplementary fans (3,11,13),
(4,7,9), and (5,6,7), separately excluded by P1.
No unrestricted failed fan is accepted as certified. See
`checks/primary/` for the named `check_u2`, `check_u3`, `cert_stage1_5d.py`,
`b2check.py`, and `caseb_wedge` programs and their dependencies.

C10 — Lean source and both computational report bridges:

```sh
"$PY" checks/report_bridge.py --write "$OUT/CompositionU3ReportP16.lean"
"$PY" checks/report_bridge.py --independent "$OUT/s3.jsonl" \
  --primary-report "$OUT/primary/s23/result_p16.json" \
  --signatures "$OUT/primary/s23/vfs.json"
"$PY" checks/test_report_bridge.py --independent "$OUT/s3.jsonl" \
  --primary-report "$OUT/primary/s23/result_p16.json" \
  --signatures "$OUT/primary/s23/vfs.json"
```

Expected: byte-identical regeneration of `CompositionU3ReportP16.lean`
from the shipped source; all 629 row signatures, verdicts, ROOT and FORCED
flags match; all 890 MATCH, 230 NO-COUNT and 32 NO pairs agree; nineteen
corruption controls rejected. Byte comparison is unconditional; `--write`
also produces a separate inspectable file. These paths follow C9's
`--part all`; a separate `--part s23 --out DIR` instead writes directly
under DIR. All row, class and figure indices are zero-based.

The full-signature source has its own decompressed SHA pin and both source
files are manifest-pinned. The Lean header itself pins only the primary
report, whose coarse facet/count data cannot distinguish the extra from
A510001. C9 regenerates full signatures, restores the pinned presentation
order and passes that actual ordered `vfs.json` to S3. C10 checks each row
against that input and the pinned full signature, including interval
identity. The unique extra is class 18,figure 0,Lean row 12; A510001 belongs
to the same class and its row 12 pair is explicitly NO, not NO-COUNT.
Their exact-star interpretation in Lean remains the external
U3Realizations obligation. A signature hash is not that geometric proof.

The candidate universe consists of every retained row in a class times
every known name admitted by radius to that class: exactly 1,152 pairs.
Both directions of the model/class inventory agree, and every one of the
890 names matches exactly one row. All other names are rejected by the
radius/model-admission stage; an absent pair alone is not a proof of NO.
C10 checks inventory consistency and every pair status; C2/C9 perform the
underlying geometric admission and exclusion checks. Interval MATCH is
not an exact equality certificate. Existence plus elimination leaves the
sole remaining row for each name, with aliases allowed within a row.

Fresh-primary comparison includes **every serialized Lean row field**,
including integer diagnostic counters. Independent comparison checks the
semantic projection, because its search/group multiplicities differ.
No general Python-to-Lean contract translator is claimed. The other
literal counts and P1 rational ranges are checked against their specified
values by executable assertions and written inspection; `stageOneOmega`
is a geometric Lean data field whose concrete interpretation remains
external. See [report provenance](report-provenance.md).

C11 — reconcile search multiplicities and the mirror exclusions:

```sh
"$PY" checks/encoding_correspondence.py \
  --primary-report "$OUT/primary/s23/result_p16.json" \
  --signatures "$OUT/primary/s23/vfs.json" \
  --independent "$OUT/s3.jsonl" --output "$OUT/accounting.json"
```

Expected: primary 633 completed states reduce to629 encodings; three extra
states represent the extra candidate and one represents A511111.
Independent 657 groups consist of629 primary-corresponding groups and
28 additional snub-product mirror alternatives, excluded by separation.
The primary search cuts those alternatives earlier by cell-patch mismatch.
C11 reruns all 28 normal searches, then a separately labeled diagnostic
which temporarily bypasses only that cut:56 distinct completed encodings,
the original28 preserved, and all 28 additional encodings have strict
full-star separation witnesses. Full signatures and class mappings agree
with independent S3. This diagnostic is not a replacement for either
normal exhaustive search or the written proof of pruning soundness.

The two implementations use shared, separately audited inputs and written
geometry. Their independence is in code; neither agreement nor the single
report bridge is an independent proof of every premise. The P16 extra's
primary development has two branches; independent development has four
nodes. The chosen cycle closes exactly at R=1 (cosines 1/5,−1/5,1/5,−1/5),
so whole-class ROOT uniqueness proves that root is 1. DEV still operates
on interval enclosures for the entire class, not a rounded substitute.

## Literal contract clauses and data transport

These field names refer to Appendix A. Every row still needs a written
interpretation of the numerical data as exact geometry; no Python command
constructs a Lean proof term. P16 means that polygon sizes in the finite
library are at most 16. `historical_comparison=false` means that the S3
coverage audit does not accept by matching an old S3 result: it checks the
new run's coverage and provenance. It does not mean that inputs are unshared.

- LIB: `model_named`, `model_hull` and `vertices_exact` use the construction
  proofs and exact face certificates; `radius_enclosed`,
  `coordinates_enclosed` and `angles_enclosed` use rigorous coordinates,
  radii and the word-angle proof. C1 rebuilds the local library and checks
  containment; C7 additionally checks exceptional whole models. Arbitrary
  real-valued Lean model data are not accepted just by comparing counts.
- S1: `cycle_count`, `listed_admissible`, `distinct_classes`, `complete`
  are full canonical closed-walk enumeration with the angle-length bound.
  `reciprocal_enclosed` and `roots_cover` combine exact maximum-radius
  bounds, the extended reciprocal domain and certified root isolation.
  `with_roots`, `without_roots`, `flat_exact`, `flat_count`,
  `degenerate_exact`, `degenerate_count` use the exact status tests and
  inventories in C1. Root intervals cover all zeros, including domain
  endpoints; small subdivision leaves can merge into larger intervals.
- S2: `signature_count` and `empty_class` are finite accounting, including
  the explicit empty triangle-cycle class 25. `complete` quantifies over
  every actual figure at every radius in each surviving class. Its proof
  needs exhaustive hinges/labels and exact placement equivalences, not
  just the 629 count. C8 checks the C1-to-C2 class/interval connection.
- ROOT: `edge_root` quantifies over every retained signature, not just
  KNOWN rows. It needs a strict endpoint sign change, nonzero derivative
  over the whole reciprocal class hull and a unique zero. C2 computes
  those witnesses; its final count script additionally requires at least
  one whole-class UNIQUE witness for every one of the 629 signatures,
  including the wholly refuted signature. This checks report coverage;
  `s3_radius.py` supplies the interval argument.
- DEV: `refutation` concerns a hypothetical uniform polytope with the
  refuted encoding's actual root, center and full incident-facet star.
  U3Realizations' written coverage and encoding correspondence place it
  in the appropriate realization list; C2 and C9 exhaust their independent
  and primary development routes. C10 checks the full cyclic signature
  and the class/figure binding to the primary refuted Lean row 12. Figure shape alone and C6 alone are insufficient.
- B2: `type_i`, `type_ii`, `type_iii` quantify over integer n ≥ 17 and their
  respective allowed configurations/parameters; type iii includes every
  polynomial root in (-1,1). C1 checks the finite residual ranges, with
  the written cutoff and exact Ω containment supplying the infinite tail.
  The geometric definition of `stageOneOmega` is linked externally to
  the recorded enclosing intervals; it is not an arbitrary substituted Ω.
- P1: `configurations`, `closable`, `nonclosable`, `degenerate`, `family`
  and `excluded` are the six inventory sets in C3. Their cardinality fields
  `configurations_count`, `closable_count`, `nonclosable_count`,
  `degenerate_count`, `family_count` and `excluded_count` require
  168, 137, 28, 3, 83 and 67, respectively. The five equivalences
  `configurations_iff`, `closable_iff`, `nonclosable_iff`, `degenerate_iff`,
  `family_iff`, plus `excluded_subset`, link them to the stated predicates. `separation` uses C4's literal rational ranges and
  all 36 bounded tails. `delta44`, `delta333_range`, `delta36_range`
  require the written identities/monotonicity argument, not sampled n.
  `survivors` gives the 16 literal family configurations. The other 54
  closable configurations have no family-size polygon; together the 54
  and 16 form the 70 unpaired type-i W fans. Thus none is dropped.
- W: `no_long_pair` and `fan_distances` are distinct obligations on every
  finite `RealizesWFan`, with the exact `WListed` domains and allowed
  points. C3 checks these through the chart correspondence and supporting
  inequalities; C5 only supplies the free-box bound for four unbounded
  paired families, not all 127 fans. The chart correspondence is a written
  proof obligation and cannot follow from numerical success alone.
- PartnerRadiusFilter: `exclude_ii` is separation from the antiprism-height
  alternative, and `force_equal` compares each of seven exceptional slices
  to the three unbounded tail families and 36 bounded integer tails. C3
  recomputes the seven singleton lists; monotonic closed-form bounds cover
  the unbounded tails. The literal `PartnerTail` domain does not include
  the extra sampled nonclosable tails in diagnostic code.
- U3Realizations: `class_valid`, `class_indices`, `signature_valid`,
  `signature_complete`, `signature_indices` are row/class/signature
  accounting. `complete` covers all full geometric stars;
  `encoding_rigid` requires equal radius and equal full rooted encoding
  to imply star congruence. C2 checks its independent version of coverage
  and rigid template correspondences. C9 also replays the primary raw encoding and C10 checks the
  complete logical row projection against C2 and the Lean table. Rooted determinism supplies the external semantic argument.
- U3Identification: `admitted` needs actual known uniform models, their
  roots/centers/radii and full library-facet admission; these use the
  construction proofs and C2's model checks. `soundNO` and `soundNOCOUNT`
  need strict exhaustive frame rejection and exact neighbor counts.
  C9 replays the primary raw encoding; C10 checks each row/name
  elimination against both the independent report and the Lean table.
  There is no additional MATCH or completeness field in U3Identification:
  coverage comes from U3Realizations, and finite other-row exclusions plus
  the soundness fields yield the derived `identified_row` theorem.
- U3Forcing: `checked` supplies `U3ForcingCheck` for every flagged row and
  admissible geometric star. Its four fields are `complete`,
  `retained_nonempty`, `encoding_unique`, `encoding_sound`. The paper's
  primary argument uses complete centered candidate maps and anchored
  exact codes. C2 supplies geometric continuation forcing by another
  encoding/coset route. C9 replays the primary anchored-code implementation; C10 checks
  the row flags against the independent report and the Lean table.
  Those checks do not construct the exact universal Lean contract.

The 181 LIB types and 181 S2 models are the same canonical four-dimensional
library, rebuilt and checked independently.

The primary programs, their source report and the table generator are
now shipped. The former packaging limitation is corrected. No claim that
separate successful computations construct jointly satisfiable Lean data
follows: the fields also require exact real models, functions, isometries
and universal geometry-to-data correspondences. The written proofs give
these interpretations outside Lean; all twelve formal inputs remain
hypotheses of the conditional composition.

For the headline statement, see `lean/Uniform5/CompositionGeometry.lean`
(`Uniform`, `UnitUniform`), `CompositionKnownFiveNames.lean`, and
`CompositionMainClassification.lean`, as explained in paper §7 and
[lean/README.md](../lean/README.md). The toolchain is Lean v4.19.0;
`lean/lake-manifest.json` pins Mathlib to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. `Audit.lean` rejects every
collected axiom other than the three listed foundations, including
`sorryAx` and `Lean.ofReduceBool` if present. It audits logical dependency,
not every compiler or foreign-function execution path; no stronger audit
of `extern` or `implemented_by` is asserted.

The lower-dimensional premise is Möller's 2004 thesis and the corresponding
[Results in Mathematics article](https://doi.org/10.1007/BF03322887),
following Conway–Guy's list, plus the cited convex uniform-polyhedron
classification. These published classification premises are not
re-proved or independently referee-reviewed by this bundle.

The known-name list and models have their own C2 provenance. `unpack_inputs.py`
checks the decompressed known-name list against both input manifests;
`stage3.py` records its byte digest and each class's parsed-list digest;
`audit_stage3.py` authenticates both and checks complete model-source and
certificate inventories. Model admission checks construction binding,
radius and facet types. These checks are separate from C8's class/interval
bridge. The written construction theorems still supply uniformity,
transitivity and the geometric interpretation; hashes establish none of
those facts and do not construct a Lean instance. The structural/lazy model
certificates are not an expansion and all-pairs check of every full orbit.

For W, `Admissible` includes distance at least one from every fan vertex;
`Allowed` instead means a fixed fan vertex outside the distinguished ends.
The free-point separation constraints apply only to `Admissible`. P checks
two admissible points, V an admissible point against every fixed fan vertex;
when both points are allowed, `no_long_pair` already has its conclusion.
F separately checks nonspecial fan-vertex distances. The expanded §5.6.2
paragraphs “Admissible points, allowed vertices, and the exact tests”,
“The lateral cone and coordinate conventions”, “The four family charts
and their bounds”, and “Unpaired families and bounded slices” give exact
thresholds, domains, explicit family points, rational box bounds and
continuous boundary expressions. In particular the 36 bounded slices use
`FanBounded`, a fixed-integer-m type-I chart, while all 16 P1 survivors
still have lateral polygon sizes at most 16 and belong to the 70 unpaired
rows. The seven exceptional slices retain only their n=m conclusions.

## Count 104 and Open Problem Garden

The finite convention is 19 A5 forms, 31 B5 forms, 8 further D5 forms,
and 47 prisms over the fixed four-dimensional bases. The only overlap
between that prism sublist and the rank-five sublist is the 5-cube,
`B500001 = prism-B40001`; hence 19 + 31 + 8 + 47 − 1 = 104.
Existence is from the construction proofs (§3.3). Pairwise noncongruence
and name aliases are justified in §3.4 and §4.5.3: different signatures
are invariant, while a common rooted star and forcing identify the whole
polytope. The 890 names are aliases for 628 objects at P16; 104 selects the
fixed sublist from those classes. The remaining classes are product-family
members at that cutoff. The 47 prisms include the prism over the grand antiprism. The same check
also verifies the remaining classes by complete parameter-to-class
bijections:420 products (`14 × 30` non-prismatic polyhedral bases),
105 unordered polygon-pair products, and a single cube already counted
among the 104. Their exact class sets exhaust all 628, so
`628 = 104 + 420 + 105 - 1`. The30 bases are four non-cubic Platonic solids,
13 Archimedean solids and13 antiprisms with parameter 4 through 16. This
breakdown is computed from the audited name classes, not just asserted
from its arithmetic. The infinite constructions are `{p} × {q} × [0,1]`
and `{p} × Q` for a convex uniform polyhedron Q (the former is included
in the latter when Q is a prism). This overlapping description does not
attempt to infer Open Problem Garden's undocumented partition.
The same cube is `{4}xcube` in the infinite product families. This is a
convention for the finite sublist, not a disjoint partition from every
member of those families; the theorem asserts coverage.

[Open Problem Garden](https://www.openproblemgarden.org/op/convex_uniform_5_polytopes),
checked October 20, 2026, states two infinite classes and 105 additional
examples, but gives no component counts or explanation of overlap. Its
105 equals the subtotal 19 + 31 + 8 + 47. Failure to subtract the cube is
therefore consistent with that number, but the page does not establish
that this was its reason. No historical reconciliation is claimed. The
proof uses the generated list and checked congruence classes, not 105.
