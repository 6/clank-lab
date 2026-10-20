# Source and replay of the Lean P16 report

`primary-u3-p16.json.gz` decompresses to the exact primary stage-three report
whose SHA-256 is printed in `lean/Uniform5/CompositionU3ReportP16.lean`:
`938851ddf8aed87c29a2cd897d8190ff29024cba923b11f2602a0d5893e7eca7`.
The gzip header has modification time zero. The report is historical evidence,
not an input to either geometric search. It contains 563 classes, 629 retained
encodings, 633 primary search states, 628 known encodings, one refuted encoding,
and 890 matched construction names.

`primary-u2-signatures-p16.json.gz` supplies the full cyclic words in the order
used by that report. Its decompressed SHA-256 is
`425c7d239a327c7eebbd72d2caf8129a14de26f6f9e65f7e667aeef38d93156d`.
The bridge explicitly checks this digest, as well as the ordered list of
class IDs and full signature keys. Both compressed files are also pinned in
the bundle manifest. The Lean header pins the U3 report only; it does not
itself pin the U2 signature file.

The report contains only facet multisets and cycle counts, so it cannot
identify a signature by itself. In particular, the extra candidate and the
known `A510001` star share those coarse data. The ordered full-key binding is
essential. Fresh primary S2 independently enumerates and checks the full
signature set, then puts those signatures in the pinned presentation order
before passing `vfs.json` to primary S3. The bridge compares the fresh report
with that actual ordered input, including each class interval, and with the
exact Lean projection. Class, figure, realization and list-row indices in
this note and the checker are **zero-based**.

From the bundle root, using the `PY` interpreter and `OUT` output directory
defined in the hypothesis map, run these commands after C9 (`--part all`,
outputs under `$OUT/primary/s23`) and C2 (output `$OUT/s3.jsonl`):

```sh
"$PY" checks/report_bridge.py --write "$OUT/CompositionU3ReportP16.lean"
"$PY" checks/report_bridge.py \
  --primary-report "$OUT/primary/s23/result_p16.json" \
  --signatures "$OUT/primary/s23/vfs.json"
"$PY" checks/report_bridge.py --independent "$OUT/s3.jsonl"
"$PY" checks/test_report_bridge.py \
  --primary-report "$OUT/primary/s23/result_p16.json" \
  --signatures "$OUT/primary/s23/vfs.json" \
  --independent "$OUT/s3.jsonl"
```

The first command regenerates the *entire* Lean source file byte for byte,
including every numeric diagnostic and proof declaration. Its source digest
must match the header. The fresh-primary comparison requires every field in
that Lean projection to agree; timing, floating diagnostics and JSON layout
are not part of the projection.

The independent comparison keys rows by class ID and full unoriented cyclic
signature. Reversing a cycle reverses its facet order and shifts the outgoing
cell labels accordingly; all rotations and the reversed rotations are
canonicalized, with multiplicities retained. Reflections are allowed in the
classification's congruence relation, so this is an unoriented signature.
Every full signature key must occur at most once within a class among the
629 active rows. The 28 rejected mirror placements are handled separately,
not grouped into an active row by signature alone. For each active row, the
checker compares the verdict, names, every embedding exclusion, unique-root
flag and forcing flag. Exact neighbor-count exclusions become `NO-COUNT`;
other strict exclusions become `NO`. A sole remaining candidate identified
by elimination corresponds to the primary `MATCH` label. This does not turn
a surviving interval frame into a congruence proof.

The expected independent comparison is:

- 563 classes and 629 retained semantic rows;
- 890 `MATCH`, 230 `NO-COUNT` and 32 `NO` pairs, checked individually;
- 28 additional mirror placements, each strictly rejected before
  identification and belonging to a signature with a known retained placement;
- Lean row 12 is class 18, figure 0, the sole retained refutation, with a
  `REFUTED` development and the same root interval containing 1; its
  `A510001` pair must specifically be `NO`, not `NO-COUNT`.

The candidate-pair universe is derived from the known-model radius-class
inventory: for every class, take every retained row and every known
construction admitted to that class. All 1,152 such pairs must occur, with
no extra pair; each of the 890 names must match exactly one row. The
primary report's model-to-class and class-to-model inventories must agree,
and the independent identification arrays must contain exactly those
admitted names. These are checks on the inventories computed by the two
geometric replays, not an independent proof that their radius admissions
are correct; the interval, construction and admission checks remain
necessary.

The outcome audit checks all 28 separation witnesses and their exact expected
family identities. The report bridge checks their relationship to the retained
signatures. It does not rerun their geometric cuts.

The two implementations have different search multiplicities and symmetry
counts. The primary has 633 search states in 629 retained encodings; the
independent implementation retains 657 raw realizations, including the 28
additional mirror placements which it rejects later. The bridge does not
assert equality of those implementation-specific quantities. All fields of
the Lean table are regenerated from the primary report, while the independent
route checks the semantic fields listed above. Both routes group by certified
whole-star congruences, not signature equality alone.

No field of the Lean table is omitted from the **fresh primary** projection
comparison. Search-state and symmetry counts differ between implementations,
so they are not compared with independent S3. The serialized fields
`search_states`, `facets`, `vf_points`, and local `neighbors`, `unique`,
`valid_g`, `tested_g`, `failures`, `no_valid` are diagnostics. The source uses
the spelling `neighbours`. Apart from the isolated finite theorem summing
`search_states` to 633 and structural equality of report rows, these
diagnostics do not discharge the geometric classification hypotheses.
`CompositionU3ForcingInputs.lean` instead consumes the `forced` flag through
its external `checked` obligation; `CompositionU3IdentificationInputs.lean`
consumes admitted names and the `NO`/`NO-COUNT` pairs, never a numeric frame
count or `MATCH` as an equality certificate. ROOT and the extra-candidate
development have their own external obligations. Regenerating the table
and comparing replay outputs does not by itself prove those obligations
inside Lean.

The corruption controls alter the Lean diagnostics, primary figure order,
class ID, full cycle signature, verdict, known name, unique-root flag, forcing
flag, extra-candidate development, and `NO`/`NO-COUNT` distinction. They also
swap the extra candidate's signature with the known `A510001` signature,
which has the same coarse facet multiset and cycle count. Fresh-primary
controls alter a serialized diagnostic, break the report/input interval
link, swap the same-coarse-data input signatures alone and together with
their report rows, delete a candidate pair, change the model radius-class
inventory, duplicate a known name, and change the extra candidate's
`A510001` exclusion to `NO-COUNT`. All nineteen corruptions must be rejected
when a complete independent replay is supplied. Supplying the fresh primary
report and its actual ordered input applies the eight primary controls to
that fresh result; without those two arguments they use the historical
report as a smaller fixture.
