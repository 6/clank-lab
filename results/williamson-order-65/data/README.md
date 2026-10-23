# Certificate data

The compact certificate files included here suffice for both public cover
and receipt checks. No dataset download is needed. The full row set is
regenerated independently by each implementation.

| Data | Size in bytes | Meaning |
| --- | ---: | --- |
| Four `receipts-*.json.xz` containers | 2,513,840 | All 70,699 exhaustion receipts in 1,105 batches |
| Receipt files after extraction | 7,550,191 | Batch tables and the empty solutions files |
| `classes65.tsv.xz` and `units65.tsv.xz` | 1,289,560 | Compressed class census and unit cover |
| Those two tables after decompression | 3,731,762 | Class identifiers, row counts, and cover representatives |
| Regenerated `rows.bin` | 1,584,203,988 | 396,050,997 masks, four bytes per mask |

The files `solutions39.txt`, `solutions45.txt`, and `solutions55.txt` hold
the complete symmetry closures of the discovered known-case witnesses:
96, 144, and 240 ordered normalized quadruples, respectively. Each is one
equivalence class. `published-counts.tsv` supplies the nontrivial odd-order
class counts through 33 for comparison against fresh baseline enumeration;
the citation is in [the checking instructions](../checks/README.md).

## Formats

Each receipt container is an xz-compressed UTF-8 JSON object mapping a batch
file basename to its exact tab-separated text. Extracting its values restores
the original receipt bytes; the container adds no mathematical content.

A mask is an unsigned 32-bit little-endian integer. Bit $i-1$ records a
negative entry at both positions $i$ and $65-i$, for $1\leq i\leq32$;
position zero is positive. `rows.bin` concatenates classes in identifier
order, with masks strictly increasing within each class.

Each class-table line contains: identifier, base-6 compression key, signed
rowsum, seven comma-separated entries of the symmetric length-13 compressed
vector, row count, row offset in `rows.bin`, and the SHA-256 digest of that
class's ascending little-endian masks. The digest compares the independently
regenerated mathematical set with the recorded census.

Each unit-table line contains: unit identifier, four class identifiers, and
the size of the unit's multiplier orbit. Identifiers run from zero through
70,698, and orbit sizes sum to 423,527. A unit is the least sorted tuple in
its orbit; the checkers independently enumerate all admissible tuples.

Each receipt line begins with `U`, followed by unit identifier, four class
identifiers, pairing index, designated position, four list sizes, pass count,
stored-side pair count, probe-side pair count, the two survivor counts,
key-match count, solution count, and CPU seconds. An `END` line records a
completed half-open unit interval and the production options. A
`SOLUTION` line would contain its unit identifier and four masks. No such
line occurs at order 65. Batch completion is credited only after its final
marker; interrupted temporary files provide no evidence.

## Full dataset record

A separate dataset record, to be deposited by the operator, would contain
the full `rows.bin`, these class and unit tables, all complete receipt
batches, and the known-case solution sets, together with these exact source
files and instructions. The core order-65 data would occupy 1,595,485,941
uncompressed bytes: rows plus the two tables plus receipt files. Archive
compression and source files change the deposit's final size, which must
be measured when it is created. No deposit has been made and no dataset
DOI is assigned here.

To check such a deposit, run the public entry point with `--work DIRECTORY`.
It reconstructs the row set from the definitions, compares every class's
count and digest, checks the complete cover with both independent
enumerators, and validates every bundled receipt. The deposited `rows.bin`
can then be compared byte for byte with `DIRECTORY/data/rows.bin` using
`cmp`. The public `--full-search` command independently recreates the
exhaustion receipts; elapsed times need not match, but the mathematical
counts and zero-solution conclusion must. Depositing data or releasing this
result is a separate action from running these checks.
