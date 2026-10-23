#!/bin/sh
# Corruption controls for checker 1 (check_receipts.py, cover_check.py, witness_check.py).
# usage: corruptions.sh DATADIR RECEIPTDIR U0 U1 WORKDIR
# RECEIPTDIR holds accepted batch files for units U0..U1-1. Each corrupted copy must be REJECTED.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
D=$1; R=$2; U0=$3; U1=$4; W=$5
mkdir -p "$W"
fails=0
expect_reject() { # name, command...
  name=$1; shift
  if "$@" > "$W/$name.out" 2>&1; then echo "FAIL $name (accepted)"; fails=$((fails+1)); else echo "PASS $name rejected: $(tail -1 "$W/$name.out")"; fi
}
fresh() { rm -rf "$W/r"; cp -r "$R" "$W/r"; }
chk() { python3 -I "$HERE/check_receipts.py" 65 5 "$D" "$1" "$W/r" --kmin-file "$W/kmin.tsv" --range "$U0" "$U1"; }
# baseline acceptance (and the kernel-minimal census, recomputed once)
rm -rf "$W/r"; cp -r "$R" "$W/r"
python3 -I "$HERE/check_receipts.py" 65 5 "$D" "$D/units.tsv" "$W/r" --range "$U0" "$U1" --write-kmin "$W/kmin.tsv" | tail -1
B=$(ls "$W/r" | grep '^batch_' | sort | head -1); B2=$(ls "$W/r" | grep '^batch_' | sort | sed -n 2p)
fresh; sed -i '1d' "$W/r/$B";                                   expect_reject deleted_receipt chk "$D/units.tsv"
fresh; head -1 "$W/r/$B" > "$W/dup"; sed -i "1r $W/dup" "$W/r/$B2"; expect_reject duplicate_unit chk "$D/units.tsv"
fresh; awk -F'\t' 'BEGIN{OFS="\t"} NR==1{$10=$10+1} {print}' "$W/r/$B" > "$W/t" && mv "$W/t" "$W/r/$B"; expect_reject list_size chk "$D/units.tsv"
fresh; awk -F'\t' 'BEGIN{OFS="\t"} NR==1{$14=$14+1} {print}' "$W/r/$B" > "$W/t" && mv "$W/t" "$W/r/$B"; expect_reject pairs_count chk "$D/units.tsv"
fresh; sed -i 's/keybits=64/keybits=12/' "$W/r/$B";              expect_reject keybits12 chk "$D/units.tsv"
fresh; rm "$W/r/$B";                                             expect_reject missing_batch chk "$D/units.tsv"
fresh; awk -F'\t' 'BEGIN{OFS="\t"} NR==1{$3=$3+1} {print}' "$W/r/$B" > "$W/t" && mv "$W/t" "$W/r/$B"; expect_reject wrong_classes chk "$D/units.tsv"
fresh; echo "SOLUTION	$U0	0	0	0	0" >> "$W/r/solutions.tsv";        expect_reject unreported_solution chk "$D/units.tsv"
echo "SOLUTION	0	0	0	0	0" > "$W/false_solution.tsv";          expect_reject false_solution python3 -I "$HERE/witness_check.py" 65 "$W/false_solution.tsv"
sed '7d' "$D/units.tsv" > "$W/units-gap.tsv";                    expect_reject cover_gap python3 -I "$HERE/cover_check.py" 65 5 "$D" "$W/units-gap.tsv"
echo "corruptions failed: $fails"
[ "$fails" -eq 0 ]
