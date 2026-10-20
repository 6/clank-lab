# Certificates and data

`core-hypotheses.txt` holds the twelve computational hypotheses, verbatim from the Lean sources; the paper's appendix prints it.

`acceptance-inputs.json` lists the checkers, authoritative inputs and certificates authenticated by `PUBLIC.sha256`. Paths are relative to the bundle root. Prose and timing-bearing outputs are not acceptance pins. Outputs are compared by parsed mathematical fields.

The actual certificates remain beside their consumers under `checks/`: `independent-s1-b2/evidence/` contains cycle, radius and B2 records; `independent-merge-filter/` contains exact alias and deletion certificates; `independent-s23/inputs/` contains compressed class/model inputs and `certificates/` contains equivalences; `model_audit/` contains exceptional-model certificates. The `check_u1/`, `check_u3/`, `input_link/` and `acceptance-third/` subdirectories contain the small reference inputs these checkers consume. These are data dependencies, not external paths.

To regenerate and retain the P=16 stage-3 states, create the documented Python environments, then run from the bundle root:

```bash
bundle=$PWD
work=$(mktemp -d)
py="$bundle/.venv/bin/python"
cd checks/independent-s23
"$py" unpack_inputs.py "$work/input" --pmax 16
"$py" run.py "$work/input/u2_classes_p16.json" "$work/s2.jsonl" --states
"$py" check_equivalence.py "$work/input/u2_classes_p16.json" certificates/equivalences-p16.json
"$py" stage3.py --states "$work/s2.jsonl" --models models \
  --known "$work/input/u3_known_p16.json" --output "$work/s3.jsonl"
"$py" audit_stage3.py --classes "$work/input/u2_classes_p16.json" \
  --states "$work/s2.jsonl" --results "$work/s3.jsonl" --models models \
  --known "$work/input/u3_known_p16.json" --pmax 16 \
  --receipt "$work/s3.jsonl.frozen.json"
```

The generated files are in the new temporary directory printed by `printf '%s\n' "$work"`. The input decompressor authenticates the expanded data. No private archive is needed.

## Construction-list provenance

The known-name lists are generated from Wythoff and Cartesian-product recipes, not transcribed from a community catalogue. At P=16 there are 890 distinct recipe names: 93 Wythoff patterns (31 nonempty ring masks for each of A5, B5 and D5), 181 facet-prism names, and 616 polygon products (14 polygon sizes times 44 polyhedron factors). Several names describe the same polytope. The public exact constructor in `checks/independent-s23/models.py` enumerates the same recipe families; the names and facet aliases are shared inputs, not an independent naming census. The lower-dimensional library is rebuilt by `checks/independent-s1-b2/library.py`. These paths are relative to the bundle root.

The exceptional-model JSON files contain generated exact support and symmetry certificates. No Wiki prose, artwork or catalogue rows are included in these construction lists. Short conventional polytope names and abbreviations are retained; the mathematical constructions and historical cataloguing work are credited in the manuscript and main README.
