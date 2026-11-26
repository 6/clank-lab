"""Compute or replay one signed theta search. Run with Sage's Python."""
import argparse
import json
from math import prod
from pathlib import Path
from tempfile import TemporaryDirectory

from sage.all import ZZ, set_random_seed

from arithmetic import admissible_ells, case, sw_status
from certificate import certify
from segments import SegmentPriceLimit, UnresolvedEigenspace


def flags(N, ell):
    classes = 1 if ell <= 3 else (ell-1)//12 + {1: 0, 5: 1, 7: 1, 11: 2}[ell % 12]
    return int(classes * prod((q+1)*q**(e-1) for q, e in ZZ(N).factor()))


def search(ainvs, D, p, root, *, ell=None, ell_cap=271, attempts=3, flag_cap=24000,
           all_rank_two=False):
    set_random_seed(0)
    data = case(ainvs, D, p, all_rank_two=all_rank_two)
    record = {"ainvs": data["ainvs"], "N": data["N"], "D": D, "p": p,
              "arithmetic": data["status"], "trials": [], "verdict": data["status"]}
    if not data["eligible"]:
        return record
    if data["rank_plus"]["rank"] == 2:
        comparison = sw_status(data, (2, 3, 4, 5), 6000)
        record["SW"] = comparison["status"]
        record["SW_evidence"] = comparison["attempts"]
    if data["Nminus"] != 1:
        record["verdict"] = "requires_discriminant_Nminus_times_ell"
        return record
    if not data["tate_normalization_is_p_unit"]:
        record["verdict"] = "normalization_zero_mod_p"
        return record
    start, end = (ell, ell) if ell is not None else (2, ell_cap)
    primes = admissible_ells(ainvs, D, p, sign=data["eps"], start=start, stop=end+1)
    record["verdict"] = "no_admissible_prime_in_range"
    for prime in primes:
        q = prime["ell"]
        trial = {"ell": q, "raw_flags": flags(data["N"], q)}
        record["trials"].append(trial)
        if trial["raw_flags"] > flag_cap:
            trial["status"] = "over_flag_cap"
        else:
            directory = root / str(q)
            directory.mkdir(parents=True, exist_ok=True)
            (directory/"case.json").write_text(json.dumps(data, sort_keys=True) + "\n")
            try:
                trial.update(certify(data, q, directory))
            except SegmentPriceLimit as exc:
                trial.update(status="over_kernel_cap", detail=str(exc))
            except UnresolvedEigenspace as exc:
                trial.update(status="unresolved_eigenline", detail=str(exc))
            else:
                trial["status"] = "nonzero" if trial["T"] else "zero"
                if trial["T"]:
                    record["verdict"] = "Q_K_nonzero"
                    return record
        record["verdict"] = "inconclusive"
        if len(record["trials"]) >= attempts:
            break
    if ell is not None and not record["trials"]:
        raise ValueError("specified prime is not admissible with the required sign")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["compute", "replay"])
    parser.add_argument("--ainvs", type=json.loads)
    parser.add_argument("--D", type=int, required=True)
    parser.add_argument("--p", type=int, required=True)
    parser.add_argument("--label")
    parser.add_argument("--table", type=Path, default=Path(__file__).with_name("rows.jsonl"))
    parser.add_argument("--all-rank-two", action="store_true",
                        help="also test rank two over K distributed (1,1) or (0,2)")
    parser.add_argument("--ell", type=int)
    parser.add_argument("--ell-cap", type=int, default=271)
    parser.add_argument("--attempts", type=int, default=3)
    parser.add_argument("--flag-cap", type=int, default=24000)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if min(args.ell_cap, args.attempts, args.flag_cap) < 1:
        parser.error("search bounds must be positive")
    expected = None
    if args.command == "replay":
        rows = [json.loads(line) for line in args.table.read_text().splitlines()]
        expected, = [r for r in rows if (r["label"], r["D"], r["p"]) ==
                     (args.label, args.D, args.p)]
        args.ainvs = expected["ainvs"]
        if args.ell is not None:
            parser.error("replay reconstructs the complete search for the selected row")
    if args.ainvs is None:
        parser.error("compute requires --ainvs")
    with TemporaryDirectory() as temp:
        result = search(args.ainvs, args.D, args.p, args.work or Path(temp),
                        ell=args.ell, ell_cap=args.ell_cap, attempts=args.attempts,
                        flag_cap=args.flag_cap, all_rank_two=args.all_rank_two)
    if args.label:
        result["label"] = args.label
    if expected is not None and result != expected:
        raise ValueError("replay mismatch: " + json.dumps(result, sort_keys=True))
    output = json.dumps(result, sort_keys=True)
    if args.output:
        staging = args.output.with_suffix(".part")
        staging.write_text(output + "\n")
        staging.replace(args.output)
    else:
        print(output)


if __name__ == "__main__":
    main()
