"""Turn the extracted LaTeX rows into plain formulas: B(x) is the q-integer [x]_q,
q**(..) a power of q, m the parameter. Keeps only trivial-phi principal-in-Levi rows
(no phi, no (a_i)/(b_i) in the Bala-Carter label). Writes krew_tables.json."""
import json, re, sys

rows = json.load(open(sys.argv[1], encoding="utf-8"))

def frac(s):
    while True:
        i = s.find(r"\frac")
        if i < 0:
            return s
        j = i + 5
        args = []
        for _ in range(2):
            while s[j] == " ":
                j += 1
            assert s[j] == "{", s
            depth, k = 0, j
            while True:
                if s[k] == "{": depth += 1
                elif s[k] == "}":
                    depth -= 1
                    if depth == 0: break
                k += 1
            args.append(s[j + 1:k]); j = k + 1
        s = s[:i] + "((" + args[0] + ")/(" + args[1] + "))" + s[j:]

def label(l):
    l = l.strip("$ ").replace(r"\Tilde{A}", "~A").replace(r"\Tilde{A", "~A")
    l = re.sub(r"_\{(\d)\}", r"\1", l); l = re.sub(r"_(\d)", r"\1", l)
    l = l.replace("{", "").replace("}", "").replace(" ", "").replace("$", "")
    return l

extra = {}
for r in rows:
    lab = r["label"]
    if "[" in lab and r["exponents"] != "-":
        base = (r["type"], label(lab.split(",")[0]))
        extra.setdefault(base, []).extend(int(x) for x in r["exponents"].replace(" ", "").split(","))
out = []
for r in rows:
    lab = r["label"]
    if "[" in lab or "(a" in lab or "(b" in lab:
        continue
    f = r["f"].strip().strip("$").strip()
    ex = [int(x) for x in r["exponents"].replace(" ", "").split(",")] if r["exponents"] != "-" else []
    if f.startswith(r"\prod"):
        n = int(re.search(r"\^(\d)", f).group(1)); assert n == len(ex)
        e = "*".join(f"B(m-{x})/B({x+1})" for x in ex)
    else:
        e = frac(f).replace(r"\cdot", "*")
        e = re.sub(r"q\^\{([^}]*)\}", r"q**(\1)", e)
        e = re.sub(r"q\^(\d+)", r"q**\1", e)
        e = re.sub(r"\[([^\]]*)\]\^(\d+)", r"B(\1)**\2", e)
        e = re.sub(r"\[([^\]]*)\]", r"B(\1)", e)
        e = " ".join(e.split())
        assert not re.search(r"[\\{}\[\]]", e), e
    out.append({"type": r["type"], "label": label(lab), "label_tex": lab,
                "exponents": ex,
                "os_exponents": sorted(ex + extra.get((r["type"], label(lab)), [])), "f_tex": r["f"], "f": e})
json.dump(out, sys.stdout, ensure_ascii=False, indent=1)
