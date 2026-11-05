"""Extract the trivial-phi rows of the exceptional f_{e,phi} tables (Reiner-Sommers
arXiv:1605.09172v2 source, section 3.6, up to the next section heading) as raw LaTeX: type,
label, exponents, formula."""
import json, re, sys

src = open(sys.argv[1], encoding="utf-8").read()
lines = []
for ln in src.split("\n"):
    m = re.search(r"(?<!\\)%", ln)
    lines.append(ln[: m.start()] if m else ln)
text = "\n".join(lines)
header = r"\subsection{The $f_{e, \phi}$ for the exceptional groups}"
start = text.index(header)
text = text[start:]
# stop at the end of section 3.6: the next \section or \subsection
end = re.search(r"\\(sub)*section\{", text[len(header):])
if end:
    text = text[: len(header) + end.start()]
out = []
cur = None
for chunk in re.split(r"\\\\", text):
    t = re.search(r"\\multicolumn\{3\}\{\|c\|\}\{\$([EFG])_\{(\d)\}\$\}", chunk)
    if t:
        cur = t.group(1) + t.group(2)
        continue
    if cur is None or chunk.count("&") != 2:
        continue
    lab, ex, f = [c.strip() for c in chunk.split("&")]
    lab = re.sub(r"\\hline", "", lab).strip()
    lab = " ".join(lab.split())
    f = " ".join(f.replace(r"\hline", "").split())
    ex = ex.strip().strip("$").replace("^{}", "").strip()
    if "multicolumn" in lab or not lab:
        continue
    out.append({"type": cur, "label": lab, "exponents": ex, "f": f})
json.dump(out, sys.stdout, ensure_ascii=False, indent=0)
