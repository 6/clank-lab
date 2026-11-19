"""Figures from the stamps rerun.py saves (needs matplotlib).

python figure.py WORKDIR OUT.svg|OUT.pdf          the three images at Pluto's predicted positions
python figure.py WORKDIR OUT.pdf --blind KEY.json  blinded sheets: on each plate the image among 11 controls,
                                                    shuffled; KEY.json says which panel is the image
"""
import sys
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

W, out = sys.argv[1], sys.argv[2]
blind = "--blind" in sys.argv
panels = [("ma731", "MA 731, December 21, 1908"), ("b2247a", "B2247a, February 20, 1909"), ("b2248b", "B2248b, February 20, 1909")]
if blind:
    import json
    key = sys.argv[sys.argv.index("--blind")+1]
    fig, axes = plt.subplots(3, 12, figsize=(9.6, 3.0))
    for row, (lab, title) in zip(axes, panels):
        z = np.load(f"{W}/blind_{lab}.npz")["snr"]
        for j, (ax, s) in enumerate(zip(row, z)):
            ax.imshow(s, origin="lower", extent=[30, -30, -30, 30], cmap="gray_r", vmin=-2, vmax=8)
            ax.set_xticks([]); ax.set_yticks([])
            ax.set_title(str(j+1), fontsize=6, pad=1.5)
        row[0].set_ylabel(title.split(",")[0], fontsize=7)
    fig.tight_layout(pad=0.3, w_pad=0.1, h_pad=0.4)
    r = json.load(open(f"{W}/results.json"))["blind_cutouts"]
    json.dump({lab: dict(image_panel=v["image_panel"], panels=v["panels"]) for lab, v in r.items()}, open(key, "w"), indent=1)
    axes = []
else:
    fig, axes = plt.subplots(1, 3, figsize=(9.6, 3.5))
for ax, (lab, title) in zip(axes, panels):
    z = np.load(f"{W}/stamp_{lab}.npz")
    s = z["snr"]; h = 60
    # sky grid has east = +xi along columns; show east to the left, north up
    ax.imshow(s, origin="lower", extent=[h, -h, -h, h], cmap="gray_r", vmin=-2, vmax=8)
    ax.add_patch(plt.Circle((0, 0), 3, fill=False, color="tab:blue", lw=1.2))
    cx, cy = z["centroid"]
    ax.plot([cx], [cy], marker="+", color="tab:red", ms=9, mew=1.4)
    ax.set_title(title, fontsize=10)
    ax.set_xlabel("east offset (arcsec)", fontsize=8)
    ax.tick_params(labelsize=7)
if not blind:
    axes[0].set_ylabel("north offset (arcsec)", fontsize=8)
    fig.tight_layout()
matplotlib.rcParams["svg.hashsalt"] = "stamps"
fig.savefig(out, dpi=144 if blind else 150, metadata={"Date": None} if out.endswith(".svg") else {"CreationDate": None})
if out.endswith(".svg"):  # strip the trailing spaces matplotlib leaves in path data
    with open(out) as f:
        t = "\n".join(line.rstrip() for line in f.read().splitlines()) + "\n"
    with open(out, "w") as f:
        f.write(t)
