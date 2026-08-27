#!/usr/bin/env python3
"""fig1_projection_cross — hidden-number projection, English labels.

Left panel:  the s-plane. The critical line Re s = 1/2 (red) maps to
Right panel: the w-plane. The critical circle |w| = sqrt(e) (red);
              |w| = 1 and |w| = e are the images of Re s = 0 and Re s = 1.
The point s0 = 1/2 + i t0 maps to w0 = e^{s0} on the critical circle.
"""
import numpy as np
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

LANG = os.environ.get("FIG_LANG", "en")

T = {
    "en": {
        "title_s": r"$s$-plane: the critical line",
        "title_w": r"$w$-plane: the critical circle",
    },
    "zh": {
        "title_s": r"$s$ 平面：临界线",
        "title_w": r"$w$ 平面：临界圆",
    },
}[LANG]

# 中文字体 (zh 版需要)
if LANG == "zh":
    import matplotlib.font_manager as fm
    for _fp in ("/System/Library/Fonts/Supplemental/Arial Unicode.ttf",
                "/System/Library/Fonts/Hiragino Sans GB.ttc",
                "/System/Library/Fonts/PingFang.ttc"):
        try:
            fm.fontManager.addfont(_fp)
        except Exception:
            pass
    plt.rcParams["font.family"] = "sans-serif"
    plt.rcParams["font.sans-serif"] = ["Arial Unicode MS", "Hiragino Sans GB",
                                       "PingFang HK", "Songti SC"]
    plt.rcParams["axes.unicode_minus"] = False

e = np.e
r_c = np.sqrt(e)          # sqrt(e) ≈ 1.6487
t0 = 3.0
s0 = 0.5 + 1j * t0
w0 = np.exp(s0)           # on the critical circle

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.6))

# ---------------- left: s-plane ----------------
ax1.axhline(0, color="k", lw=0.7)
ax1.axvline(0, color="k", lw=0.7)
# Re s = 0 and Re s = 1 (images: unit circle and |w|=e)
ax1.axvline(0.0, color="0.6", lw=1.2, ls="--")
ax1.axvline(1.0, color="0.6", lw=1.2, ls="--")
# critical line Re s = 1/2 (red, bold)
ax1.axvline(0.5, color="#d62728", lw=2.6)
# the point s0
ax1.plot([s0.real], [s0.imag], "o", color="#1f77b4", ms=8, zorder=5)
ax1.annotate(r"$s = \frac{1}{2} + it$", (s0.real, s0.imag),
             textcoords="offset points", xytext=(10, 10),
             fontsize=13, color="#1f77b4")
ax1.annotate(r"$\mathrm{Re}\,s = 1/2$", (0.5, 7.0),
             textcoords="offset points", xytext=(8, 0),
             fontsize=12, color="#d62728", rotation=90, va="center")
ax1.annotate(r"$\mathrm{Re}\,s = 0$", (0.0, -6.5),
             textcoords="offset points", xytext=(-4, -12),
             fontsize=11, color="0.4", rotation=90, va="center")
ax1.annotate(r"$\mathrm{Re}\,s = 1$", (1.0, -6.5),
             textcoords="offset points", xytext=(4, -12),
             fontsize=11, color="0.4", rotation=90, va="center")
ax1.set_xlim(-1.4, 2.2)
ax1.set_ylim(-8, 8)
ax1.set_xlabel(r"$\mathrm{Re}\,s$", fontsize=13)
ax1.set_ylabel(r"$\mathrm{Im}\,s$", fontsize=13)
ax1.set_title(T["title_s"], fontsize=14)
ax1.set_aspect(0.35)
ax1.grid(alpha=0.25)

# ---------------- right: w-plane ----------------
ax2.axhline(0, color="k", lw=0.7)
ax2.axvline(0, color="k", lw=0.7)
# circles: |w|=1, |w|=e (dashed grey), critical circle |w|=sqrt(e) (red)
for r, c, ls, lw in [(1.0, "0.55", "--", 1.2),
                     (e, "0.55", "--", 1.2),
                     (r_c, "#d62728", "-", 2.6)]:
    ax2.add_patch(Circle((0, 0), r, fill=False, edgecolor=c,
                         linestyle=ls, lw=lw))
ax2.annotate(r"$|w| = 1$", (0.85, 1.05), fontsize=11, color="0.4")
ax2.annotate(r"$|w| = e$", (e + 0.12, 0.55), fontsize=11, color="0.4")
ax2.annotate(r"$|w| = \sqrt{e}$", (r_c + 0.10, 1.35),
             fontsize=12, color="#d62728")
# the image point w0 = e^{s0}
ax2.plot([w0.real], [w0.imag], "o", color="#1f77b4", ms=8, zorder=5)
ax2.annotate(r"$w = e^{s}$", (w0.real, w0.imag),
             textcoords="offset points", xytext=(12, 8),
             fontsize=13, color="#1f77b4")
# (map arrow removed per request)
ax2.set_xlim(-3.4, 3.8)
ax2.set_ylim(-3.4, 3.8)
ax2.set_xlabel(r"$\mathrm{Re}\,w$", fontsize=13)
ax2.set_ylabel(r"$\mathrm{Im}\,w$", fontsize=13)
ax2.set_title(T["title_w"], fontsize=14)
ax2.set_aspect("equal")
ax2.grid(alpha=0.25)

plt.tight_layout()
plt.savefig(f"viz/fig1_projection_cross_{LANG}.png", dpi=200, bbox_inches="tight")
print(f"written viz/fig1_projection_cross_{LANG}.png")
