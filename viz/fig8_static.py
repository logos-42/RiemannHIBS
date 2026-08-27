#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""fig8_static — static snapshot of the zero spiral (bilingual).

Left:  3D helical cylinder — the image of the critical line is the
       spiral of radius sqrt(e); the zeros gamma_1..gamma_6 lie on it.
Right: 2D projection — the circle |w| = sqrt(e) with the zero stars.
Bilingual: FIG_LANG=en -> viz/fig8_static_en.png, zh -> fig8_static_zh.png.
"""
import mpmath as mp
import numpy as np
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
from mpl_toolkits.mplot3d import Axes3D  # noqa

LANG = os.environ.get("FIG_LANG", "zh")

T = {
    "en": {
        "spiral": "critical-line image = spiral (radius $\\sqrt{e}$)",
        "z_axis": "height $t$",
        "title3d": "The zero spiral: zeros $\\gamma_1..\\gamma_6$ on the critical-line image",
        "circle": "circle $|w| = \\sqrt{e}$",
        "circ_e": "$|w| = e$",
        "title2d": "Projection: zeros on the critical circle",
        "zeros": "zeros $\\gamma_k$",
        "re_w": "Re $w$", "im_w": "Im $w$",
    },
    "zh": {
        "spiral": "临界线像 = 螺旋 (半径 $\\sqrt{e}$)",
        "z_axis": "高度 $t$",
        "title3d": "零点螺旋: 零点 $\\gamma_1..\\gamma_6$ 在临界线像上",
        "circle": "圆周 $|w| = \\sqrt{e}$",
        "circ_e": "$|w| = e$",
        "title2d": "投影: 零点在临界圆上",
        "zeros": "零点 $\\gamma_k$",
        "re_w": "Re $w$", "im_w": "Im $w$",
    },
}[LANG]

OUT = "viz"
SQRT_E = float(np.e) ** 0.5
N_ZEROS = 6
T_MAX = 42.0          # covers gamma_6 ~ 37.59
TURNS = 2.5

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

gammas = [float(mp.im(mp.zetazero(n))) for n in range(1, N_ZEROS + 1)]

fig = plt.figure(figsize=(12.5, 5.6))
ax3 = fig.add_subplot(1, 2, 1, projection="3d")
ax2 = fig.add_subplot(1, 2, 2)

# ---------- 3D: helical cylinder ----------
tt = np.linspace(0, TURNS * 2 * np.pi, 2000)
ax3.plot(SQRT_E * np.cos(tt), SQRT_E * np.sin(tt), tt, "r-", lw=1.1, alpha=0.55,
         label=T["spiral"])
for k in range(int(TURNS) + 2):
    th = np.linspace(0, 2 * np.pi, 120)
    ax3.plot(SQRT_E * np.cos(th), SQRT_E * np.sin(th), np.full(120, k * 2 * np.pi),
             "gray", lw=0.3, alpha=0.35)
# zeros on the spiral (red, all reached at t = T_MAX)
for g in gammas:
    ax3.scatter([SQRT_E * np.cos(g)], [SQRT_E * np.sin(g)], [g],
                c="red", s=70, depthshade=False, zorder=10)
ax3.set_xlabel(T["re_w"]); ax3.set_ylabel(T["im_w"]); ax3.set_zlabel(T["z_axis"])
ax3.set_title(T["title3d"], fontsize=11)
ax3.set_xlim(-2, 2); ax3.set_ylim(-2, 2); ax3.set_zlim(0, TURNS * 2 * np.pi + 2)
ax3.legend(loc="upper left", fontsize=8)

# ---------- 2D: circle projection ----------
th2 = np.linspace(0, 2 * np.pi, 400)
ax2.plot(SQRT_E * np.cos(th2), SQRT_E * np.sin(th2), "r-", lw=2.2,
         label=T["circle"])
ax2.plot(np.e * np.cos(th2), np.e * np.sin(th2), "b-", lw=1, alpha=0.5,
         label=T["circ_e"])
for g in gammas:
    ax2.plot([SQRT_E * np.cos(g)], [SQRT_E * np.sin(g)], "r*", ms=14)
ax2.axhline(0, color="k", lw=0.5); ax2.axvline(0, color="k", lw=0.5)
ax2.set_xlim(-3.2, 3.2); ax2.set_ylim(-3.2, 3.2)
ax2.set_aspect("equal")
ax2.set_xlabel(T["re_w"]); ax2.set_ylabel(T["im_w"])
ax2.set_title(T["title2d"], fontsize=11)
ax2.legend(loc="upper left", fontsize=8)

plt.tight_layout()
fname = f"{OUT}/fig8_static_{LANG}.png"
plt.savefig(fname, dpi=200, bbox_inches="tight")
plt.close(fig)
import os as _os
print(f"written {fname} ({_os.path.getsize(fname)//1024} KB)")
