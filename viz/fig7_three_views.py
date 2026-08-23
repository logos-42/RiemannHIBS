#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig7: 同一零点集的三视图 — 直线(s) / 圆(w=e^s) / 螺旋(万有覆盖柱面)
回答: "零点在圆上和直线上有什么区别? 圆是什么样? 有螺旋线吗?"
"""
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
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

OUT = "viz"
SQRT_E = float(np.e) ** 0.5
N = 6
gammas = [float(mp.im(mp.zetazero(n))) for n in range(1, N + 1)]

fig = plt.figure(figsize=(15, 5.2))

# ---------------- 左: s 平面 (直线) ----------------
a1 = fig.add_subplot(1, 3, 1)
t = np.linspace(-25, 25, 400)
a1.plot([0.5, 0.5], [-25, 25], "r-", lw=2)
a1.plot([1, 1], [-25, 25], "b-", lw=1, alpha=0.6)
for g in gammas:
    a1.plot(0.5, g, "r*", ms=10)
    a1.plot(0.5, -g, "r*", ms=7, alpha=0.5)
a1.plot(1, 0, "ko", ms=8)
a1.axhline(0, color="k", lw=0.5)
a1.set_xlim(-1.5, 3); a1.set_ylim(-25, 25)
a1.set_xlabel("Re s"); a1.set_ylabel("t = Im s")
a1.set_title("① s 平面: 零点在直线\nRe s = 1/2 (无限延伸)")
a1.annotate("极点 s=1", (1, 0), textcoords="offset points", xytext=(8, 8), fontsize=9)

# ---------------- 中: w 平面 (圆) ----------------
a2 = fig.add_subplot(1, 3, 2)
th = np.linspace(0, 2 * np.pi, 800)
a2.plot(SQRT_E * np.cos(th), SQRT_E * np.sin(th), "r-", lw=2,
        label="圆 |w| = √e ≈ 1.649")
a2.plot(np.e * np.cos(th), np.e * np.sin(th), "b-", lw=1, alpha=0.6,
        label="|w| = e (极点/收敛边界)")
for g in gammas:
    w = np.exp(0.5 + 1j * g)
    a2.plot(w.real, w.imag, "r*", ms=10)
a2.plot(np.e, 0, "ko", ms=8)
# 平凡零点 (圆内点列)
for k in range(1, 5):
    a2.plot(np.exp(-2 * k), 0, "gx", ms=7)
a2.axhline(0, color="k", lw=0.5); a2.axvline(0, color="k", lw=0.5)
a2.set_xlim(-3.4, 3.4); a2.set_ylim(-3.4, 3.4)
a2.set_aspect("equal")
a2.set_xlabel("Re w"); a2.set_ylabel("Im w")
a2.set_title("② w = e^s 平面: 零点在圆\n|w| = √e (紧, 内外分离)")
a2.legend(loc="upper left", fontsize=8)

# ---------------- 右: 万有覆盖柱面 (螺旋) ----------------
a3 = fig.add_subplot(1, 3, 3, projection="3d")
# 螺旋柱面: 临界线的像在 (Re w, Im w, 圈数层) 坐标下 = 半径 √e 的螺旋
tt = np.linspace(0, 4 * np.pi, 1200)
a3.plot(SQRT_E * np.cos(tt), SQRT_E * np.sin(tt), tt, "r-", lw=1.6,
        label="临界线像 = 螺旋 (半径 √e)")
a3.plot(np.e * np.cos(tt), np.e * np.sin(tt), tt, "b-", lw=0.8, alpha=0.5,
        label="|w| = e (另一螺旋)")
# 零点: 高度 = γ_n, 角度 = γ_n mod 2π
for g in gammas:
    a3.scatter([SQRT_E * np.cos(g)], [SQRT_E * np.sin(g)], [g],
               c="red", s=60, depthshade=False)
    a3.scatter([SQRT_E * np.cos(-g)], [SQRT_E * np.sin(-g)], [abs(g)],
               c="red", s=30, alpha=0.5, depthshade=False)
# 层标记 (每 2π 一层)
for k in range(5):
    a3.add_line(plt.Line2D([0], [0], color="gray", lw=0.4, alpha=0.4))
a3.set_xlabel("Re w"); a3.set_ylabel("Im w")
a3.set_zlabel("圈数层 t (第三维)")
a3.set_title("③ 万有覆盖柱面: 圆展开成螺旋\n每 2π 一层; 零点=螺旋上的点")
a3.legend(loc="upper left", fontsize=8)

fig.suptitle("同一零点集的三视图: 直线 (s) — 圆 (w=e^s) — 螺旋 (万有覆盖展开)",
             fontsize=14)
fig.tight_layout(rect=[0, 0, 1, 0.93])
fig.savefig(f"{OUT}/fig7_three_views.png", dpi=150)
plt.close(fig)
print("fig7_three_views.png 已生成")

# ---------------- 附加: 零点在圆上的聚点结构 (最小角度间隙) ----------------
print()
print("零点在圆上的角度间隙 (γ mod 2π):")
for M in [30, 100, 300]:
    gs = np.array([float(mp.im(mp.zetazero(n))) for n in range(1, M + 1)])
    ths = np.sort(gs % (2 * np.pi))
    gaps = np.diff(np.concatenate([ths, [ths[0] + 2 * np.pi]]))
    print(f"  前 {M:3d} 个零点: 最小角度间隙 = {gaps.min():.4f} rad"
          f"  (最大 = {gaps.max():.4f})")
print("最小间隙随 N 减小 → 角度在圆上趋于稠密的雏形 (聚点=全圆, 猜测非定理)")
