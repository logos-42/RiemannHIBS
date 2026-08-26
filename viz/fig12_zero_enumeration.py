#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig12: 零点孤立与可枚举性 — ζ 零点 ↔ ℕ 一一对应的直观
======================================================
Lean 侧已证 (Abundance.lean §7):
  zeta_zero_isolated: 每个非平凡零点的去心邻域无其他零点 (identity theorem)
配图:
  左: s 平面, 前 10 个零点 (红星) + 隔离盘 (每个零点周围无其他零点的圆盘)
  右: γ_n vs n 阶梯 — 每个自然数 n 恰好对应一个零点虚部 γ_n (双射直观)
"""
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
from matplotlib.patches import Circle

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
N = 10
gammas = [float(mp.im(mp.zetazero(n))) for n in range(1, N + 1)]

fig, (a1, a2) = plt.subplots(1, 2, figsize=(13, 5.4))

# ---------------- 左: s 平面 — 零点孤立 ----------------
t = np.linspace(-6, 60, 400)
a1.plot([0.5, 0.5], [t[0], t[-1]], "r-", lw=1.5, alpha=0.6,
        label="临界线 Re s = 1/2")
for i, g in enumerate(gammas, 1):
    a1.plot(0.5, g, "r*", ms=12)
    a1.annotate(str(i), (0.5, g), textcoords="offset points",
                xytext=(8, 4), fontsize=10, color="darkred")
# 隔离盘: 半径 = 到最近相邻零点距离的一半
for i, g in enumerate(gammas):
    left = gammas[i - 1] if i > 0 else g - 14.0
    right = gammas[i + 1] if i + 1 < N else g + 14.0
    r_iso = min(g - left, right - g) / 2
    a1.add_patch(Circle((0.5, g), r_iso, fill=False, ls="--",
                        edgecolor="gray", lw=1.0, alpha=0.8))
a1.axhline(0, color="k", lw=0.5)
a1.set_xlim(0, 2.2); a1.set_ylim(0, 55)
a1.set_xlabel("Re s"); a1.set_ylabel("Im s = t")
a1.set_title("零点孤立 (已证 zeta_zero_isolated):\n"
             "每个零点的隔离盘内无其他零点 (去心邻域 ζ ≠ 0)")
a1.legend(loc="lower left", fontsize=8)

# ---------------- 右: γ_n vs n — 可枚举双射 ----------------
a2.plot(np.arange(1, N + 1), gammas, "b-o", lw=1.5, ms=6)
for i, g in enumerate(gammas, 1):
    a2.annotate(f"γ{i}={g:.1f}", (i, g), textcoords="offset points",
                xytext=(0, -16), fontsize=8, rotation=30, ha="center")
a2.set_xlim(0, N + 1)
a2.set_xlabel("n (自然数序号)"); a2.set_ylabel("γ_n (零点虚部)")
a2.set_title("零点 ↔ ℕ 一一对应 (可枚举):\n"
             "每个 n 恰好一个 γ_n, 每个零点恰好一个序号\n"
             "(排序 γ₁<γ₂<… 存在性 = draft, 未形式化)")
a2.grid(True, alpha=0.3)

fig.suptitle("零点孤立 + 可枚举: '零点与 ζ 一一对应'的几何与数值证据\n"
             "(Lean 已证孤立性; 可数/排序为 draft)",
             fontsize=12.5)
fig.tight_layout(rect=[0, 0, 1, 0.9])
fig.savefig(f"{OUT}/fig12_zero_enumeration.png", dpi=150)
plt.close(fig)

# 数据
gaps = np.diff(gammas)
print(f"前 {N} 个零点: γ₁={gammas[0]:.2f} … γ₁₀={gammas[-1]:.2f}")
print(f"相邻间距: min={gaps.min():.2f}, max={gaps.max():.2f}, "
      f"均值={gaps.mean():.2f} (全 > 0 ⟹ 严格递增可排序)")
print(f"fig12_zero_enumeration.png 已生成")
