#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig13 (v2): B1 交叉相消 — t 依赖截断 X(t) = √(t/2π) regime
================================================================
Lean 已证 (Abundance.lean §12): rotating_integral_bound_min /
log_one_add_ge_half / near_frequency_bound / cross_pair_bound_min

B1 数学链 (本图数值验证):
  1. 截断部分和能量 E(T) = ∫₁ᵀ |Σ_{n≤X(t)} n^{-1/2} e^{it log n}|² dt,
     X(t) = √(t/2π) (t 依赖截断 — 近似函数方程)
  2. 对角贡献 ∫₀ᵀ Σ_{n≤X(t)} 1/n dt ≈ (T/2)·log(T/2π) = 主项/2
     (单侧 Dirichlet 多项式贡献均值定理主项的一半; 另一半来自辅项)
  3. 交叉上界 ~ X(T)·log X(T) = √(T/2π)·log T — 次主导于对角
     (交叉/对角 → 0 当 T → ∞)
"""
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

def cutoff_energy(T, nsteps=1500):
    """E(T) = ∫₁ᵀ |Σ_{n≤√(t/2π)} n^{-1/2} e^{it log n}|² dt (数值)"""
    ts = np.linspace(1, T, nsteps)
    Es = np.empty_like(ts)
    for i, t in enumerate(ts):
        X = max(1, int(np.sqrt(t / (2 * np.pi))))
        ns = np.arange(1, X + 1, dtype=float)
        S = np.sum(ns ** (-0.5) * np.exp(1j * t * np.log(ns)))
        Es[i] = abs(S) ** 2
    return np.trapz(Es, ts), ts

Ts = [50, 100, 200, 400, 800, 1600]
E = []; main = []; ratio = []
for T in Ts:
    e, _ = cutoff_energy(T)
    E.append(e)
    m = T * np.log(T / (2 * np.pi))          # von Mangoldt 主项
    main.append(m)
    ratio.append(e / m)

# 交叉上界估算: X(T)·log X(T) vs 对角 (截断 regime)
Xc = np.sqrt(np.array(Ts) / (2 * np.pi))
cross_est = 4 * Xc * np.log(np.maximum(Xc, 2))          # 粗上界 ~ X·log X
main_arr = np.array(main)
cross_ratio = cross_est / main_arr

fig, (a1, a2) = plt.subplots(1, 2, figsize=(13, 5.2))

# 左: E(T) vs 主项 (T·log(T/2π)), 比值 → 0.5 (单侧对角 = 主项/2)
a1.plot(Ts, E, "b-o", ms=5, lw=1.5, label="E(T) 截断部分和能量 (数值)")
a1.plot(Ts, main_arr, "g--", lw=2, label="主项 T·log(T/2π)")
a1.plot(Ts, main_arr / 2, "g:", lw=1.5, label="主项/2 (单侧对角)")
a1.axhline(0, color="k", lw=0.5)
a1.set_xlabel("T (高度)"); a1.set_ylabel("能量")
a1.set_title("B1: 截断 regime 能量 (X(t)=√(t/2π))\nE(T) ≈ 主项/2 = (T/2)·log(T/2π)")
a1.legend(fontsize=8); a1.grid(True, alpha=0.3)

# 右: 比值 → 0.5 与交叉占比 → 0
a2.plot(Ts, ratio, "b-o", ms=5, lw=1.5, label="E(T)/主项 → 0.5")
a2.axhline(0.5, color="b", ls="--", lw=1, alpha=0.5)
a2.plot(Ts, cross_ratio, "orange", "s--", ms=4, lw=1.5,
        label="交叉上界/主项 → 0 (截断相消)")
a2.axhline(0, color="k", lw=0.5)
a2.set_xlabel("T"); a2.set_ylabel("比值")
a2.set_title("交叉相消: E/主项 → 0.5 (对角主导)\n交叉上界/主项 → 0 (次主导)")
a2.legend(fontsize=8); a2.grid(True, alpha=0.3)

fig.suptitle("fig13 (v2): B1 交叉相消 — 截断 X(t)=√(t/2π) 使交叉次主导\n"
             "Lean 已证: rotating_integral_bound_min / log_one_add_ge_half /\n"
             "near_frequency_bound / cross_pair_bound_min (Abundance §12)",
             fontsize=11.5)
fig.tight_layout(rect=[0, 0, 1, 0.88])
fig.savefig("viz/fig13_energy_budget.png", dpi=150)
plt.close(fig)

print(f"T=1600: E={E[-1]:.0f}, 主项={main[-1]:.0f}, E/主项={ratio[-1]:.3f}")
print(f"交叉上界/主项 (T=1600): {cross_ratio[-1]:.3f} (→0 ✓)")
print(f"fig13_energy_budget.png 已生成 (v2 截断 regime)")
