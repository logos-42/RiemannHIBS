#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig13: B 桥能量预算 — 对角与交叉的真实分解 (临界叶, 隐数坐标系)
================================================================
Lean 已证 (Abundance.lean §12):
  diagonal_energy:          ∫‖v_n‖² = 2T·(n+1)⁻¹  (对角 = 调和, 无 Stirling)
  rotating_integral_bound:  ‖∫e^{iΔt}‖ ≤ 2/|Δ|   (交叉上界原子)
  cross_energy_bound:       |∫v_m conj v_n| ≤ (√(m+1)√(n+1))⁻¹·2/|Δ|

诚实标注: 逐项三角不等式上界在相邻频率 (Δ≈0) 处过粗, 交叉相消
(振荡积分双和的精确估计) 是 Hardy–Littlewood 型分析 — 隐数坐标系
把交叉项写成旋转积分的精确形态 (已证), 但相消估计本身未形式化.

本图: 部分和能量的真实分解 ∫|S_N|² = 对角 + 交叉真实 (数值精确),
  展示"能量无界"机制 (对角调和发散主导) 的数值证据.
  v_n(t) = (n+1)^{-1/2}·e^{it·log(n+1)}
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

T = 50.0
Ns = list(range(10, 401, 10))

# 对角: 2T·Σ_{n<N}(n+1)⁻¹  (能量种子, 调和 — 已证 diagonal_energy)
diag = [2 * T * sum(1.0 / (n + 1) for n in range(N)) for N in Ns]

# 真实能量 ∫₀ᵀ|S_N|² = ΣΣ (√(mn))⁻¹ ∫₀ᵀe^{iΔt} (数值精确, 向量化)
def energy_exact(N, T):
    ns = np.arange(1, N + 1, dtype=float)
    logs = np.log(ns)
    D = logs[:, None] - logs[None, :]
    diagc = T / ns
    cross = ((np.exp(1j * D * T) - 1) / (1j * D)) / np.sqrt(ns[:, None] * ns[None, :])
    np.fill_diagonal(cross, 0)
    return float(diagc.sum() + cross.real.sum())
E = [energy_exact(N, T) for N in Ns]
cross_real = [e - d for e, d in zip(E, diag)]

fig, (a1, a2) = plt.subplots(1, 2, figsize=(13, 5.2))

# 左: 能量分解随 N (固定 T=50)
a1.plot(Ns, E, "b-o", ms=3, lw=1.5, label="真实能量 ∫|S_N|² (数值精确)")
a1.plot(Ns, diag, "g-", lw=2, label="对角 2T·Σ(n+1)⁻¹ (调和, Lean 已证)")
a1.plot(Ns, cross_real, "orange", lw=1.5, ls="--",
        label="交叉真实贡献 (E − 对角, 有相消)")
a1.axhline(0, color="k", lw=0.5)
a1.set_xlabel("N (部分和项数)"); a1.set_ylabel("能量")
a1.set_title(f"临界叶部分和能量 (T={T:.0f}):\n真实能量随 N 增长 (能量无界机制)")
a1.legend(fontsize=8); a1.grid(True, alpha=0.3)

# 右: 能量增长率 E(N)/log N → 2T? (对角主导检验)
ratio = [e / np.log(N) for e, N in zip(E, Ns)]
a2.plot(Ns, ratio, "b-o", ms=3, lw=1.5, label="E(N)/log N")
a2.axhline(2 * T, color="g", ls="--", lw=1.5,
           label=f"2T·(对角系数) = {2*T:.0f}")
a2.set_xlabel("N"); a2.set_ylabel("E/log N")
a2.set_title("增长率检验: E(N) ~ 2T·log N?\n(对角主导 ⟹ 比值 → 2T)")
a2.legend(fontsize=8); a2.grid(True, alpha=0.3)

fig.suptitle("fig13: 临界叶能量预算 — 旋转向量能量展开 (B 桥)\n"
             "Lean 已证原子: diagonal_energy / rotating_integral_bound / cross_energy_bound\n"
             "诚实边界: 交叉相消估计 (Hardy–Littlewood 型) 未形式化; 逐项上界在相邻频率过粗",
             fontsize=11.5)
fig.tight_layout(rect=[0, 0, 1, 0.88])
fig.savefig("viz/fig13_energy_budget.png", dpi=150)
plt.close(fig)

print(f"T={T}: N=400 时 对角={diag[-1]:.1f}, 交叉真实={cross_real[-1]:+.1f}, "
      f"E={E[-1]:.1f}")
print(f"E/log N (N=400): {E[-1]/np.log(400):.1f} vs 2T={2*T:.0f}")
print(f"fig13_energy_budget.png 已生成")
