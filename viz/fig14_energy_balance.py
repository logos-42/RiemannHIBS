#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig14: 能量平衡半径 — 1/2 是能量的唯一平衡点 (攻坚点 A 内禀骨架)
================================================================
Lean 已证 (Abundance.lean §12):
  energy_balance_radius:       Σ(n+1)^{-2σ} 收敛 ⟺ σ > 1/2
  energy_diverges_below_balance: σ ≤ 1/2 ⟹ 能量发散
  结合: 反射 σ↦1−σ ⟺ w↦e/w (Analytic §14.5), 不动点 σ=1/2 ⟺ |w|=√e

本图: 对角能量 E(σ;N) = Σ_{n<N}(n+1)^{-2σ} 的三态行为
  σ > 1/2: 超调和收敛 (能量预算有限)
  σ = 1/2: 调和边界 (恰好临界 — 能量种子, B 桥)
  σ < 1/2: 亚调和发散 (能量预算爆炸)
⟹ 1/2 是能量的唯一平衡点 — "为什么临界线是 1/2"的能量版本
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

fig, (a1, a2) = plt.subplots(1, 2, figsize=(13, 5.2))

# 左: E(σ;N) = Σ(n+1)^{-2σ} 随 N (三态)
Ns = np.arange(1, 3001)
for σ, c, ls, lab in [(0.4, "red", "-", "σ=0.4 发散 (亚调和)"),
                      (0.5, "green", "-", "σ=1/2 调和边界 (临界)"),
                      (0.55, "blue", "-", "σ=0.55 收敛 (超调和)"),
                      (0.6, "purple", "--", "σ=0.6 收敛 (超调和)")]:
    E = np.cumsum((Ns + 1) ** (-2 * σ))
    a1.plot(Ns, E, c, lw=1.5, ls=ls, label=lab)
a1.axhline(0, color="k", lw=0.5)
a1.set_xlabel("N (项数)"); a1.set_ylabel("E(σ;N) = Σ(n+1)^{-2σ}")
a1.set_title("能量三态: 收敛 ⟺ σ > 1/2 (Lean 已证 energy_balance_radius)\n"
             "σ=1/2 是唯一平衡点 — 调和边界")
a1.legend(fontsize=8); a1.grid(True, alpha=0.3)

# 右: 平衡点 = 反射不动点 σ=1/2 (机制图)
sigmas = np.linspace(0, 1, 200)
# 有限 N 下的对数能量增长率 (σ<1/2 时 →∞)
growth = [np.log(np.sum((np.arange(1, 3001) + 1) ** (-2 * s))) for s in sigmas]
a2.plot(sigmas, growth, "b-", lw=2, label="log E(σ;N=3000)")
a2.axvline(0.5, color="r", ls="--", lw=1.5, label="σ=1/2 (反射不动点)")
a2.axhline(np.log(np.sum((np.arange(1, 3001) + 1.0) ** (-1))),
           color="g", ls=":", lw=1, alpha=0.6, label="调和边界 log E(1/2)")
a2.set_xlabel("σ (Re s)"); a2.set_ylabel("log E(σ;N)")
a2.set_title("能量平衡点 = 反射不动点 σ=1/2\n"
             "(σ ↦ 1−σ 的不动点 ⟺ w ↦ e/w 的不动圆 |w|=√e)")
a2.legend(fontsize=8); a2.grid(True, alpha=0.3)

fig.suptitle("fig14: 能量平衡半径 — 1/2 是能量唯一平衡点 (攻坚点 A 内禀骨架)\n"
             "Lean 已证: energy_balance_radius / energy_diverges_below_balance\n"
             "诚实边界: 平衡点给出半径唯一候选, 不单独推出零点在此 (RH 未证)",
             fontsize=11.5)
fig.tight_layout(rect=[0, 0, 1, 0.88])
fig.savefig("viz/fig14_energy_balance.png", dpi=150)
plt.close(fig)

# 数据
E05 = np.sum((np.arange(1, 3001) + 1.0) ** (-1))
print(f"N=3000: E(σ=0.4)={np.sum((np.arange(1,3001)+1.0)**(-0.8)):.1f} (发散中)")
print(f"        E(σ=0.5)={E05:.2f} (调和边界)")
print(f"        E(σ=0.6)={np.sum((np.arange(1,3001)+1.0)**(-1.2)):.3f} (收敛)")
print(f"fig14_energy_balance.png 已生成")
