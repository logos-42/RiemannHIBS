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

双语版: 设 FIG_LANG=en|zh (默认 zh) 生成 viz/fig14_en.png / viz/fig14_zh.png
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

LANG = os.environ.get("FIG_LANG", "zh")
if LANG not in ("en", "zh"):
    LANG = "zh"

T = {
    "zh": {
        # 左: 三态图例
        "l1": "σ=0.4 发散 (亚调和)",
        "l2": "σ=1/2 调和边界 (临界)",
        "l3": "σ=0.55 收敛 (超调和)",
        "l4": "σ=0.6 收敛 (超调和)",
        # 左: 轴与标题
        "x1": "N (项数)",
        "t1": "能量三态: 收敛 ⟺ σ > 1/2 (Lean 已证 energy_balance_radius)\n"
              "σ=1/2 是唯一平衡点 — 调和边界",
        # 右: 图例与标题
        "r1": "σ=1/2 (反射不动点)",
        "r2": "调和边界 log E(1/2)",
        "t2": "能量平衡点 = 反射不动点 σ=1/2\n"
              "(σ ↦ 1−σ 的不动点 ⟺ w ↦ e/w 的不动圆 |w|=√e)",
        # 总标题
        "sup": "fig14: 能量平衡半径 — 1/2 是能量唯一平衡点 (攻坚点 A 内禀骨架)\n"
               "Lean 已证: energy_balance_radius / energy_diverges_below_balance\n"
               "诚实边界: 平衡点给出半径唯一候选, 不单独推出零点在此 (RH 未证)",
        # 控制台输出
        "p1": "N=3000: E(σ=0.4)={v:.1f} (发散中)",
        "p2": "        E(σ=0.5)={v:.2f} (调和边界)",
        "p3": "        E(σ=0.6)={v:.3f} (收敛)",
        "saved": "{f} 已生成",
    },
    "en": {
        # Left: three-regime legend
        "l1": "σ=0.4 diverges (subharmonic)",
        "l2": "σ=1/2 harmonic boundary (critical)",
        "l3": "σ=0.55 converges (superharmonic)",
        "l4": "σ=0.6 converges (superharmonic)",
        # Left: axis & title
        "x1": "N (number of terms)",
        "t1": "Energy regimes: convergence ⟺ σ > 1/2 (Lean-proved energy_balance_radius)\n"
              "σ=1/2 is the unique balance point — harmonic boundary",
        # Right: legend & title
        "r1": "σ=1/2 (reflection fixed point)",
        "r2": "harmonic boundary log E(1/2)",
        "t2": "Energy balance point = reflection fixed point σ=1/2\n"
              "(fixed point of σ ↦ 1−σ ⟺ fixed circle of w ↦ e/w, |w|=√e)",
        # Figure suptitle
        "sup": "fig14: Energy balance radius — 1/2 is the unique energy balance point "
               "(intrinsic skeleton of Attack Point A)\n"
               "Lean-proved: energy_balance_radius / energy_diverges_below_balance\n"
               "Honest boundary: the balance point gives the unique radius candidate, "
               "but does not by itself place a zero there (RH unproved)",
        # Console output
        "p1": "N=3000: E(σ=0.4)={v:.1f} (diverging)",
        "p2": "        E(σ=0.5)={v:.2f} (harmonic boundary)",
        "p3": "        E(σ=0.6)={v:.3f} (converging)",
        "saved": "{f} saved",
    },
}

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
for σ, c, ls, lab in [(0.4, "red", "-", T[LANG]["l1"]),
                      (0.5, "green", "-", T[LANG]["l2"]),
                      (0.55, "blue", "-", T[LANG]["l3"]),
                      (0.6, "purple", "--", T[LANG]["l4"])]:
    E = np.cumsum((Ns + 1) ** (-2 * σ))
    a1.plot(Ns, E, c, lw=1.5, ls=ls, label=lab)
a1.axhline(0, color="k", lw=0.5)
a1.set_xlabel(T[LANG]["x1"]); a1.set_ylabel("E(σ;N) = Σ(n+1)^{-2σ}")
a1.set_title(T[LANG]["t1"])
a1.legend(fontsize=8); a1.grid(True, alpha=0.3)

# 右: 平衡点 = 反射不动点 σ=1/2 (机制图)
sigmas = np.linspace(0, 1, 200)
# 有限 N 下的对数能量增长率 (σ<1/2 时 →∞)
growth = [np.log(np.sum((np.arange(1, 3001) + 1) ** (-2 * s))) for s in sigmas]
a2.plot(sigmas, growth, "b-", lw=2, label="log E(σ;N=3000)")
a2.axvline(0.5, color="r", ls="--", lw=1.5, label=T[LANG]["r1"])
a2.axhline(np.log(np.sum((np.arange(1, 3001) + 1.0) ** (-1))),
           color="g", ls=":", lw=1, alpha=0.6, label=T[LANG]["r2"])
a2.set_xlabel("σ (Re s)"); a2.set_ylabel("log E(σ;N)")
a2.set_title(T[LANG]["t2"])
a2.legend(fontsize=8); a2.grid(True, alpha=0.3)

fig.suptitle(T[LANG]["sup"], fontsize=11.5)
fig.tight_layout(rect=[0, 0, 1, 0.88])

out_path = f"viz/fig14_{LANG}.png"
fig.savefig(out_path, dpi=150)
fig.savefig("viz/fig14_energy_balance.png", dpi=150)  # 向后兼容 (论文引用)
plt.close(fig)

# 数据
E05 = np.sum((np.arange(1, 3001) + 1.0) ** (-1))
print(T[LANG]["p1"].format(v=np.sum((np.arange(1, 3001) + 1.0) ** (-0.8))))
print(T[LANG]["p2"].format(v=E05))
print(T[LANG]["p3"].format(v=np.sum((np.arange(1, 3001) + 1.0) ** (-1.2))))
print(T[LANG]["saved"].format(f=out_path))
