#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig11: 零点丰度的频率机制 — 隐数坐标下的 Weyl 律
================================================
机制假设: 零点是频率集 {log n} 的干涉图样.
  - 第 n 个自然数 = 角速度 log n 的旋转向量 (对方 §17 已形式化)
  - 有效频率带宽 ~ (1/2)log(t/2π) (Riemann–Siegel 截断 n ≤ √(t/2π))
  - 干涉间距(不确定性原理型) Δγ ~ 2π/带宽 ⟹ 丰度 N(T) ~ (1/2π)∫log(t/2π)dt
    = (T/2π)(log(T/2π) − 1)  — Riemann–von Mangoldt 主项!
检验:
  1. 归一化间距 δ_n := Δγ_n·log(γ_n/2π)/(2π) 的均值 → 1? (频率带宽倒数)
  2. 计数 N(T) vs (T/2π)(log(T/2π) − 1) 的逼近
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
mp.mp.dps = 12
N = 400

gammas = np.array([float(mp.im(mp.zetazero(n))) for n in range(1, N + 1)])

# 1) 归一化间距: δ_n = Δγ_n · log(γ_n/2π) / (2π)
gaps = np.diff(gammas)
mid = gammas[:-1] + gaps / 2
delta = gaps * np.log(mid / (2 * np.pi)) / (2 * np.pi)

# 2) 计数公式: N(T) ≈ (T/2π)(log(T/2π) − 1)
def N_formula(T):
    return (T / (2 * np.pi)) * (np.log(T / (2 * np.pi)) - 1)

fig, (a1, a2) = plt.subplots(1, 2, figsize=(13, 5.2))

# --- 左: 归一化间距 δ_n (频率带宽倒数机制) ---
a1.plot(np.arange(1, N), delta, color="#1f77b4", lw=0.8,
        label="δ_n = Δγ_n·log(γ_n/2π)/(2π)")
a1.axhline(1.0, color="red", ls="--", lw=1.2,
           label="= 1 (频率带宽倒数: Δγ ≈ 2π/log(γ/2π))")
a1.axhline(delta.mean(), color="orange", ls=":", lw=1.2,
           label=f"均值 = {delta.mean():.3f}")
a1.set_xlim(0, N); a1.set_ylim(0, 2.5)
a1.set_xlabel("n"); a1.set_ylabel("δ_n")
a1.set_title("归一化零点间距: 围绕 1 涨落\n"
             "→ 间距由最大有效频率 log(γ/2π) 决定 (干涉机制)")
a1.legend(loc="upper right", fontsize=8)

# --- 右: 计数 N(T) vs 丰度公式 ---
Ts = np.linspace(5, gammas[-1], 400)
counts = np.array([np.sum(gammas <= T) for T in Ts])
a2.plot(Ts, counts, color="#1f77b4", lw=1.5, label="实际 N(T) (零点计数)")
a2.plot(Ts, N_formula(Ts), "r--", lw=1.5,
        label="(T/2π)(log(T/2π) − 1)")
a2.plot(Ts, N_formula(Ts) + 1.5 * np.log(Ts), "g:", lw=1.2,
        label="+ O(log T) 误差带 (von Mangoldt)")
a2.set_xlim(0, gammas[-1])
a2.set_xlabel("T"); a2.set_ylabel("N(T)")
a2.set_title("零点丰度: 频率机制主项 vs 实际计数\n"
             "(Riemann–von Mangoldt, 无需 Stirling 的机制表述)")
a2.legend(loc="upper left", fontsize=8)

fig.suptitle("丰度的频率机制: Δγ ≈ 2π/log(γ/2π)  ⟹  N(T) ≈ (T/2π)(log(T/2π) − 1)\n"
             "log 因子来自频率集 {log n} 的密度 — 隐数坐标下的'增长维度'",
             fontsize=12.5)
fig.tight_layout(rect=[0, 0, 1, 0.88])
fig.savefig(f"{OUT}/fig11_zero_abundance.png", dpi=150)
plt.close(fig)

# 数值总结
print(f"前 {N} 个零点:")
print(f"  归一化间距均值 δ̄ = {delta.mean():.4f}  (理论 1, σ = {delta.std():.4f})")
print(f"  最大/最小 γ: {gammas[0]:.2f} / {gammas[-1]:.2f}")
print(f"  N({gammas[-1]:.0f}) 实际 = {N}, 公式 = {N_formula(gammas[-1]):.1f} "
      f"(差 {N - N_formula(gammas[-1]):.2f}, 在 O(log T) ≈ {1.5*np.log(gammas[-1]):.1f} 内)")
print(f"  → 频率机制 (带宽倒数) 复现丰度主项, 无需 Stirling 渐近")
print("fig11_zero_abundance.png 已生成")
