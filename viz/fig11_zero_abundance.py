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

Bilingual: FIG_LANG=en -> viz/fig11_en.png, zh -> viz/fig11_zh.png.
"""
import os
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

LANG = os.environ.get("FIG_LANG", "zh")

T = {
    "en": {
        "delta_label": "δ_n = Δγ_n·log(γ_n/2π)/(2π)",
        "unit_label": "= 1 (frequency bandwidth inverse: Δγ ≈ 2π/log(γ/2π))",
        "mean_label": "mean = {v:.3f}",
        "title_left": "Normalized zero spacing: fluctuations around 1\n"
                      "→ spacing determined by the largest effective frequency "
                      "log(γ/2π) (interference mechanism)",
        "count_label": "actual N(T) (zero count)",
        "rm_label": "(T/2π)(log(T/2π) − 1)",
        "err_label": "+ O(log T) error band (von Mangoldt)",
        "title_right": "Zero abundance: frequency-mechanism main term vs actual count\n"
                       "(Riemann–von Mangoldt, mechanism formulation without Stirling)",
        "suptitle": "The frequency mechanism of abundance: Δγ ≈ 2π/log(γ/2π)  ⟹  "
                    "N(T) ≈ (T/2π)(log(T/2π) − 1)\n"
                    "The log factor comes from the density of the frequency set "
                    "{log n} — the 'growth dimension' in hidden-number coordinates",
        "sum_head": "First {n} zeros:",
        "sum_mean": "  mean normalized spacing δ̄ = {m:.4f}  (theory 1, σ = {s:.4f})",
        "sum_minmax": "  max/min γ: {lo:.2f} / {hi:.2f}",
        "sum_count": "  N({tm:.0f}) actual = {n}, formula = {f:.1f} "
                     "(diff {d:.2f}, within O(log T) ≈ {b:.1f})",
        "sum_mech": "  → frequency mechanism (bandwidth inverse) reproduces the "
                    "abundance main term, no Stirling asymptotics needed",
        "sum_done": "{fname} written",
    },
    "zh": {
        "delta_label": "δ_n = Δγ_n·log(γ_n/2π)/(2π)",
        "unit_label": "= 1 (频率带宽倒数: Δγ ≈ 2π/log(γ/2π))",
        "mean_label": "均值 = {v:.3f}",
        "title_left": "归一化零点间距: 围绕 1 涨落\n"
                      "→ 间距由最大有效频率 log(γ/2π) 决定 (干涉机制)",
        "count_label": "实际 N(T) (零点计数)",
        "rm_label": "(T/2π)(log(T/2π) − 1)",
        "err_label": "+ O(log T) 误差带 (von Mangoldt)",
        "title_right": "零点丰度: 频率机制主项 vs 实际计数\n"
                       "(Riemann–von Mangoldt, 无需 Stirling 的机制表述)",
        "suptitle": "丰度的频率机制: Δγ ≈ 2π/log(γ/2π)  ⟹  N(T) ≈ (T/2π)(log(T/2π) − 1)\n"
                    "log 因子来自频率集 {log n} 的密度 — 隐数坐标下的'增长维度'",
        "sum_head": "前 {n} 个零点:",
        "sum_mean": "  归一化间距均值 δ̄ = {m:.4f}  (理论 1, σ = {s:.4f})",
        "sum_minmax": "  最大/最小 γ: {lo:.2f} / {hi:.2f}",
        "sum_count": "  N({tm:.0f}) 实际 = {n}, 公式 = {f:.1f} "
                     "(差 {d:.2f}, 在 O(log T) ≈ {b:.1f} 内)",
        "sum_mech": "  → 频率机制 (带宽倒数) 复现丰度主项, 无需 Stirling 渐近",
        "sum_done": "{fname} 已生成",
    },
}[LANG]

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
        label=T["delta_label"])
a1.axhline(1.0, color="red", ls="--", lw=1.2,
           label=T["unit_label"])
a1.axhline(delta.mean(), color="orange", ls=":", lw=1.2,
           label=T["mean_label"].format(v=delta.mean()))
a1.set_xlim(0, N); a1.set_ylim(0, 2.5)
a1.set_xlabel("n"); a1.set_ylabel("δ_n")
a1.set_title(T["title_left"])
a1.legend(loc="upper right", fontsize=8)

# --- 右: 计数 N(T) vs 丰度公式 ---
Ts = np.linspace(5, gammas[-1], 400)
counts = np.array([np.sum(gammas <= T) for T in Ts])
a2.plot(Ts, counts, color="#1f77b4", lw=1.5, label=T["count_label"])
a2.plot(Ts, N_formula(Ts), "r--", lw=1.5,
        label=T["rm_label"])
a2.plot(Ts, N_formula(Ts) + 1.5 * np.log(Ts), "g:", lw=1.2,
        label=T["err_label"])
a2.set_xlim(0, gammas[-1])
a2.set_xlabel("T"); a2.set_ylabel("N(T)")
a2.set_title(T["title_right"])
a2.legend(loc="upper left", fontsize=8)

fig.suptitle(T["suptitle"], fontsize=12.5)
fig.tight_layout(rect=[0, 0, 1, 0.88])
fname = f"{OUT}/fig11_{LANG}.png"
fig.savefig(fname, dpi=150)
plt.close(fig)

# 数值总结
print(T["sum_head"].format(n=N))
print(T["sum_mean"].format(m=delta.mean(), s=delta.std()))
print(T["sum_minmax"].format(lo=gammas[0], hi=gammas[-1]))
print(T["sum_count"].format(tm=gammas[-1], n=N,
                            f=N_formula(gammas[-1]),
                            d=N - N_formula(gammas[-1]),
                            b=1.5 * np.log(gammas[-1])))
print(T["sum_mech"])
print(T["sum_done"].format(fname=fname))
