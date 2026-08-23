#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig10: 零点 = 自然数频率的振动干涉
==================================
猜想一翻译: ζ(s) = Σ n^{-s}, 每项 n^{-it} = e^{-it·log n} 是以频率 log n
旋转的振动 → ζ 在临界线 = 频率集 {log n} 的干涉叠加, 零点 = 干涉零点.

展示:
  左: Hardy Z(t) (实值振动, 零点 = 过零)  +  Riemann-Siegel θ 的旋转因子
  中: ζ(1/2+it) 实部/虚部 (在实数域和虚数域之间跳动)
  右: ζ(1/2+it) 复平面轨迹 (旋转运动; 相邻零点间相位转 2π)
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
mp.mp.dps = 15
N_ZEROS = 6
gammas = [float(mp.im(mp.zetazero(n))) for n in range(1, N_ZEROS + 1)]

# ζ(1/2+it) 的采样
ts = np.linspace(0.0, 45.0, 3000)
zs = np.array([complex(mp.zeta(mp.mpc(0.5, t))) for t in ts])
Z = np.array([float(mp.siegelz(t)) for t in ts])          # Hardy Z (实值)

fig = plt.figure(figsize=(15, 4.9))

# ---- 左: Hardy Z(t) ----
a1 = fig.add_subplot(1, 3, 1)
a1.plot(ts, Z, color="#1f77b4", lw=1.0, label="Z(t) = e^{iθ(t)}·ζ(1/2+it)  (实值)")
for g in gammas:
    a1.axvline(g, color="red", lw=0.8, alpha=0.7)
    a1.plot(g, 0, "r*", ms=11)
a1.axhline(0, color="k", lw=0.7)
a1.set_xlim(0, 45); a1.set_ylim(-6, 6)
a1.set_xlabel("t"); a1.set_ylabel("Z(t)")
a1.set_title("Hardy Z(t): 实值振动\n零点 = 过零 (红星 γ₁..γ₆)")
a1.legend(loc="upper left", fontsize=8)

# ---- 中: 实部/虚部 ----
a2 = fig.add_subplot(1, 3, 2)
a2.plot(ts, zs.real, color="#1f77b4", lw=0.8, label="Re ζ(1/2+it)")
a2.plot(ts, zs.imag, color="#ff7f0e", lw=0.8, label="Im ζ(1/2+it)")
for g in gammas:
    a2.axvline(g, color="red", lw=0.8, alpha=0.7)
a2.axhline(0, color="k", lw=0.6)
a2.set_xlim(0, 45); a2.set_ylim(-4, 4)
a2.set_xlabel("t")
a2.set_title("实部/虚部: 在实数域和虚数域\n之间来回跳动, 零点处同时为零")
a2.legend(loc="upper left", fontsize=8)

# ---- 右: 复平面轨迹 ----
a3 = fig.add_subplot(1, 3, 3)
a3.plot(zs.real, zs.imag, color="purple", lw=0.9, alpha=0.9,
        label="ζ(1/2+it), t ∈ [0, 45]")
a3.plot(0, 0, "ko", ms=5)
a3.annotate("原点: 每个零点处轨迹穿过", (0, 0),
            textcoords="offset points", xytext=(8, -24), fontsize=8)
for g in gammas:
    w = complex(mp.zeta(mp.mpc(0.5, g)))
    a3.plot(w.real, w.imag, "r*", ms=11)
a3.axhline(0, color="k", lw=0.4); a3.axvline(0, color="k", lw=0.4)
a3.set_xlim(-4, 4); a3.set_ylim(-4, 4)
a3.set_aspect("equal")
a3.set_xlabel("Re ζ"); a3.set_ylabel("Im ζ")
a3.set_title("复平面轨迹: 旋转运动\n(相位连续缠绕, 零点处穿过原点)")
a3.legend(loc="upper left", fontsize=8)

fig.suptitle("零点 = 自然数频率 {log n} 的干涉: ζ(1/2+it) = Σ n^{-1/2}·e^{-it·log n}\n"
             "实振动 (Z) × 旋转因子 (e^{-iθ}) — 零点 = 干涉图样的零振幅点",
             fontsize=12.5)
fig.tight_layout(rect=[0, 0, 1, 0.88])
fig.savefig(f"{OUT}/fig10_zero_vibration.png", dpi=150)
plt.close(fig)

# ---- 附加: 频率 {log n} 的干涉重建 Z(t) ----
# Riemann-Siegel 主项: Z(t) ≈ 2Σ_{n≤√(t/2π)} n^{-1/2} cos(θ(t) - t·log n)
print("频率干涉重建 (Riemann-Siegel 主项):")
for Nt in [2, 5, 10]:
    t0 = 30.0
    theta = float(mp.siegeltheta(t0))
    S = 0.0
    for n in range(1, Nt + 1):
        S += np.cos(theta - t0 * np.log(n)) / np.sqrt(n)
    print(f"  t=30: 前 {Nt:2d} 项部分和 = {2*S:+.4f}   精确 Z(30) = {float(mp.siegelz(30)):+.4f}")
print("→ Z 由频率 {log n} 的余弦叠加逼近 — '自然数旋转'的精确含义")
print("fig10_zero_vibration.png 已生成")
