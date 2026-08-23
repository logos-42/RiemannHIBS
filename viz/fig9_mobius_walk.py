#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig9: Möbius 随机行走 — 零点产生机制的候选直觉
============================================
机制性理解: 1/ζ(s) = Σ μ(n)/n^s (Möbius 反演, Re s>1).
零点 = 1/ζ 的极点. 在临界带内, μ 符号的"类随机翻转"决定 1/ζ 的行为.
已知等价:  RH ⟺ M(x) := Σ_{n≤x} μ(n) = O(x^{1/2+ε})  (任意 ε>0).
所以"零点为什么在临界线上"可翻译为"μ 的符号翻转为什么被平方根界控制".
本图: M(x) 的随机行走 (前 10^5 项) + ±√x 边界 (RH 的界) + 已知反例区
(Mertens 猜想 |M(x)|<√x 被 Odlyzko–te Riele 1985 证伪).
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

OUT = "viz"
N = 100_000

# 莫比乌斯函数 (线性筛)
mu = np.zeros(N + 1, dtype=int)
mu[1] = 1
is_prime = np.ones(N + 1, dtype=bool)
primes = []
for i in range(2, N + 1):
    if is_prime[i]:
        primes.append(i)
        mu[i] = -1
    for p in primes:
        if i * p > N:
            break
        is_prime[i * p] = False
        if i % p == 0:
            mu[i * p] = 0
            break
        else:
            mu[i * p] = -mu[i]

M = np.cumsum(mu[1:])          # M(x) = Σ_{n≤x} μ(n), x = 1..N
x = np.arange(1, N + 1)

fig, (a1, a2) = plt.subplots(1, 2, figsize=(13, 5.2))

# --- 左: Mertens 函数随机行走 ---
a1.plot(x, M, color="#1f77b4", lw=0.7)
a1.plot(x, np.sqrt(x), "r--", lw=1.2, label=r"$+\sqrt{x}$ (RH 的界)")
a1.plot(x, -np.sqrt(x), "r--", lw=1.2, label=r"$-\sqrt{x}$")
a1.axhline(0, color="k", lw=0.6)
a1.set_xlim(0, N); a1.set_ylim(-120, 120)
a1.set_xlabel("x"); a1.set_ylabel("M(x) = Σ μ(n)")
a1.set_title("Mertens 函数 M(x): μ 的符号翻转 = 随机行走\n"
             "RH ⟺ M(x) = O(x^{1/2+ε})")
a1.legend(loc="upper left", fontsize=9)

# --- 右: 局部放大 (前 3000 项, 看涨落结构) ---
N2 = 3000
a2.plot(x[:N2], M[:N2], color="#1f77b4", lw=0.8)
a2.plot(x[:N2], np.sqrt(x[:N2]), "r--", lw=1.0, alpha=0.8)
a2.plot(x[:N2], -np.sqrt(x[:N2]), "r--", lw=1.0, alpha=0.8)
a2.axhline(0, color="k", lw=0.6)
a2.set_xlim(0, N2); a2.set_ylim(-60, 60)
a2.set_xlabel("x"); a2.set_ylabel("M(x)")
a2.set_title("局部放大: 涨落被 √x 夹住 (数值)\n"
             "Mertens 猜想 |M(x)|<√x 已被证伪 (1985)")

fig.suptitle("零点产生机制: 1/ζ(s) = Σ μ(n)/n^s — 零点是 μ 随机翻转的干涉产物;\n"
             "全称性控制 (所有零点在临界线) ⟺ M(x) 的平方根界 (= RH)", fontsize=12.5)
fig.tight_layout(rect=[0, 0, 1, 0.9])
fig.savefig(f"{OUT}/fig9_mobius_walk.png", dpi=150)
plt.close(fig)

# 数据点
mx = M[-1]
print(f"M({N}) = {mx}   (√N = {np.sqrt(N):.1f}, 比值 {abs(mx)/np.sqrt(N):.3f})")
rec = np.abs(M).max()
print(f"前 {N} 项 |M(x)| 最大值 = {rec}, 对应 √x = {np.sqrt(np.argmax(np.abs(M))+1):.1f}")
print(f"fig9_mobius_walk.png 已生成")
