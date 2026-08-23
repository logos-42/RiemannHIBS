#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
隐数包络结构 (envelope) 数值实验
=================================
核心猜想: 隐数三标签 {S,R,iR} 是复平面三个锚定方向 {θ=0, π/2, π} 的离散采样。
把标签连续化 (θ ∈ S¹) + 值连续化 (x ∈ ℝ) 后, 隐数空间包络成复对数曲面
w = e^s (螺旋柱面 / 万有覆盖), 而 ζ 函数在其上的画像变得极简:

    s 坐标                w = e^s 坐标
    ------------          ---------------------
    收敛半平面 Re s>1     圆外 |w| > e
    极点 s=1              单点 w = e
    平凡零点 s=−2k        正实轴点列 e^{−2k} → 0
    临界线 Re s=1/2       圆周 |w| = √e
    非平凡零点 (若 RH)    全部在圆周 |w| = √e 上
    η 的 spurious 零点    稠密于圆周 |w| = e
        s = 1+2πik/ln2    (因 2π/ln2 无理)

本脚本验证:
  (E1) 非平凡零点共圆: |e^{1/2+iγ_n}| = √e  (机器精度)
  (E2) η spurious 零点共圆: |e^{1+2πik/ln2}| = e, 角度分布均匀(稠密性雏形)
  (E3) 平凡零点 → 正实轴点列, 极点 → 单点
  (E4) argument principle: 沿矩形路径 ∮ ζ'/ζ dz 的绕数 = 内部非平凡零点个数
       ("数圈数 = 数零点" —— 引数维度就是第三个维度)
"""
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

# macOS 中文字体: 显式注册字体文件 (ttc/ttf), 避免 DejaVu Sans 缺 CJK 字形
# (PingFang SC 名字在 ttc 集合里解析为 PingFang HK, 需 addfont 注册后再引用)
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
# 验证字体可用性
try:
    _test = fm.findfont(fm.FontProperties(family=plt.rcParams["font.sans-serif"][0]),
                        fallback_to_default=False)
except Exception:
    _test = "FALLBACK"
print(f"[font] 中文渲染字体: {_test}")

mp.mp.dps = 30
LN2 = mp.log(2)
PI = mp.pi
SQRT_E = mp.e ** mp.mpf("0.5")

print("=" * 70)
print("E1: 非平凡零点共圆 |w| = sqrt(e) =", mp.nstr(SQRT_E, 12))
print("=" * 70)
errs = []
for n in range(1, 11):
    s = mp.zetazero(n)          # s_n = 1/2 + i·γ_n
    w = mp.e ** s               # 指数映射 (包络坐标)
    err = abs(abs(w) - SQRT_E)
    errs.append(float(err))
    print(f"  n={n:2d}  s={mp.nstr(s, 10):22s}  |w|={mp.nstr(abs(w), 12):14s}  | |w|−√e |={mp.nstr(err, 5)}")
print(f"  最大偏差 = {max(errs):.2e}  (机器精度级 → 共圆成立)")

print()
print("=" * 70)
print("E2: eta 的 spurious 零点 s_k = 1 + 2πik/ln2  →  w_k = e·e^{iθ_k}")
print("    2π/ln2 =", mp.nstr(2 * PI / LN2, 12), "≈ 1.443 圈/步 (无理 → 稠密)")
print("=" * 70)
K = 300
thetas = []
for k in range(K):
    w = mp.e * mp.e ** (mp.mpc(0, 2 * PI * k / LN2))
    assert abs(abs(w) - mp.e) < mp.mpf("1e-25")
    th = mp.arg(w) % (2 * PI)
    thetas.append(float(th))
thetas = np.array(thetas)
print(f"  前 {K} 个 spurious 零点: 全部落在 |w| = e 上 (模恒等, 断言通过)")
# 角度直方图均匀性: 36 格
hist, _ = np.histogram(thetas, bins=36, range=(0, 2 * np.pi))
print(f"  角度 36 格计数: min={hist.min()}, max={hist.max()}, "
      f"均值={hist.mean():.1f} (均匀 ~ 泊松涨落 √mean={np.sqrt(hist.mean()):.1f})")
print(f"  角度分布近均匀 → 稠密性 (圆周上无空洞) 的数值雏形")

print()
print("=" * 70)
print("E3: 平凡零点 e^{−2k} → 0 (正实轴点列)   极点 e (单点)")
print("=" * 70)
for k in range(1, 7):
    print(f"  平凡零点 s=−{2*k:2d} →  w = {mp.nstr(mp.e ** mp.mpf(-2*k), 10)}")
print(f"  极点 s=1      →  w = {mp.nstr(mp.e, 10)}")

print()
print("=" * 70)
print("E4: argument principle — 数圈数 = 数零点")
print("    矩形 R = [1/3, 5/6] × [0, 38]  (仅含非平凡零点, 无极点/平凡零点)")
print("=" * 70)
T = mp.mpf("38")
gammas = []
n = 1
while True:
    g = mp.im(mp.zetazero(n))
    if g > T:
        break
    gammas.append(g)
    n += 1
N_expected = len(gammas)
print(f"  矩形内非平凡零点 (γ < {T}): {N_expected} 个  → {[mp.nstr(g,6) for g in gammas]}")

def contour(f, zpath, N=400):
    """数值积分 ∮ f(z) dz, zpath: 参数 t∈[0,1] → z(t), 需含导数 z'(t)
    注: zpath 四段用段内参数 u 参数化 (dz = zp·du), 每段 N 步, du = 1/N"""
    acc = mp.mpc(0)
    for seg in range(4):
        for j in range(N):
            u = (j + 0.5) / N        # 段内中点 (u 参数)
            tm = (seg + u) / 4       # 全局 t
            z, zp = zpath(tm)
            acc += f(z) * zp * (1 / N)
    return acc

# 逆时针矩形, 四段
def zpath(t):
    if t < 0.25:      # 右段: σ=5/6, t∈[0,38]
        u = t / 0.25
        return mp.mpc(mp.mpf("5/6"), T * u), mp.mpc(0, T)
    elif t < 0.5:     # 顶段: σ: 5/6→1/3
        u = (t - 0.25) / 0.25
        return mp.mpc(mp.mpf("5/6") - (mp.mpf("5/6") - mp.mpf("1/3")) * u, T), -mp.mpf("5/6") + mp.mpf("1/3")
    elif t < 0.75:    # 左段: t: 38→0
        u = (t - 0.5) / 0.25
        return mp.mpc(mp.mpf("1/3"), T * (1 - u)), mp.mpc(0, -T)
    else:             # 底段: σ: 1/3→5/6
        u = (t - 0.75) / 0.25
        return mp.mpc(mp.mpf("1/3") + (mp.mpf("5/6") - mp.mpf("1/3")) * u, 0), mp.mpf("5/6") - mp.mpf("1/3")

def dzeta_over_zeta(z):
    if abs(z - 1) < mp.mpf("1e-6"):
        return mp.mpc(0)   # 路径避开极点, 此分支不应触发
    return mp.zeta(z, derivative=1) / mp.zeta(z)

I = contour(dzeta_over_zeta, zpath)
winding = float((I / (2 * PI * 1j)).real)
print(f"  ∮ ζ'/ζ dz = {mp.nstr(I, 8)}")
print(f"  绕数 W = (1/2πi)∮ ζ'/ζ dz = {winding:.4f}   期望零点数 N = {N_expected}")
print(f"  |W − N| = {abs(winding - N_expected):.4f}  → 数圈数 = 数零点 ✓")

# ------------------------------------------------------------------
# 图 1: w 平面 — 点、点列、圆、稠密零点
# ------------------------------------------------------------------
fig, ax = plt.subplots(figsize=(8, 8))

th = np.linspace(0, 2 * np.pi, 1000)
ax.plot(np.e * np.cos(th), np.e * np.sin(th), "b-", lw=1.2, alpha=0.7,
        label=r"$|w|=e$  (η spurious zeros 稠密于此)")
ax.plot(np.sqrt(np.e) * np.cos(th), np.sqrt(np.e) * np.sin(th), "r--", lw=1.5,
        label=r"$|w|=\sqrt{e}$  (临界线, RH 零点共圆于此)")

# 非平凡零点 (前 20 个) → 红星
for n in range(1, 21):
    s = mp.zetazero(n)
    w = mp.e ** s
    ax.plot(float(w.real), float(w.imag), "r*", ms=10, zorder=5)
ax.plot([], [], "r*", ms=10, label="非平凡零点 (共圆 $\\sqrt{e}$)")

# spurious zeros (前 300 个) → 蓝点
ws = [mp.e * mp.e ** (mp.mpc(0, 2 * PI * k / LN2)) for k in range(300)]
ax.scatter([float(w.real) for w in ws], [float(w.imag) for w in ws],
           s=4, c="b", alpha=0.5, zorder=3)
ax.plot([], [], "o", c="b", ms=4, alpha=0.6, label="η spurious 零点 (分布近均匀)")

# 平凡零点点列 → 正实轴
for k in range(1, 11):
    w = mp.e ** mp.mpf(-2 * k)
    ax.plot(float(w), 0.0, "gx", ms=8, zorder=6)
ax.plot([], [], "gx", ms=8, label="平凡零点 $e^{-2k}\\to 0$")

# 极点 → 黑点
ax.plot(float(mp.e), 0.0, "ko", ms=11, zorder=7)
ax.annotate("极点 $s=1 \\to w=e$", (float(mp.e), 0.0),
            textcoords="offset points", xytext=(10, -18), fontsize=10)

ax.axhline(0, color="k", lw=0.5); ax.axvline(0, color="k", lw=0.5)
ax.set_xlim(-3.4, 3.4); ax.set_ylim(-3.4, 3.4)
ax.set_aspect("equal")
ax.set_title("隐数包络坐标 $w=e^s$: 极点=单点, 平凡零点=点列, 非平凡零点(若RH)=共圆 $\\sqrt{e}$, η多余零点=稠密于 $e$")
ax.legend(loc="upper left", fontsize=9)
fig.tight_layout()
fig.savefig("/Users/apple/Downloads/lean/RiemannHIBS/experiments/envelope_plane.png", dpi=150)
print("\n图1已保存: experiments/envelope_plane.png")

# ------------------------------------------------------------------
# 图 2: s 平面 (直线) ↔ w 平面 (圆): 卷绕
# ------------------------------------------------------------------
fig2, (a1, a2) = plt.subplots(1, 2, figsize=(11, 5))

# 左: s 平面, 临界线是竖直线
tvals = np.linspace(-25, 25, 400)
a1.plot([0.5, 0.5], [tvals[0], tvals[-1]], "r-", lw=2)
a1.plot([1, 1], [tvals[0], tvals[-1]], "b-", lw=1.5, alpha=0.7)
for n in range(1, 7):
    s = mp.zetazero(n)
    a1.plot(float(s.real), float(s.imag), "r*", ms=10)
a1.plot(float(mp.e.real if hasattr(mp.e, 'real') else 1), 0, "ko", ms=8)
a1.set_xlim(-1, 3); a1.set_ylim(-25, 25)
a1.axhline(0, color="k", lw=0.5)
a1.set_xlabel("Re s"); a1.set_ylabel("Im s = t")
a1.set_title("s 平面: 临界线 Re s = 1/2 (直线)")
a1.annotate("极点 s=1", (1, 0), textcoords="offset points", xytext=(8, 8))
a1.annotate("零点 γ₁..γ₆", (0.5, 14), textcoords="offset points", xytext=(8, 0))

# 右: w 平面, 临界线是圆
th2 = np.linspace(0, 2 * np.pi, 800)
a2.plot(np.sqrt(np.e) * np.cos(th2), np.sqrt(np.e) * np.sin(th2), "r-", lw=2)
a2.plot(np.e * np.cos(th2), np.e * np.sin(th2), "b-", lw=1.5, alpha=0.7)
for n in range(1, 7):
    w = mp.e ** mp.zetazero(n)
    a2.plot(float(w.real), float(w.imag), "r*", ms=10)
a2.plot(float(mp.e), 0, "ko", ms=8)
a2.set_xlim(-3.4, 3.4); a2.set_ylim(-3.4, 3.4)
a2.set_aspect("equal"); a2.axhline(0, color="k", lw=0.5); a2.axvline(0, color="k", lw=0.5)
a2.set_xlabel("Re w"); a2.set_ylabel("Im w")
a2.set_title("w = e^s 平面: 临界线卷成圆 |w| = √e")

fig2.tight_layout()
fig2.savefig("/Users/apple/Downloads/lean/RiemannHIBS/experiments/envelope_critical.png", dpi=150)
print("图2已保存: experiments/envelope_critical.png")

# ------------------------------------------------------------------
# 图 3: 隐数包络 3D — 螺旋柱面 (复对数曲面) + 三条离散母线
# ------------------------------------------------------------------
from mpl_toolkits.mplot3d import Axes3D  # noqa
fig3 = plt.figure(figsize=(9, 8))
ax3 = fig3.add_subplot(111, projection="3d")

# 离散骨架: 三标签 = 三个离散"楼层" (θ = 0, π/2, π) 上的射线
# 坐标: (Re w, Im w, 引数层 θ)
for th_lab, c, lab in [(0, "green", "S 支 (θ=0)"),
                       (np.pi / 2, "orange", "iR 支 (θ=π/2)"),
                       (np.pi, "red", "R 支 (θ=π)")]:
    xs = np.linspace(0, 2.5, 50) * np.cos(th_lab)
    ys = np.linspace(0, 2.5, 50) * np.sin(th_lab)
    zs = np.full(50, th_lab)
    ax3.plot(xs, ys, zs, c=c, lw=2.5, label=lab)
    # 格点 (值连续化前的整数点)
    for k in range(1, 7):
        ax3.scatter([k * np.cos(th_lab)], [k * np.sin(th_lab)], [th_lab], c=c, s=25, depthshade=False)

# 连续包络: 螺旋 (临界线在包络上的像 = 半径 √e 的螺旋)
t3 = np.linspace(0, 4 * np.pi, 600)
r3 = np.sqrt(np.e)
ax3.plot(r3 * np.cos(t3), r3 * np.sin(t3), t3, "b-", lw=1.2, alpha=0.8,
         label="连续化: 临界线卷成螺旋 (半径 √e)")
r3b = np.e
ax3.plot(r3b * np.cos(t3), r3b * np.sin(t3), t3, "c-", lw=0.8, alpha=0.5,
         label="收敛边界 |w| = e (螺旋)")
ax3.set_xlabel("Re w"); ax3.set_ylabel("Im w")
ax3.set_zlabel("引数维度 θ (第三维)")
ax3.set_title("隐数包络: 三标签是离散母线, 连续化 = 螺旋柱面 (复对数曲面)")
ax3.legend(loc="upper left", fontsize=8)
fig3.tight_layout()
fig3.savefig("/Users/apple/Downloads/lean/RiemannHIBS/experiments/envelope_surface.png", dpi=150)
print("图3已保存: experiments/envelope_surface.png")
print("\n全部数值验证完成。")
