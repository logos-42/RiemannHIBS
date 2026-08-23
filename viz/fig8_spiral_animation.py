#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fig8: 零点螺旋动画 — 亮点沿半径 √e 的螺旋爬升 (临界线像),
      投影在圆 |w|=√e 上绕圈; 经过零点 γ₁..γ₆ 时高亮.
      回答: "圆展开成螺旋, 零点在螺旋上" 的动态演示.
"""
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
from matplotlib.animation import FuncAnimation, PillowWriter
from mpl_toolkits.mplot3d import Axes3D  # noqa

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
SQRT_E = float(np.e) ** 0.5
N_ZEROS = 6
T_MAX = 40.0          # 覆盖 γ₆ ≈ 37.59
FPS = 30
FRAMES = 240          # 8 秒
TURNS = 2.5           # 螺旋圈数 (静态底)

gammas = [float(mp.im(mp.zetazero(n))) for n in range(1, N_ZEROS + 1)]

fig = plt.figure(figsize=(12.5, 5.6))
ax3 = fig.add_subplot(1, 2, 1, projection="3d")
ax2 = fig.add_subplot(1, 2, 2)

# ---------- 3D: 螺旋柱面 ----------
tt = np.linspace(0, TURNS * 2 * np.pi, 2000)
ax3.plot(SQRT_E * np.cos(tt), SQRT_E * np.sin(tt), tt, "r-", lw=1.1, alpha=0.55,
         label="临界线像 = 螺旋 (半径 √e)")
for k in range(int(TURNS) + 2):
    th = np.linspace(0, 2 * np.pi, 120)
    ax3.plot(SQRT_E * np.cos(th), SQRT_E * np.sin(th), np.full(120, k * 2 * np.pi),
             "gray", lw=0.3, alpha=0.35)
# 零点静态底座 (灰, 将被点亮)
zero_sc = []
for g in gammas:
    s = ax3.scatter([SQRT_E * np.cos(g)], [SQRT_E * np.sin(g)], [g],
                    c="gray", s=70, depthshade=False)
    zero_sc.append(s)
# 动态亮点
pt3, = ax3.plot([], [], [], "o", color="orange", ms=10, zorder=10)
ax3.set_xlabel("Re w"); ax3.set_ylabel("Im w"); ax3.set_zlabel("圈数 t")
ax3.set_title("螺旋爬升: t = 0.00", fontsize=11)
ax3.set_xlim(-2, 2); ax3.set_ylim(-2, 2); ax3.set_zlim(0, TURNS * 2 * np.pi + 2)
ax3.legend(loc="upper left", fontsize=8)

# ---------- 2D: 圆 (投影) ----------
th2 = np.linspace(0, 2 * np.pi, 400)
ax2.plot(SQRT_E * np.cos(th2), SQRT_E * np.sin(th2), "r-", lw=2.2,
         label="圆周 |w| = √e")
ax2.plot(np.e * np.cos(th2), np.e * np.sin(th2), "b-", lw=1, alpha=0.5,
         label="|w| = e")
zero2 = []
for g in gammas:
    z2, = ax2.plot([SQRT_E * np.cos(g)], [SQRT_E * np.sin(g)], "k*", ms=13)
    zero2.append(z2)
traj, = ax2.plot([], [], "-", color="orange", lw=1.8, alpha=0.9)
pt2, = ax2.plot([], [], "o", color="orange", ms=9, zorder=10)
ax2.axhline(0, color="k", lw=0.5); ax2.axvline(0, color="k", lw=0.5)
ax2.set_xlim(-3.2, 3.2); ax2.set_ylim(-3.2, 3.2)
ax2.set_aspect("equal")
ax2.set_xlabel("Re w"); ax2.set_ylabel("Im w")
ax2.set_title("投影: 亮点沿圆绕圈", fontsize=11)
ax2.legend(loc="upper left", fontsize=8)

found_txt = ax2.text(0.02, 0.02, "", transform=ax2.transAxes, fontsize=10,
                     color="darkred")

def update(frame):
    t = T_MAX * frame / FRAMES
    # 3D 亮点
    pt3.set_data([SQRT_E * np.cos(t)], [SQRT_E * np.sin(t)])
    pt3.set_3d_properties([t])
    # 2D 投影 + 最近一圈轨迹
    ts = np.linspace(max(0.0, t - 2 * np.pi), t, 120)
    traj.set_data(SQRT_E * np.cos(ts), SQRT_E * np.sin(ts))
    pt2.set_data([SQRT_E * np.cos(t)], [SQRT_E * np.sin(t)])
    # 点亮已过的零点
    for i, g in enumerate(gammas):
        if t >= g:
            zero_sc[i].set_color("red")
            zero2[i].set_color("red")
            zero2[i].set_markersize(15)
        else:
            zero_sc[i].set_color("gray")
            zero2[i].set_color("k")
            zero2[i].set_markersize(13)
    n_found = sum(1 for g in gammas if t >= g)
    found_txt.set_text(f"已发现零点: {n_found}/{N_ZEROS}  "
                       f"(γ₁..γ₆ = {', '.join(f'{g:.1f}' for g in gammas)})")
    ax3.set_title(f"螺旋爬升: t = {t:.2f}", fontsize=11)
    ax2.set_title(f"投影: 亮点沿圆绕圈 (角度 t mod 2π = {t % (2 * np.pi):.2f})",
                  fontsize=11)
    return pt3, pt2, traj

anim = FuncAnimation(fig, update, frames=FRAMES, interval=1000 / FPS, blit=False)
anim.save(f"{OUT}/fig8_spiral_animation.gif", writer=PillowWriter(fps=FPS))
plt.close(fig)
import os
print(f"已生成: {OUT}/fig8_spiral_animation.gif "
      f"({os.path.getsize(f'{OUT}/fig8_spiral_animation.gif')//1024} KB, "
      f"{FRAMES} 帧 @ {FPS}fps = {FRAMES/FPS:.1f}s)")
