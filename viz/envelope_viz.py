#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RiemannHIBS — 隐数包络 (Envelope) 可视化
对应 Lean 模块: RiemannHIBS.Envelope (core) 与 RiemannHIBS.EnvelopeC (mathlib).

几何事实 (已在 Lean 中形式化证明):
  - 隐数空间 S = ℤ×{S,R,iR} 是 ℂ 上的"三叶覆盖" (离散包络).
  - 连续化 E = ℝ×Tag, 投影 hEvalC:
        ⟨x, S⟩  ↦  x        (正实轴)
        ⟨x, R⟩  ↦ −x        (负实轴, A2b 符号携带)
        ⟨y, iR⟩ ↦ y·i       (虚轴)
  - 投影像 = 实轴 ∪ 虚轴 (十字). 同一点 x 来自 S 叶与 R 叶两片 (折叠 = 非单射投影).
  - 临界截面 criticalSectionC: 临界线 Re(s)=1/2 嵌入包络,
        RiemannHypothesisHiddenC: 经典 RH ⟹ 零点纤维 ⊂ 该截面投影像.
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle

OUT = "viz"

def fig_projection_cross():
    """图1: 三叶投影到 ℂ 的十字 + 折叠标记."""
    fig, ax = plt.subplots(figsize=(7, 7))
    # 实轴 / 虚轴
    ax.axhline(0, color="gray", lw=1)
    ax.axvline(0, color="gray", lw=1)

    x = np.linspace(-3, 3, 400)
    # S 叶: 正实轴 (x -> x, 取 x>=0 为正, 但整条实轴都可由 S 或 R 覆盖)
    ax.plot(x, np.zeros_like(x), color="#1f77b4", lw=3, label="S sheet (<x,S>|->x, real axis)")
    # R 叶: 负实轴 (x -> -x) -- 画在实轴上但用不同样式表示"来自 R 叶的符号反转"
    ax.plot(-x, np.zeros_like(x), color="#ff7f0e", lw=1.5, linestyle="--",
            label="R sheet (<x,R>|->-x, same real axis, A2b)")
    # iR 叶: 虚轴
    y = np.linspace(-3, 3, 400)
    ax.plot(np.zeros_like(y), y, color="#2ca02c", lw=3, label="iR sheet (<y,iR>|->y*i, imag axis)")

    # 折叠 witness: 点 x=2 同时有 S 叶 (2) 与 R 叶 (−2 投影后=2)
    ax.plot(2, 0, "o", color="#1f77b4", ms=10)
    ax.plot(-2, 0, "s", color="#ff7f0e", ms=10)
    ax.annotate("fold: <2,S> and <-2,R>\nboth project to z=2 (pi non-injective)",
                xy=(2, 0), xytext=(2.2, 1.6), fontsize=9,
                arrowprops=dict(arrowstyle="->"))

    ax.set_xlim(-3.5, 3.5)
    ax.set_ylim(-3.5, 3.5)
    ax.set_xlabel("Re(z)")
    ax.set_ylabel("Im(z)")
    ax.set_title("Envelope projection: 3-sheet shell -> real U imag axis (cross)\n"
                 "fold = non-injective projection pi (A1)")
    ax.legend(loc="upper right", fontsize=8)
    ax.grid(True, alpha=0.2)
    fig.tight_layout()
    fig.savefig(f"{OUT}/fig1_projection_cross.png", dpi=140)
    plt.close(fig)


def fig_envelope_shell():
    """图2: 连续包络 E = ℝ×Tag 的三维示意, 投影沿三轴落回 ℂ."""
    from mpl_toolkits.mplot3d import Axes3D  # noqa
    fig = plt.figure(figsize=(9, 7))
    ax = fig.add_subplot(111, projection="3d")

    xs = np.linspace(-2, 2, 30)
    # S 叶 (tag 编码 = 0) 沿 x 轴
    ax.plot(xs, np.zeros_like(xs), np.zeros_like(xs) + 0, color="#1f77b4", lw=2,
            label="S sheet (tag=S)")
    # R 叶 (tag 编码 = 1) 沿 x 轴, 但投影 = -x
    ax.plot(xs, np.zeros_like(xs), np.zeros_like(xs) + 1, color="#ff7f0e", lw=2,
            label="R sheet (tag=R, proj -x)")
    # iR 叶 (tag 编码 = 2) 沿 y 轴
    ys = np.linspace(-2, 2, 30)
    ax.plot(np.zeros_like(ys), ys, np.zeros_like(ys) + 2, color="#2ca02c", lw=2,
            label="iR sheet (tag=iR, proj y*i)")

    # 投影到基空间 (ℂ 十字, 放在 z=0 平面)
    ax.plot(xs, np.zeros_like(xs), np.zeros_like(xs), color="gray", lw=1, alpha=0.5)
    ax.plot(np.zeros_like(ys), ys, np.zeros_like(ys), color="gray", lw=1, alpha=0.5)
    # 连接线: 每叶到基空间投影
    for xi in [-1.5, 0.5, 1.8]:
        ax.plot([xi, xi], [0, 0], [0, 0], color="#1f77b4", ls=":", alpha=0.4)
    for yi in [-1.2, 1.2]:
        ax.plot([0, 0], [yi, yi], [2, 0], color="#2ca02c", ls=":", alpha=0.4)

    ax.set_xlabel("val (hidden coord)")
    ax.set_ylabel("val (iR sheet imag)")
    ax.set_zlabel("tag axis (S/R/iR)")
    ax.set_title("Continuous envelope E = R x Tag: total-space shell,\n"
                 "projection hEvalC drops to C cross along 3 axes")
    ax.legend(fontsize=8)
    fig.tight_layout()
    fig.savefig(f"{OUT}/fig2_envelope_shell.png", dpi=140)
    plt.close(fig)


def fig_critical_section():
    """图3: 临界截面 (临界线 1/2+it) + 已知 ζ 非平凡零点佐证."""
    fig, ax = plt.subplots(figsize=(7, 7))
    ax.axhline(0, color="gray", lw=1)
    ax.axvline(0, color="gray", lw=1)
    # 临界线
    t = np.linspace(-22, 22, 800)
    ax.plot(np.ones_like(t) * 0.5, t, color="red", lw=2, label="critical line Re(s)=1/2")

    # 已知 ζ 非平凡零点虚部 (前 10 个正虚部, 来自文献)
    zeros_im = [14.1347, 21.0220, 25.0109, 30.4249, 32.9351,
                37.5862, 40.9187, 43.3271, 48.0052, 49.7738]
    for yi in zeros_im:
        ax.plot(0.5, yi, "k*", ms=9)
        ax.plot(0.5, -yi, "k*", ms=9)
    ax.plot([], [], "k*", ms=9, label="zeta nontrivial zeros (known, all on critical line)")

    ax.set_xlim(-1, 3)
    ax.set_ylim(-22, 22)
    ax.set_xlabel("Re(s)")
    ax.set_ylabel("Im(s)")
    ax.set_title("Critical section criticalSectionC: zero fibers subset of critical line\n"
                 "(RiemannHypothesisHiddenC); known zeta zeros lie on Re=1/2")
    ax.legend(loc="lower right", fontsize=8)
    ax.grid(True, alpha=0.2)
    fig.tight_layout()
    fig.savefig(f"{OUT}/fig3_critical_section.png", dpi=140)
    plt.close(fig)


def fig_phase_cover():
    """图4: 相位包络 hEvalPhase ⟨r,θ⟩ = r·e^{iθ} 覆盖整个 ℂ."""
    fig, ax = plt.subplots(figsize=(7, 7))

    # 极坐标网格: r ∈ [0.2, 3], θ ∈ [0, 2π) -- 每个格点 ⟨r,θ⟩ 投影到一个复点
    rs = np.linspace(0.3, 3.0, 22)
    thetas = np.linspace(0, 2 * np.pi, 48)
    R, T = np.meshgrid(rs, thetas)
    X = R * np.cos(T)
    Y = R * np.sin(T)
    # 画同心圆 (等半径) 与 射线 (等相位) -- 展示 (r,θ) 参数扫过全平面
    for r in rs[::4]:
        ax.add_patch(Circle((0, 0), r, fill=False, color="#888888", lw=0.5))
    for th in thetas[::6]:
        ax.plot([0, 3 * np.cos(th)], [0, 3 * np.sin(th)], color="#cccccc", lw=0.5)
    # 相位叶 (固定 θ) 的几条径向线, 突出"叶"
    for th in [0, np.pi / 3, 2 * np.pi / 3, np.pi, 4 * np.pi / 3, 5 * np.pi / 3]:
        ax.plot([0, 3.2 * np.cos(th)], [0, 3.2 * np.sin(th)], color="#ff7f0e", lw=1.5, alpha=0.7)

    # 原点 (所有相位叶相交处 = 奇异点)
    ax.plot(0, 0, "o", color="black", ms=5)
    ax.annotate("origin: all phase leaves meet", xy=(0, 0), xytext=(0.6, -2.8), fontsize=8,
                arrowprops=dict(arrowstyle="->"))

    ax.set_xlim(-3.5, 3.5)
    ax.set_ylim(-3.5, 3.5)
    ax.set_xlabel("Re(z)")
    ax.set_ylabel("Im(z)")
    ax.set_title("Phase envelope: hEvalPhase <r,theta> = r*e^(i*theta) covers ALL of C\n"
                 "(polar coordinates; phase leaves are rays through origin)")
    ax.grid(True, alpha=0.2)
    fig.tight_layout()
    fig.savefig(f"{OUT}/fig4_phase_cover.png", dpi=140)
    plt.close(fig)


if __name__ == "__main__":
    import os
    os.makedirs(OUT, exist_ok=True)
    fig_projection_cross()
    fig_envelope_shell()
    fig_critical_section()
    fig_phase_cover()
    print("已生成:")
    for f in ["fig1_projection_cross.png", "fig2_envelope_shell.png",
              "fig3_critical_section.png", "fig4_phase_cover.png"]:
        print("  ", f"{OUT}/{f}")
