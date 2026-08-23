#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
RiemannHIBS — 包络合并可视化 (方向 2 + 3)
=========================================
fig5_rollup.png   : s 平面临界线(直线) ↔ w 平面圆周 |w|=√e (卷绕合并图)
                    —— 对方 fig3 (s 平面零点) + 本会话 envelope_critical 合并
fig6_winding.png  : argument principle 可视化: ζ 沿矩形路径的像绕原点 6 圈
                    —— 数值补强 E4 (数圈数 = 数零点) 的直观图
"""
import mpmath as mp
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
from matplotlib.patches import Rectangle

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

# ------------------------------------------------------------------
# fig5: 临界线直线 → 圆周 √e (卷绕)
# ------------------------------------------------------------------
def fig5_rollup():
    gammas = [float(mp.im(mp.zetazero(n))) for n in range(1, N_ZEROS + 1)]

    fig, (a1, a2) = plt.subplots(1, 2, figsize=(12, 5.6),
                                 gridspec_kw={"width_ratios": [1, 1.25]})

    # --- 左: s 平面 ---
    tvals = np.linspace(-40, 40, 600)
    a1.plot([0.5, 0.5], [tvals[0], tvals[-1]], "r-", lw=2,
            label="临界线 Re s = 1/2")
    a1.plot([1, 1], [tvals[0], tvals[-1]], "b-", lw=1.2, alpha=0.6,
            label="Re s = 1 (极点)")
    for i, g in enumerate(gammas, 1):
        a1.plot(0.5, g, "r*", ms=11)
        a1.annotate(str(i), (0.5, g), textcoords="offset points",
                    xytext=(8, 4), fontsize=9, color="red")
        a1.plot(0.5, -g, "r*", ms=8, alpha=0.5)
    a1.plot(1, 0, "ko", ms=9)
    a1.annotate("极点 s=1", (1, 0), textcoords="offset points", xytext=(8, 8))
    a1.axhline(0, color="k", lw=0.5)
    a1.set_xlim(-0.2, 1.8); a1.set_ylim(-40, 40)
    a1.set_xlabel("Re s"); a1.set_ylabel("Im s = t")
    a1.set_title("s 平面: 临界线是直线\n零点 γ₁..γ₆ 在线上 (编号)")
    a1.legend(loc="upper left", fontsize=9)

    # --- 右: w 平面 (包络坐标) ---
    th = np.linspace(0, 2 * np.pi, 800)
    a2.plot(SQRT_E * np.cos(th), SQRT_E * np.sin(th), "r-", lw=2,
            label=r"圆周 $|w|=\sqrt{e}$ (临界线卷成)")
    a2.plot(np.e * np.cos(th), np.e * np.sin(th), "b-", lw=1.2, alpha=0.6,
            label=r"$|w|=e$ (极点/收敛边界)")
    for i, g in enumerate(gammas, 1):
        w = np.exp(0.5 + 1j * g)          # w = e^{1/2 + iγ}
        a2.plot(w.real, w.imag, "r*", ms=11)
        a2.annotate(str(i), (w.real, w.imag), textcoords="offset points",
                    xytext=(8, 4), fontsize=9, color="red")
    a2.plot(np.e, 0, "ko", ms=9)
    a2.annotate("极点 → w=e", (np.e, 0), textcoords="offset points",
                xytext=(10, -16), fontsize=9)
    # 映射轨迹: t 从 0 走到 γ₆, 在圆上走弧
    tt = np.linspace(0, gammas[-1], 3000)
    ww = np.exp(0.5 + 1j * tt)
    a2.plot(ww.real, ww.imag, color="orange", lw=1.0, alpha=0.7,
            label="像曲线 w=e^{1/2+it} (沿圆)")
    a2.axhline(0, color="k", lw=0.5); a2.axvline(0, color="k", lw=0.5)
    a2.set_xlim(-3.2, 3.2); a2.set_ylim(-3.2, 3.2)
    a2.set_aspect("equal")
    a2.set_xlabel("Re w"); a2.set_ylabel("Im w")
    a2.set_title("w = e^s 平面: 临界线卷成圆周\n零点像共圆 $|w|=\\sqrt{e}$ (同编号)")
    a2.legend(loc="upper left", fontsize=9)

    fig.suptitle("指数映射卷绕: 临界线 Re s = 1/2 (直线)  ↦  圆周 |w| = √e (共圆)",
                 fontsize=13)
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    fig.savefig(f"{OUT}/fig5_rollup.png", dpi=150)
    plt.close(fig)
    print("fig5_rollup.png 已生成")

# ------------------------------------------------------------------
# fig6: argument principle — ζ 的像曲线绕原点 6 圈
# ------------------------------------------------------------------
def fig6_winding():
    # 矩形 R = [1/3, 5/6] × [0, 38], 内部 6 个非平凡零点
    sig1, sig2, T = 1 / 3, 5 / 6, 38.0
    N = 500

    def path():
        # 逆时针, 返回 (z 列表)
        seg1 = [complex(sig2, t) for t in np.linspace(0, T, N)]
        seg2 = [complex(s, T) for s in np.linspace(sig2, sig1, N)]
        seg3 = [complex(sig1, t) for t in np.linspace(T, 0, N)]
        seg4 = [complex(s, 0) for s in np.linspace(sig1, sig2, N)]
        return seg1 + seg2 + seg3 + seg4

    pts = path()
    # ζ 沿路径的像 (mpmath)
    mp.mp.dps = 18
    zeta_img = [mp.zeta(mp.mpc(z.real, z.imag)) for z in pts]
    img = np.array([(float(z.real), float(z.imag)) for z in zeta_img])

    fig, (a1, a2) = plt.subplots(1, 2, figsize=(12, 5.6),
                                 gridspec_kw={"width_ratios": [1, 1.6]})

    # --- 左: s 平面的矩形路径 + 零点 ---
    a1.add_patch(Rectangle((sig1, 0), sig2 - sig1, T, fill=False,
                           edgecolor="blue", lw=1.5))
    for n in range(1, 7):
        g = float(mp.im(mp.zetazero(n)))
        a1.plot(0.5, g, "r*", ms=10)
    a1.plot(0.5, 0, "ro", ms=4)
    a1.annotate("矩形 R = [1/3, 5/6]×[0, 38]\n含 6 个非平凡零点 (红星)",
                xy=(0.42, 22), fontsize=9)
    a1.set_xlim(0.2, 1.0); a1.set_ylim(-2, 40)
    a1.set_xlabel("Re s"); a1.set_ylabel("Im s")
    a1.set_title("s 平面: 积分路径 (逆时针矩形)")

    # --- 右: ζ 的像曲线 (ζ 值平面) ---
    a2.plot(img[:, 0], img[:, 1], color="purple", lw=1.2,
            label=r"像曲线 ζ(R)")
    a2.plot(0, 0, "ko", ms=6)
    a2.annotate("原点 (绕数计数的中心)", (0, 0),
                textcoords="offset points", xytext=(10, -20), fontsize=9)
    # 辅助: 圆心在原点半径 3 的圆 (参照)
    th = np.linspace(0, 2 * np.pi, 400)
    a2.plot(3 * np.cos(th), 3 * np.sin(th), "k--", lw=0.7, alpha=0.5)
    a2.axhline(0, color="k", lw=0.5); a2.axvline(0, color="k", lw=0.5)
    a2.set_xlim(-30, 30); a2.set_ylim(-30, 30)
    a2.set_aspect("equal")
    a2.set_xlabel("Re ζ"); a2.set_ylabel("Im ζ")
    a2.set_title("ζ 值平面: 像曲线绕原点 6 圈\n"
                 "W = (1/2πi)∮ ζ'/ζ dz = 6 (数圈数 = 数零点)")

    # 计算绕数 (跨过正实轴计数)
    winding = 0
    for i in range(1, len(img)):
        y0, y1 = img[i - 1, 1], img[i, 1]
        if y0 * y1 < 0 and img[i, 0] > 0:
            winding += 1 if y1 > y0 else -1
    fig.suptitle(f"Argument principle: 绕数 W = {winding} = 矩形内非平凡零点数 6",
                 fontsize=13)
    fig.tight_layout(rect=[0, 0, 1, 0.94])
    fig.savefig(f"{OUT}/fig6_winding.png", dpi=150)
    plt.close(fig)
    print(f"fig6_winding.png 已生成 (绕数 = {winding})")


if __name__ == "__main__":
    import os
    os.makedirs(OUT, exist_ok=True)
    fig5_rollup()
    fig6_winding()
    print("完成:", f"{OUT}/fig5_rollup.png", f"{OUT}/fig6_winding.png")
