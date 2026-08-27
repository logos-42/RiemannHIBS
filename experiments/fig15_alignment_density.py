"""fig15: 对齐密度投影 — 频率均匀性 → 对齐密度 (隐数坐标系猜想)
上: N(T)/F(T) → 1 (零点计数 = 频率相位投影, 无 Stirling)
下: 反演对分解对照 (平凡零点被排斥因子破坏 vs 临界带零点成对)

双语标注: FIG_LANG=en|zh (默认 en) → viz/fig15_en.png / viz/fig15_zh.png
"""
import os
import mpmath as mp
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm

LANG = os.environ.get("FIG_LANG", "en")

# 中文字体配置 (与 viz/fig11_zero_abundance.py 一致)
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

T = {
    "en": {
        "limit_label": "1 (conjectured limit)",
        "ratio_label": "N(T)/F(T)",
        "xlabel_left": "T (高度)",
        "ylabel_left": "N(T) / F(T)",
        "title_left": ("Alignment-density projection: zero count = "
                       "frequency-phase budget\n"
                       "N(T) ≈ (T/2π)(log(T/2π) − 1) — no Stirling"),
        "trivial_label": ("ζ(1+2k): inversion image of trivial zeros "
                          "(≠0, repulsion breaks pair)"),
        "pair_label": "|ζ(1−s)|: inversion image of strip zeros (≈0, paired)",
        "ylabel_right": "|ζ| (对数)",
        "title_right": "Inversion-pair decomposition: critical strip only (R4 check)",
    },
    "zh": {
        "limit_label": "1 (猜想极限)",
        "ratio_label": "N(T)/F(T)",
        "xlabel_left": "T (高度)",
        "ylabel_left": "N(T) / F(T)",
        "title_left": ("对齐密度投影：零点计数 = 频率相位预算\n"
                       "N(T) ≈ (T/2π)(log(T/2π) − 1) — 无需 Stirling"),
        "trivial_label": "ζ(1+2k)：平凡零点的反演像 (≠0，排斥破坏配对)",
        "pair_label": "|ζ(1−s)|：临界带零点的反演像 (≈0，成对)",
        "ylabel_right": "|ζ| (对数)",
        "title_right": "反演对分解：仅临界带 (R4 检验)",
    },
}
if LANG not in T:
    LANG = "en"

mp.mp.dps = 15

def zeta_zero_count(T):
    lo, hi = 1, max(100, int(T * 3))
    while mp.im(mp.zetazero(hi)) < T:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mp.im(mp.zetazero(mid)) <= T:
            lo = mid
        else:
            hi = mid
    return lo

Ts = [100, 200, 400, 800, 1600, 3200]
Ns = [zeta_zero_count(T) for T in Ts]
Fs = [(T / (2 * mp.pi)) * (mp.log(T / (2 * mp.pi)) - 1) for T in Ts]
ratio = [N / F for N, F in zip(Ns, Fs)]

fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 4.2))

# 左: 对齐密度投影
ax1.axhline(1.0, color="gray", ls="--", lw=0.8, label=T[LANG]["limit_label"])
ax1.plot(Ts, [float(r) for r in ratio], "o-", color="#1f77b4", label=T[LANG]["ratio_label"])
ax1.set_xscale("log")
ax1.set_xlabel(T[LANG]["xlabel_left"])
ax1.set_ylabel(T[LANG]["ylabel_left"])
ax1.set_title(T[LANG]["title_left"])
ax1.legend()
ax1.grid(alpha=0.3)

# 右: 反演对分解对照
kvals = [1, 2, 3]
triv = [float(mp.zeta(1 + 2 * k)) for k in kvals]
gammas = [mp.im(mp.zetazero(n)) for n in [1, 2, 3]]
pair = [abs(mp.zeta(1 - (0.5 + 1j * t))) for t in gammas]
x = range(3)
ax2.bar([i - 0.18 for i in x], triv, width=0.36, color="#d62728", label=T[LANG]["trivial_label"])
ax2.bar([i + 0.18 for i in x], pair, width=0.36, color="#2ca02c", label=T[LANG]["pair_label"])
ax2.set_xticks(list(x))
ax2.set_xticklabels([f"k={k}" for k in kvals])
ax2.set_yscale("log")
ax2.set_ylabel(T[LANG]["ylabel_right"])
ax2.set_title(T[LANG]["title_right"])
ax2.legend(fontsize=8)
ax2.grid(alpha=0.3)

plt.tight_layout()
out = f"viz/fig15_{LANG}.png"
plt.savefig(out, dpi=150)
print(f"saved {out}")
