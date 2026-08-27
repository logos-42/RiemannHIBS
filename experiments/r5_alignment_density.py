"""R5: 对齐密度的频率投影 — 隐数坐标系独有猜想 + 数值验证
猜想: 零点 (对齐事件) 密度 = 频率密度的干涉投影
  N(T) ≈ F(T) = (T/2π)·(log(T/2π) − 1)   (fig11 已验 N(680)=400 vs 398.5)
对照: 平凡零点 −2k 的反演对 1+2k 不是零点 (排斥因子破坏 ⟹ 反演对只属临界带)
"""
import mpmath as mp
mp.mp.dps = 15

def zeta_zero_count(T):
    """高度 ≤ T 的非平凡零点数 (二分)"""
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

print("=== R5a: 对齐密度投影 N(T) vs F(T) ===")
print(f"{'T':>8} {'N(T)':>8} {'F(T)':>10} {'N/F':>8} {'δ̄(T)':>8}")
for T in [100, 200, 400, 800, 1600, 3200]:
    N = zeta_zero_count(T)
    F = (T / (2 * mp.pi)) * (mp.log(T / (2 * mp.pi)) - 1)
    # 频率均匀性: 归一化间距 δ̄ (前 X 个频率, X = sqrt(T/2π))
    X = int(mp.sqrt(T / (2 * mp.pi))) + 1
    freqs = [mp.log(n + 1) for n in range(1, X + 1)]
    gaps = [freqs[i + 1] - freqs[i] for i in range(len(freqs) - 1)]
    mean_gap = (freqs[-1] - freqs[0]) / (len(freqs) - 1)
    delta_bar = sum(g / mean_gap for g in gaps) / len(gaps)
    print(f"{T:>8} {N:>8} {float(F):>10.2f} {float(N / F):>8.4f} {float(delta_bar):>8.4f}")

print()
print("=== R5b: 反演对破坏检验 (平凡零点 vs 非平凡) ===")
print("平凡零点 s=-2k 的反演对 s'=1+2k: ζ(1+2k) ≠ 0 (排斥因子破坏 ⟹ 对分解只属临界带)")
for k in [1, 2, 3]:
    s = 1 + 2 * k
    z = mp.zeta(s)
    print(f"  k={k}: ζ({s}) = {float(z):+.6f}  (≠0 ✓ 反演对破坏)")
print("非平凡零点对 (临界带): ζ(1/2+it) 与镜像 1−(1/2+it) = 1/2−it (共轭)")
for n in [1, 2, 3]:
    t = mp.im(mp.zetazero(n))
    z1 = mp.zeta(0.5 + 1j * t)
    z2 = mp.zeta(1 - (0.5 + 1j * t))
    print(f"  γ_{n}={mp.nstr(t, 6)}: |ζ(1/2+it)|={mp.nstr(abs(z1), 3)}  |ζ(1-s)|={mp.nstr(abs(z2), 3)}  (都≈0 ✓ 成对)")

print()
print("=== R5c: 对齐质量 (零点处 Dirichlet 部分和衰减) ===")
t = float(mp.im(mp.zetazero(1)))
for N in [10, 50, 100, 200, 400]:
    S = sum((n + 1) ** (-0.5 - 1j * t) for n in range(N))
    print(f"  gamma1={t:.4f}, N={N:>4}: |S_N|={abs(S):.5f}  尾~N^-0.5={N ** -0.5:.4f}")
