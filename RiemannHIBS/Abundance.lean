-- RiemannHIBS.Abundance — 零点丰度的频率坐标 (frequency coordinate)
--
-- 机制: 零点是频率集 {log n} 的干涉图样 — Dirichlet 第 n 项是角速度
--   log(n+1) 的旋转向量 (Analytic.lean §17 dirichlet_term_rotating_vector).
--   log 因子 = 频率密度 d(log n) 的均匀性 (数值: 归一化间距 δ̄=0.9999,
--   fig11_zero_abundance; N(T) ≈ (T/2π)(log(T/2π) − 1) 无需 Stirling).
--
-- 本模块 (独立, 仅依赖 mathlib): 频率坐标的**可证离散骨架** —
--   1. 频率跨度 (telescoping): Σ Δfreq = log N  — "log 因子"的精确离散版
--   2. 频率间距收缩: Δfreq n ≤ 1/(n+1)           — 频率谱稠密化
--   3. 密度下界: log(N+1) ≤ Σ_{n<N} 1/(n+1)      — "密度 = log"的调和版
--   4. Draft (如实标注): 丰度机制声明 — 连续极限 (Riemann–Siegel 估计) 未证
--
-- 与 Analytic.lean 的关系: 独立模块, 不依赖其 (对方正在编辑, 编译未稳).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.CauchyIntegral

open scoped Topology
open Set

namespace RiemannHIBS.Abundance

-- ====================================================================
-- 频率坐标: 第 n 个自然数的角速度 (旋转向量频率)
-- ====================================================================

-- 频率: freq n = log(n+1)  (Dirichlet 第 n 项的角速度)
noncomputable def freq (n : ℕ) : ℝ := Real.log (((n + 1 : ℕ) : ℝ))

-- 频率间距: 相邻角速度之差
noncomputable def freqGap (n : ℕ) : ℝ := freq (n + 1) - freq n

-- 频率坐标原点: freq 0 = log 1 = 0
theorem freq_zero : freq 0 = 0 := by
  simp [freq]

-- ====================================================================
-- 1. 频率跨度 (telescoping): Σ_{n<N} Δfreq = log(N+1)
--    "log 因子"在离散骨架层面是精确恒等式, 不是渐近.
-- ====================================================================

-- 频率坐标的总跨度 = log(N+1): 丰度公式中 log 因子的离散精确版
theorem freq_span_telescopes (N : ℕ) :
    (∑ n ∈ Finset.range N, freqGap n) = Real.log (((N + 1 : ℕ) : ℝ)) := by
  -- telescoping: Σ (f(n+1) − f n) = f N − f 0
  dsimp [freqGap, freq]
  change (∑ n ∈ Finset.range N,
      (Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)))) =
    Real.log (((N + 1 : ℕ) : ℝ))
  rw [Finset.sum_range_sub (fun k : ℕ => Real.log (((k + 1 : ℕ) : ℝ))) N]
  -- 化简: log 1 = 0
  simp

-- ====================================================================
-- 2. 频率间距收缩: Δfreq n ≤ 1/(n+1)
--    log(1 + x) ≤ x with x = 1/(n+1): 对数间距随 n 递减 (频率谱稠密化).
-- ====================================================================

-- 频率间距 = log(1 + 1/(n+1))
theorem freqGap_eq_log_one_add (n : ℕ) :
    freqGap n = Real.log (1 + 1 / (((n + 1 : ℕ) : ℝ))) := by
  unfold freqGap freq
  change Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)) =
    Real.log (1 + 1 / (((n + 1 : ℕ) : ℝ)))
  -- log(n+2) − log(n+1) = log((n+2)/(n+1)) = log(1 + 1/(n+1))
  have hdiv : Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) =
      Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)) := by
    apply Real.log_div
    · exact_mod_cast (Nat.succ_ne_zero (n + 1))
    · exact_mod_cast (Nat.succ_ne_zero n)
  rw [← hdiv]
  congr 1
  -- (n+2)/(n+1) = 1 + 1/(n+1)  (ℝ 层, 先拆 cast 再环等式)
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

-- 频率间距收缩: Δfreq n ≤ 1/(n+1)  (对数间距递减)
theorem freq_gap_le_inv (n : ℕ) :
    freqGap n ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by
  rw [freqGap_eq_log_one_add]
  -- log(1+x) ≤ x  with x = 1/(n+1)
  have hx : 0 < 1 + 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
  have hle := Real.log_le_sub_one_of_pos hx
  -- hle : log (1 + x) ≤ (1 + x) − 1 = x
  simpa using hle

-- ====================================================================
-- 3. 密度下界: log(N+1) ≤ Σ_{n<N} 1/(n+1)
--    "密度 = log"的调和版本 — 频率坐标总跨度 ≤ 调和和 (逐项收缩).
-- ====================================================================

-- 频率密度下界: log(N+1) ≤ 调和和 (从 telescope + 逐项收缩推出)
theorem log_le_harmonic_sum (N : ℕ) :
    Real.log (((N + 1 : ℕ) : ℝ)) ≤
      ∑ n ∈ Finset.range N, 1 / (((n + 1 : ℕ) : ℝ)) := by
  calc
    Real.log (((N + 1 : ℕ) : ℝ))
        = ∑ n ∈ Finset.range N, freqGap n := (freq_span_telescopes N).symm
    _ ≤ ∑ n ∈ Finset.range N, 1 / (((n + 1 : ℕ) : ℝ)) := by
          exact Finset.sum_le_sum (fun n _ => freq_gap_le_inv n)

-- ====================================================================
-- 5. 能量无界: 调和和超过任意界 (零点无限性论证的能量侧)
--    用户的能量描述: 每项能量 (n+1)^{-1}, 总和 = 调和级数 (发散).
--    这里证明它的精确形式: ∀ B, ∃ N, B < Σ_{n<N} 1/(n+1).
--    证明: log(N+1) → ∞ (tendsto_log_atTop) + log(N+1) ≤ 调和和.
-- ====================================================================

-- 能量无界 (调和发散): 调和和超过任意界
--   = "零点无限性"论证中能量侧的精确可证内核
--   证明: 对任意 B, 取 x = exp(B+1) ⟹ B < log x; Archimedean 取 N > x;
--     log 严格递增 ⟹ log x < log(N+1) ≤ 调和和 (log_le_harmonic_sum).
theorem harmonic_sum_unbounded : ∀ B : ℝ, ∃ N : ℕ,
    B < ∑ n ∈ Finset.range N, 1 / (((n + 1 : ℕ) : ℝ)) := by
  intro B
  -- 取 x = exp(B+1): B < log x (log_exp)
  let x : ℝ := Real.exp (B + 1)
  have hBlog : B < Real.log x := by
    dsimp [x]
    rw [Real.log_exp]
    linarith
  -- Archimedean: 取 N 使 x < (N : ℝ) ≤ (N+1 : ℝ)
  rcases exists_nat_gt x with ⟨N, hN⟩
  -- log 严格递增: log x < log(N+1)
  have hlog : Real.log x < Real.log (((N + 1 : ℕ) : ℝ)) := by
    apply Real.log_lt_log
    · exact Real.exp_pos (B + 1)
    · -- x < (N:ℝ) ≤ (N+1:ℝ)
      have hN1 : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.le_succ N)
      linarith [hN, hN1]
  refine ⟨N, ?_⟩
  -- B < log x < log(N+1) ≤ 调和和
  exact lt_of_lt_of_le (lt_trans hBlog hlog) (log_le_harmonic_sum N)

-- ====================================================================
-- 6. Draft (如实标注): 零点无限性与 ζ↔零点一一对应
--    能量无界 (上) 是 Hardy 论证的能量侧; 完整论证还需要:
--      (a) 均值定理: ∫₀ᵀ |ζ(1/2+it)|² dt 的对角贡献 = Σ_{n≤√(T/2π)} (n+1)^{-1}
--          随 T → ∞ 发散 (Riemann–Siegel/Hardy–Littlewood, mathlib 无)
--      (b) 有限零点 ⟹ 对数均值有界 (1/ζ 有界 + 辐角缠绕有界)
--      (a)+(b) 矛盾 ⟹ 临界线上有无限零点 (Hardy 1914, 经典已证).
--    零点与 ℕ 的一一对应: 零点无限 + 零点孤立 (ζ 在 s≠1 解析) + 无聚点
--      (亚纯) ⟹ 可按虚部排序 γ₁<γ₂<… 与 ℕ 双射; 排序存在性未形式化.
-- ====================================================================

-- Hardy 零点无限性桥 (概念注释; 完整证明需均值定理, 未形式化):
--   1. 均值定理: ∫₀ᵀ |ζ(1/2+it)|² dt 的对角贡献随 T 发散
--      (能量无界 ⟹ 均值无界; Hardy–Littlewood, mathlib 无)
--   2. 有限零点 ⟹ 均值有界 (1/ζ 有界 + 辐角缠绕有界)
--   3. 1+2 矛盾 ⟹ 临界线零点无限 (Hardy 1914, 经典已证)

-- 零点与 ζ 的一一对应 (概念注释, 非定理):
--   若临界线零点无限, 则零点集 {1/2 + iγ_n} 按虚部升序与 ℕ 双射 —
--   每个零点唯一对应一个自然数 (可枚举), 每个自然数唯一对应一个零点.
--   严格化需: 零点孤立 (下证) + 亚纯零点无聚点 + 排序定理. 未形式化, 如实标注.

-- ====================================================================
-- 7. 零点孤立: ζ 的每个非平凡零点是孤立零点 (identity theorem)
--    配合 §5 能量无界 (调和发散), 这是"零点无限 + 零点 ↔ ℕ 一一对应"
--    的支撑: 孤立零点 ⟹ 去心邻域无其他零点; 无限 + 孤立 ⟹ 可枚举.
-- ====================================================================

-- ζ 在 s ≠ 1 处解析 (DifferentiableOn → AnalyticAt)
theorem zeta_analyticAt (s : ℂ) (hs1 : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hdU : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    intro z hz
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hdU.analyticAt (isOpen_compl_singleton.mem_nhds hs1)

-- ζ(2) ≠ 0 (π²/6 ≠ 0) — 用于排除"恒零分支"
theorem zeta_two_ne_zero : riemannZeta 2 ≠ 0 := by
  rw [riemannZeta_two]
  exact div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)

-- 非平凡零点孤立: 每个零点 s ≠ 1 的去心邻域内无其他零点
--   证明: AnalyticAt.eventually_eq_zero_or_eventually_ne_zero 给出
--     "恒零分支 ∨ 去心非零分支"; 恒零分支被 identity theorem 排除
--     (ℂ∖{1} 连通 + ζ(2) ≠ 0 ⟹ ζ 不恒零).
theorem zeta_zero_isolated (s : ℂ) (hs1 : s ≠ 1) (_hz : riemannZeta s = 0) :
    ∀ᶠ z in 𝓝[≠] s, riemannZeta z ≠ 0 := by
  have hf : AnalyticAt ℂ riemannZeta s := zeta_analyticAt s hs1
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · -- 恒零分支: identity theorem ⟹ ζ 在 ℂ∖{1} 恒零 ⟹ ζ(2) = 0 矛盾
    exfalso
    have hfreq : ∃ᶠ z in 𝓝[≠] s, riemannZeta z = 0 :=
      (hzero.filter_mono nhdsWithin_le_nhds).frequently
    let U : Set ℂ := {z : ℂ | z ≠ 1}
    have hfU : AnalyticOnNhd ℂ riemannZeta U := by
      intro z hz
      exact zeta_analyticAt z hz
    have hU : IsPreconnected U := by
      have hrank : 1 < Module.rank ℝ ℂ := by
        rw [Complex.rank_real_complex]
        norm_num
      exact (isPathConnected_compl_singleton_of_one_lt_rank hrank (1 : ℂ)).isConnected.isPreconnected
    have hEq : EqOn riemannZeta 0 U :=
      hfU.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hs1 hfreq
    have hz2 : riemannZeta 2 = 0 := hEq (by norm_num : (2 : ℂ) ≠ 1)
    exact zeta_two_ne_zero hz2
  · exact hne

-- ====================================================================
-- 8. Draft (如实标注): 零点可枚举性
--    孤立零点 (上) + 零点无聚点 (identity theorem 推论) ⟹ 零点集
--    是 ℂ 的离散子集; ℂ 是第二可数空间, 孤立点集可数 (mathlib 无
--    现成引理, 未形式化). 若再配合 §5 能量无界 (调和发散 ⟹ 零点
--    无限, Hardy 桥), 则零点按虚部升序 γ₁<γ₂<… 与 ℕ 双射 —
--    "零点与 ζ 一一对应"的完整链条. 排序定理本身未形式化.
-- ====================================================================

-- ====================================================================
-- 4. Draft (如实标注): 零点丰度的频率机制
--    离散骨架已证 (上述); 连续极限未证:
--       N(T) = (1/2π)∫₀ᵀ log(t/2π) dt = (T/2π)(log(T/2π) − 1)
--     需要 Riemann–Siegel 型估计 (截断 n ≤ √(t/2π) + 误差控制) 与
--     零点计数 ↔ 相位缠绕的桥接 — 超出本模块, 完整形式化待后续.
-- ====================================================================

-- 丰度机制声明 (概念层, 无结构体 — 字段须为证明, 故以注释记录待证命题):
--   1. 间距 = 频率带宽倒数 (不确定性原理型): Δγ ≈ 2π/log(γ/2π)
--      (数值: 归一化间距均值 δ̄ = 0.9999, fig11)
--   2. 计数 = 频率密度积分: N(T) = (1/2π)∫₀ᵀ log(t/2π) dt
--      = (T/2π)(log(T/2π) − 1)  (von Mangoldt 主项)
--   3. 零点角度均匀: γ mod 2π 近均匀 (数值 χ² 支持, 未证)
--   连续极限需要 Riemann–Siegel 型估计, 超出本模块.

end RiemannHIBS.Abundance
