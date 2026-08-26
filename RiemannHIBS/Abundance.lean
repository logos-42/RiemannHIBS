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
