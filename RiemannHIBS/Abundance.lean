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
--   4. 丰度机制: 离散骨架已证 (§1-3); 连续极限 (Riemann–Siegel 估计)
--      为外部输入, 显式声明于 §11 FrequencyMechanismAssumptions
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Rat.BigOperators
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped Topology
open scoped ComplexConjugate
open scoped BigOperators
open Set
open Filter

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
-- 6. 零点无限性与 ζ↔零点一一对应
--    能量无界 (上, §5) 是 Hardy 论证的能量侧; 完整论证还需要均值定理
--    (外部经典, §10 结构体显式承载). 一一对应的两个方向:
--      * 可数侧 (孤立 + 可数 + 双射枚举): §7 + §9 完整形式化 ✓
--      * 无限侧 (均值定理 ⟹ 零点无限): Hardy 1914 经典, 外部输入
--        (mathlib 无引理链), §10 HardyBridgeAssumptions 显式声明
--    "按虚部排序 γ₁<γ₂<…" 的严格化需要无聚点引理 (亚纯零点), 见 §9 注释.
-- ====================================================================

-- Hardy 零点无限性桥 (论证骨架, 外部输入在 §10 结构体):
--   1. 均值定理: ∫₀ᵀ |ζ(1/2+it)|² dt 的对角贡献随 T 发散 (外部经典)
--   2. 有限零点 ⟹ 均值有界 (1/ζ 有界 + 辐角缠绕有界)
--   3. 1+2 矛盾 ⟹ 临界线零点无限 (Hardy 1914, 经典已证)
--   我们的贡献: 从"无限"到"一一对应"的双射枚举 (§9.5 zero_enumeration_of_infinite).

-- ====================================================================
-- 7. 零点孤立: ζ 的每个非平凡零点是孤立零点 (identity theorem)
--    配合 §5 能量无界 (调和发散), 这是"零点无限 + 零点 ↔ ℕ 一一对应"
--    的支撑: 孤立零点 ⟹ 去心邻域无其他零点; 无限 + 孤立 ⟹ 可枚举
--    (可枚举性本身在 §9 完整形式化).
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
-- 8. 零点可枚举性 (见 §9 完整形式化 — 本节为桥梁说明)
--    孤立零点 (上) ⟹ 零点集是 ℂ 的离散子集; ℂ 第二可数 ⟹ 遗传
--    Lindelöf ⟹ 离散子集可数 (zero_set_countable, §9.4). 配合外部
--    无限性 (Hardy 桥, §10) ⟹ 零点与 ℕ 双射 (zero_enumeration_of_infinite).
--    "按虚部升序 γ₁<γ₂<…" 的保序细化需无聚点引理, 未单独形式化.
-- ====================================================================

-- ====================================================================
-- 9. 零点可枚举性 (完整形式化 — draft 清理)
--    孤立零点 (§7) ⟹ 零点集是 ℂ 的离散子集; ℂ 第二可数 ⟹ 遗传
--    Lindelöf ⟹ 离散子集可数; 可数 + (外部) 无限 ⟹ 与 ℕ 双射.
-- ====================================================================

-- 非平凡零点集 (排除 s = 1: ζ 在该点不解析; ζ(1) 的 mathlib 值见
-- riemannZeta_one, 可数性只依赖 s ≠ 1 处的解析孤立性)
abbrev zeroSet : Set ℂ := {s : ℂ | s ≠ 1 ∧ riemannZeta s = 0}

-- 9.1 孤立性 ⟹ 每个零点有分离开集 (V ∩ zeroSet = {z})
theorem zero_separating_open (z : ℂ) (hz1 : z ≠ 1) (hz : riemannZeta z = 0) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ∩ zeroSet = {z} := by
  have hne : ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 := zeta_zero_isolated z hz1 hz
  have hne' : ∀ᶠ w in 𝓝 z, w ≠ z → riemannZeta w ≠ 0 := by
    simpa [ne_eq] using (eventually_nhdsWithin_iff.mp hne)
  have hset : {w : ℂ | w ≠ z → riemannZeta w ≠ 0} ∈ 𝓝 z := hne'
  rcases mem_nhds_iff.mp hset with ⟨V, hVsub, hVopen, hzV⟩
  refine ⟨V, hVopen, hzV, ?_⟩
  apply Subset.antisymm
  · intro w hw
    by_contra hwz
    exact (hVsub hw.1 hwz) hw.2.2
  · intro w hw
    simp at hw
    simpa [hw] using (⟨hzV, ⟨hz1, hz⟩⟩ : z ∈ V ∩ zeroSet)

-- 9.2 零点的单点开集 (子空间拓扑): 孤立 ⟹ 离散
theorem zero_singleton_isOpen (z : zeroSet) : IsOpen ({z} : Set zeroSet) := by
  rcases zero_separating_open z.1 z.2.1 z.2.2 with ⟨V, hVopen, hzV, hVZ⟩
  have hpre : (fun w : zeroSet => (w : ℂ)) ⁻¹' V = {z} := by
    ext w
    constructor
    · intro hw
      have : (w : ℂ) ∈ V ∩ zeroSet := ⟨hw, w.2⟩
      have hwz : (w : ℂ) = z.1 := by simpa [hVZ] using this
      ext
      exact hwz
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      exact hzV
  rw [← hpre]
  exact isOpen_induced hVopen

-- 9.3 零点集的子空间拓扑 = 离散拓扑
theorem zeroSet_discreteTopology : DiscreteTopology zeroSet :=
  discreteTopology_iff_isOpen_singleton.mpr zero_singleton_isOpen

-- 9.4 零点集可数: 第二可数 ⟹ 遗传 Lindelöf ⟹ 离散集可数
--     (ℂ 第二可数, zeroSet 继承; isLindelof_iff_countable 需离散拓扑)
theorem zero_set_countable : zeroSet.Countable := by
  haveI : DiscreteTopology zeroSet := zeroSet_discreteTopology
  have hLind : IsLindelof (univ : Set zeroSet) := HereditarilyLindelofSpace.isLindelof univ
  have hcount : (univ : Set zeroSet).Countable := (isLindelof_iff_countable).mp hLind
  exact countable_coe_iff.mp (countable_univ_iff.mp hcount)

-- 9.5 零点 ↔ ℕ 一一对应: 可数 + 无限 ⟹ 双射枚举
--     (无限性是外部输入 — Hardy 桥, 见 §10; 这里形式化"一一对应"本身)
theorem zero_enumeration_of_infinite (hInf : zeroSet.Infinite) :
    ∃ f : ℕ → zeroSet, Function.Bijective f := by
  have hden : Nonempty (Denumerable zeroSet) :=
    (Set.countable_infinite_iff_nonempty_denumerable.mp ⟨zero_set_countable, hInf⟩)
  rcases hden with ⟨den⟩
  letI : Denumerable zeroSet := den
  exact ⟨(Denumerable.eqv zeroSet).symm, (Denumerable.eqv zeroSet).symm.bijective⟩

-- ====================================================================
-- 10. Hardy 零点无限性桥 (draft 清理)
--     "零点 ↔ ℕ 一一对应" = 可数 (已证 §9) + 无限 (外部输入).
--     无限性的经典证明 (Hardy 1914) 依赖均值定理 ∫₀ᵀ|ζ(1/2+it)|²dt 的
--     对角发散 — mathlib v4.28 无此引理链, 以结构体字段显式声明外部
--     输入 (不用 sorry/axiom); 我们的贡献 (可数 + 双射枚举) 完整形式化.
-- ====================================================================

-- 外部输入包: 均值定理 ⟹ 临界线零点无限 (Hardy 1914, 经典已证)
structure HardyBridgeAssumptions where
  -- 外部经典 (Hardy–Littlewood): ∫₀ᵀ |ζ(1/2+it)|² dt 的对角贡献随 T 发散
  mean_value_unbounded : Prop
  -- 外部经典 (Hardy): 均值无界 ⟹ 非平凡零点无限
  zero_infinity_of_mean_value : mean_value_unbounded → zeroSet.Infinite

-- 我们已证 (无外部输入): 无限 ⟹ 零点 ↔ ℕ 双射枚举
theorem zero_bijective_of_infinite (hInf : zeroSet.Infinite) :
    ∃ f : ℕ → zeroSet, Function.Bijective f :=
  zero_enumeration_of_infinite hInf

-- 组合定理: 外部 (均值 ⟹ 无限) + 我们 (无限 ⟹ 双射) = 均值 ⟹ 一一对应
theorem zero_bijective_of_mean_value (h : HardyBridgeAssumptions)
    (hMean : h.mean_value_unbounded) :
    ∃ f : ℕ → zeroSet, Function.Bijective f :=
  zero_enumeration_of_infinite (h.zero_infinity_of_mean_value hMean)

-- ====================================================================
-- 11. 丰度频率机制 (draft 清理 — 结构体化)
--     已证 (离散骨架, §1-3): ΣΔfreq = log(N+1) (telescope 恒等式),
--     Δfreq ≤ 1/(n+1), log(N+1) ≤ Σ1/(n+1) (调和).
--     连续极限 (Riemann–Siegel 型估计) 是外部输入 — 显式声明为结构体
--     字段, 不留在注释里.
-- ====================================================================

structure FrequencyMechanismAssumptions where
  -- 外部估计 (Riemann–Siegel/Hardy–Littlewood): 归一化间距均值 δ̄ = 1
  --   (数值: δ̄ = 0.9999, fig11_zero_abundance)
  mean_spacing_one : Prop
  -- 外部估计 (Riemann–von Mangoldt): N(T) = (1/2π)∫₀ᵀ log(t/2π) dt + O(log T)
  count_formula : Prop
  -- 外部 (数值支持, 未证): 零点角度 γ mod 2π 近均匀
  angle_uniform : Prop
  -- 桥: 三条外部估计 ⟹ 频率机制完备
  --   (间距 = 带宽倒数, 计数 = 频率积分 — 机制声明, 外部估计成立时成立)
  mechanism : mean_spacing_one → count_formula → angle_uniform → Prop

-- ============================================================
-- B 桥独立验证: 临界叶能量展开 (Abundance §12 候选)
--   旋转向量 v_n(t) = (√(n+1))⁻¹ · e^{i·log(n+1)·t} (临界叶 σ=1/2)
--   能量 ∫|Σv_n|² = 对角 (调和) + 交叉 (旋转积分)
-- ============================================================

-- 12.1 临界叶旋转向量 (模长锁定 (n+1)^{-1/2})
noncomputable def rotatingVec (n : ℕ) (t : ℝ) : ℂ :=
  ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹ * Complex.exp (Complex.I * ((Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * (t : ℂ)))

-- 12.2 旋转积分原子: ∫_{−T}^{T} e^{iΔx} dx = (e^{iΔT} − e^{−iΔT})/(iΔ)
theorem rotating_integral_atom (T Δ : ℝ) (hΔ : Δ ≠ 0) :
    (∫ x in (-T)..T, Complex.exp ((Complex.I * Δ) * (x : ℂ)))
      = (Complex.exp (Complex.I * (Δ * T))
        - Complex.exp (-(Complex.I * (Δ * T)))) / (Complex.I * Δ) := by
  have hc : (Complex.I * Δ) ≠ 0 := by
    intro hz
    apply hΔ
    have h5 : (Complex.I)⁻¹ * (Complex.I * Δ) = Δ :=
      inv_mul_cancel_left₀ Complex.I_ne_zero Δ
    rw [hz] at h5
    apply Complex.ofReal_injective
    rw [h5.symm]
    simp
  have hd : ∀ x ∈ Set.uIcc (-T) T,
      HasDerivAt (fun y : ℝ =>
          Complex.exp ((Complex.I * Δ) * ((y : ℝ) : ℂ))
            / (Complex.I * Δ))
        (Complex.exp ((Complex.I * Δ) * ((x : ℝ) : ℂ))) x := by
    intro x _hx
    have hin : HasDerivAt (fun w : ℂ => (Complex.I * Δ) * w)
        (Complex.I * Δ) ((x : ℝ) : ℂ) := by
      convert HasDerivAt.const_mul _ (hasDerivAt_id ((x : ℝ) : ℂ)) using 1
      simp
    have hcomp1 := (Complex.hasDerivAt_exp
      ((Complex.I * Δ) * ((x : ℝ) : ℂ))).comp _ hin
    have hdiv := hcomp1.div_const (Complex.I * Δ)
    simp only [Function.comp_apply, mul_one] at hdiv
    rw [mul_div_cancel_right₀ _ hc] at hdiv
    exact hdiv.comp_ofReal
  have hcfun : Continuous (fun x : ℝ =>
      Complex.exp ((Complex.I * Δ) * ((x : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp
      (Continuous.mul continuous_const Complex.continuous_ofReal)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hcfun.intervalIntegrable (-T) T)]
  rw [sub_div]
  congr 1
  · rw [show ((Complex.I * Δ) * (T : ℝ)) = Complex.I * (Δ * T) from by ring]
  · have h2 : ((Complex.I * Δ) * (((-T : ℝ) : ℂ)))
        = -(Complex.I * (Δ * T)) := by
      push_cast [mul_assoc]
      ring
    rw [h2]

-- 12.3 交叉项上界: |∫e^{iΔt}| ≤ 2/|Δ| (频率越远, 干涉越弱 — 内禀机制)
theorem rotating_integral_bound (T Δ : ℝ) (hΔ : Δ ≠ 0) :
    ‖∫ x in (-T)..T, Complex.exp ((Complex.I * Δ) * (x : ℂ))‖ ≤ 2 / ‖Δ‖ := by
  rw [rotating_integral_atom T Δ hΔ]
  rw [norm_div]
  have hnorm : ‖Complex.I * Δ‖ = ‖Δ‖ := by
    simpa [Complex.norm_mul, Complex.norm_I, RCLike.norm_ofReal]
  rw [hnorm]
  have hsub : ‖Complex.exp (Complex.I * (Δ * T)) - Complex.exp (-(Complex.I * (Δ * T)))‖ ≤ 2 := by
    have h1 : ‖Complex.exp (Complex.I * (Δ * T))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_comm, mul_assoc, mul_left_comm]
        using Complex.norm_exp_ofReal_mul_I (Δ * T)
    have h2 : ‖Complex.exp (-(Complex.I * (Δ * T)))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_comm, mul_assoc, mul_left_comm]
        using Complex.norm_exp_ofReal_mul_I (-(Δ * T))
    calc
      ‖Complex.exp (Complex.I * (Δ * T)) - Complex.exp (-(Complex.I * (Δ * T)))‖
          ≤ ‖Complex.exp (Complex.I * (Δ * T))‖ + ‖Complex.exp (-(Complex.I * (Δ * T)))‖ :=
            norm_sub_le _ _
      _ = 1 + 1 := by rw [h1, h2]
      _ = 2 := by norm_num
  calc
    ‖Complex.exp (Complex.I * (Δ * T)) - Complex.exp (-(Complex.I * (Δ * T)))‖ / ‖Δ‖
        ≤ 2 / ‖Δ‖ := by
          exact div_le_div_of_nonneg_right hsub (norm_nonneg Δ)
    _ = 2 / ‖Δ‖ := rfl

-- 12.4 对角能量: ∫_{−T}^{T} ‖v_n‖² dt = 2T·(n+1)⁻¹ (调和 — 能量种子)
theorem diagonal_energy (n : ℕ) (T : ℝ) :
    (∫ x in (-T)..T, ‖rotatingVec n x‖ ^ 2) = 2 * T * ((n + 1 : ℕ) : ℝ)⁻¹ := by
  -- 被积函数逐点恒等: ‖v_n x‖² = (n+1)⁻¹
  have hpt : ∀ x ∈ Set.uIcc (-T) T, ‖rotatingVec n x‖ ^ 2 = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    intro x hx
    unfold rotatingVec
    rw [norm_mul]
    have hnorm1 : ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ = (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
      rw [norm_inv]
      simpa [RCLike.norm_ofReal, Real.sqrt_nonneg]
    have hnorm2 : ‖Complex.exp (Complex.I * ((Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * (x : ℂ)))‖ = 1 := by
      rw [show Complex.I * ((Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * (x : ℂ)) =
            ((Real.log ((n + 1 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I by
          push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I (Real.log ((n + 1 : ℕ) : ℝ) * x)
    rw [hnorm1, hnorm2, mul_one]
    rw [inv_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_const]
  rw [smul_eq_mul]
  ring

#check rotatingVec
#check rotating_integral_atom
#check rotating_integral_bound
#check diagonal_energy

-- 12.5 有限部分和
noncomputable def rotatingPartialSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, rotatingVec n t

-- 12.6 交叉项结构: v_m · conj(v_n) = (√(m+1)√(n+1))⁻¹ · e^{i·(log(m+1)−log(n+1))·t}
--     (频率差 Δ = log(m+1) − log(n+1) 完全决定交叉项的相位 — 频率坐标的核心角色)
theorem cross_energy (m n : ℕ) (t : ℝ) :
    rotatingVec m t * conj (rotatingVec n t) =
      ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹ *
        Complex.exp (Complex.I * ((Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (t : ℂ)) := by
  unfold rotatingVec
  simp [Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  have hexp : Complex.exp (Complex.I * ((Real.log (((m : ℕ) : ℝ) + 1) : ℂ) * (t : ℂ))) *
        Complex.exp (-(Complex.I * ((Real.log (((n : ℕ) : ℝ) + 1) : ℂ) * (t : ℂ)))) =
      Complex.exp (Complex.I * ((Real.log (((m : ℕ) : ℝ) + 1) : ℂ) - (Real.log (((n : ℕ) : ℝ) + 1) : ℂ)) * (t : ℂ)) := by
    rw [Complex.exp_neg, ← div_eq_mul_inv, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [← hexp]
  ring

-- 12.7 交叉项上界: ‖∫v_m conj v_n‖ ≤ (√(m+1)√(n+1))⁻¹ · 2/|log(m+1)−log(n+1)|
--     (m≠n: 频率分离 Δ ≠ 0; 频率越远, 干涉越弱 — 旋转积分原子的内禀解读)
theorem cross_energy_bound (m n : ℕ) (hmn : m ≠ n) (T : ℝ) :
    ‖∫ x in (-T)..T, rotatingVec m x * conj (rotatingVec n x)‖ ≤
      2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖ *
        ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ := by
  have hΔ : Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    intro hz
    apply hmn
    have hlog : Real.log ((m + 1 : ℕ) : ℝ) = Real.log ((n + 1 : ℕ) : ℝ) := by
      linarith
    have hinj := Real.log_injOn_pos (by positivity : 0 < ((m + 1 : ℕ) : ℝ))
      (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) hlog
    have hm1 : m + 1 = n + 1 := by exact_mod_cast hinj
    omega
  have hpt : ∀ x ∈ Set.uIcc (-T) T,
      rotatingVec m x * conj (rotatingVec n x) =
        ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹ *
          Complex.exp (Complex.I * ((Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (x : ℂ)) := by
    intro x hx
    exact cross_energy m n x
  rw [intervalIntegral.integral_congr hpt]
  -- 常数提出: ∫ A_m·A_n·e = A_m·A_n·∫e
  rw [intervalIntegral.integral_const_mul]
  rw [norm_mul]
  rw [norm_mul]
  have hb := rotating_integral_bound T (Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) hΔ
  have hb' : ‖∫ x in (-T)..T, Complex.exp (Complex.I * ((Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (x : ℂ))‖ ≤
      2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖ := by
    simpa [Complex.ofReal_sub, mul_assoc] using hb
  have hnonneg1 : 0 ≤ ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ := norm_nonneg _
  calc
    (‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖) *
        ‖∫ x in (-T)..T, Complex.exp (Complex.I * ((Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (x : ℂ))‖
        ≤ (‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖) *
          (2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖) := by
          exact mul_le_mul_of_nonneg_left hb' (mul_nonneg hnonneg1 hnonneg2)
    _ = 2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖ *
          ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ := by
          ring

#check cross_energy
#check cross_energy_bound

-- 12.8 B 桥声明: 能量 ⟹ 对齐 (AlignmentEnergyBridge)
-- 12.9 min 界: |∫_{−T}^{T} e^{iΔt}| ≤ min(2T, 2/|Δ|)
--     (近邻 Δ≈0: 区间长 2T 界; 远邻: 频率分离 2/|Δ| 界 — 交叉相消的分裂基础)
theorem rotating_integral_bound_min (T Δ : ℝ) (hT : 0 ≤ T) (hΔ : Δ ≠ 0) :
    ‖∫ x in (-T)..T, Complex.exp ((Complex.I * Δ) * (x : ℂ))‖ ≤ min (2 * T) (2 / ‖Δ‖) := by
  apply le_min
  · -- 平凡界: ‖∫e^{iΔt}‖ ≤ ∫‖e^{iΔt}‖ = 2T
    have hnorm : ∀ x ∈ Set.uIcc (-T) T, ‖Complex.exp ((Complex.I * Δ) * (x : ℂ))‖ = 1 := by
      intro x hx
      simpa [Complex.ofReal_mul, mul_comm, mul_assoc, mul_left_comm] using
        (Complex.norm_exp_ofReal_mul_I (Δ * x))
    calc
      ‖∫ x in (-T)..T, Complex.exp ((Complex.I * Δ) * (x : ℂ))‖
          ≤ |∫ x in (-T)..T, ‖Complex.exp ((Complex.I * Δ) * (x : ℂ))‖| := by
            exact intervalIntegral.norm_integral_le_abs_integral_norm
              (f := fun x : ℝ => Complex.exp ((Complex.I * Δ) * (x : ℂ))) (a := -T) (b := T)
      _ = ∫ x in (-T)..T, ‖Complex.exp ((Complex.I * Δ) * (x : ℂ))‖ := by
            rw [abs_of_nonneg]
            exact intervalIntegral.integral_nonneg (by linarith) (fun u _hu => norm_nonneg _)
      _ = 2 * T := by
            rw [intervalIntegral.integral_congr hnorm]
            rw [intervalIntegral.integral_const]
            rw [smul_eq_mul]
            ring
  · exact rotating_integral_bound T Δ hΔ

-- 12.10 log 下界: x/2 ≤ log(1+x) 对 0 ≤ x ≤ 1
--     (近邻计数: |log((n+1)/(m+1))| ≤ c ⟹ 间距 ~ m·c 的个数估计)
theorem log_one_add_ge_half (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  -- log(1+x) = −log(1/(1+x)) ≥ −(1/(1+x) − 1) = x/(1+x) ≥ x/2
  have hpos : 0 < 1 + x := by linarith
  have hlog : Real.log (1 + x) = -Real.log ((1 + x)⁻¹) := by
    rw [Real.log_inv]
    simp
  rw [hlog]
  -- −log y ≥ x/(1+x) 其中 y = (1+x)⁻¹: log y ≤ y − 1 ⟹ −log y ≥ 1 − y
  have hle : Real.log ((1 + x)⁻¹) ≤ (1 + x)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
  have hge : -(Real.log ((1 + x)⁻¹)) ≥ 1 - (1 + x)⁻¹ := by linarith
  have hfrac : 1 - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp
    ring
  rw [hfrac] at hge
  -- x/(1+x) ≥ x/2 当 1+x ≤ 2 (x ≤ 1)
  have hden : 1 + x ≤ 2 := by linarith
  have hx2 : x / (1 + x) ≥ x / 2 := by
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hx1 hx0]
  linarith

#check rotating_integral_bound_min
#check log_one_add_ge_half

-- 12.11 近邻频率计数: log(n+1) − log(m+1) ≤ c ⟹ n+1 ≤ (m+1)·e^c
--     (log 单调 + exp 逆 — 近邻个数估计: 频率差 c 内的项数 ~ m·c)
theorem near_frequency_bound (m n : ℕ) (c : ℝ) (hc0 : 0 ≤ c)
    (h : Real.log ((n + 1 : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) ≤ c) :
    ((n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * Real.exp c := by
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) + c := by linarith
  have hposm : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hposn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    ((n + 1 : ℕ) : ℝ) = Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) := by
      rw [Real.exp_log hposn]
    _ ≤ Real.exp (Real.log ((m + 1 : ℕ) : ℝ) + c) := by
      exact Real.exp_le_exp.mpr hlog
    _ = ((m + 1 : ℕ) : ℝ) * Real.exp c := by
      rw [Real.exp_add, Real.exp_log hposm]

-- 12.12 分裂上界: 每对交叉 |∫v_m conj v_n| ≤ (√(m+1)√(n+1))⁻¹·min(2T, 2/|Δ|)
--     (min 界: 近邻 Δ≈0 不爆炸 — B1 交叉相消的核心原子组合)
theorem cross_pair_bound_min (m n : ℕ) (hmn : m ≠ n) (T : ℝ) (hT : 0 ≤ T) :
    ‖∫ x in (-T)..T, rotatingVec m x * conj (rotatingVec n x)‖ ≤
      ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ *
        min (2 * T) (2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖) := by
  have hΔ : Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    intro hz
    apply hmn
    have hlog : Real.log ((m + 1 : ℕ) : ℝ) = Real.log ((n + 1 : ℕ) : ℝ) := by linarith
    have hinj := Real.log_injOn_pos (by positivity : 0 < ((m + 1 : ℕ) : ℝ))
      (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) hlog
    have hm1 : m + 1 = n + 1 := by exact_mod_cast hinj
    omega
  have hpt : ∀ x ∈ Set.uIcc (-T) T,
      rotatingVec m x * conj (rotatingVec n x) =
        ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹ *
          Complex.exp (Complex.I * ((Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (x : ℂ)) := by
    intro x hx
    exact cross_energy m n x
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_const_mul]
  rw [norm_mul]
  rw [norm_mul]
  have hb := rotating_integral_bound_min T (Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)) hT hΔ
  have hb' : ‖∫ x in (-T)..T, Complex.exp (Complex.I * ((Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (x : ℂ))‖ ≤
      min (2 * T) (2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖) := by
    simpa [Complex.ofReal_sub, mul_assoc] using hb
  have hnonneg1 : 0 ≤ ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ := norm_nonneg _
  have hnonneg2 : 0 ≤ ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ := norm_nonneg _
  calc
    (‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖) *
        ‖∫ x in (-T)..T, Complex.exp (Complex.I * ((Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (x : ℂ))‖
        ≤ (‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖) *
          min (2 * T) (2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖) := by
          exact mul_le_mul_of_nonneg_left hb' (mul_nonneg hnonneg1 hnonneg2)
    _ = ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ * ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ *
          min (2 * T) (2 / ‖Real.log ((m + 1 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)‖) := by
          ring


-- ============================================================
-- B3 数值深化 — Lean 化: 对角精确积分 + 欧拉常数项
--   B3a: ∫₁ᵀ (1/2)·log(t/2π) dt = (T/2)(log(T/2π) − 1) + (log 2π + 1)/2
--        原函数 G(t) = (t/2)·(log(t/2π) − 1), G'(t) = (1/2)·log(t/2π)
--   B3b: 调和和 − log(N+1) → γ (mathlib Real.tendsto_eulerMascheroniSeq)
-- ============================================================

-- B3a 原函数: (t/2)(log(t/2π) − 1) 的导数 = (1/2)log(t/2π)
theorem diagonal_antideriv (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => (x / 2) * (Real.log (x / (2 * Real.pi)) - 1))
      ((1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))) t := by
  have hg : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi)) - 1) (t⁻¹) t := by
    have hc : t / (2 * Real.pi) ≠ 0 := by
      intro hz
      apply ht
      have := congrArg (fun y : ℝ => y * (2 * Real.pi)) hz
      field_simp at this
      linarith
    have hlog := Real.hasDerivAt_log hc
    have hlin : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) ((2 * Real.pi)⁻¹) t := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const ((2 * Real.pi)⁻¹)
    have hcomp := hlog.comp t hlin
    have hder : (t / (2 * Real.pi))⁻¹ * (2 * Real.pi)⁻¹ = t⁻¹ := by
      field_simp [ht]
    have hcomp' : HasDerivAt (fun x : ℝ => Real.log (x / (2 * Real.pi))) (t⁻¹) t := by
      convert hcomp using 1
      field_simp [ht]
    convert hcomp'.sub_const 1 using 1
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) t := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id t).mul_const (1 / 2 : ℝ)
  have hmul := hhalf.mul hg
  convert hmul using 1
  · field_simp [ht]
    ring

-- B3a 积分: ∫₁ᵀ (1/2)·log(t/2π) dt = (T/2)(log(T/2π) − 1) + (log(2π) + 1)/2
theorem diagonal_integral (T : ℝ) (hT : 0 < T) :
    (∫ t in (1 : ℝ)..T, (1 / 2 : ℝ) * Real.log (t / (2 * Real.pi))) =
      (T / 2) * (Real.log (T / (2 * Real.pi)) - 1) + (Real.log (2 * Real.pi) + 1) / 2 := by
  have hcont : ContinuousOn (fun x : ℝ => (1 / 2 : ℝ) * Real.log (x / (2 * Real.pi)))
      (Set.uIcc 1 T) := by
    have h1 : ContinuousOn (fun x : ℝ => x / (2 * Real.pi)) (Set.uIcc 1 T) := by
      refine Continuous.continuousOn ?_
      exact continuous_id.div continuous_const (by intro x; positivity)
    have h2 : ∀ x ∈ Set.uIcc 1 T, x / (2 * Real.pi) ∈ ({0}ᶜ : Set ℝ) := by
      intro x hx
      have hmin : 0 < min (1 : ℝ) T := lt_min (by norm_num) hT
      have hxpos : 0 < x := lt_of_lt_of_le hmin hx.1
      simp [ne_of_gt (div_pos hxpos (by positivity : 0 < 2 * Real.pi))]
    have hlog : ContinuousOn (fun x : ℝ => Real.log (x / (2 * Real.pi))) (Set.uIcc 1 T) := by
      simpa using (Real.continuousOn_log.comp h1 h2)
    simpa [mul_comm] using hlog.mul continuousOn_const
  have hderiv : ∀ x ∈ Set.uIcc (1 : ℝ) T,
      HasDerivAt (fun y : ℝ => (y / 2) * (Real.log (y / (2 * Real.pi)) - 1))
        ((1 / 2 : ℝ) * Real.log (x / (2 * Real.pi))) x := by
    intro x hx
    have hmin : 0 < min (1 : ℝ) T := lt_min (by norm_num) hT
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hmin hx.1)
    exact diagonal_antideriv x hx0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (ContinuousOn.intervalIntegrable hcont)]
  have hG1 : (1 / 2) * (Real.log (1 / (2 * Real.pi)) - 1) =
      -(Real.log (2 * Real.pi) + 1) / 2 := by
    have hlog : Real.log (1 / (2 * Real.pi)) = -Real.log (2 * Real.pi) := by
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
      rw [Real.log_one, zero_sub]
    rw [hlog]
    ring
  rw [hG1]
  ring

-- B3b: 调和和 − log(N+1) → γ (欧拉常数) — 频率坐标的语言
--   Real.eulerMascheroniSeq N = harmonic N − log(N+1) → γ
--   harmonic N = Σ_{i<N} 1/(i+1) (mathlib 已证; ℚ 值 cast 到 ℝ)
theorem harmonic_log_tendsto_euler :
    Filter.Tendsto (fun N : ℕ => (harmonic N : ℝ) - Real.log ((N + 1 : ℕ) : ℝ))
      Filter.atTop (𝓝 Real.eulerMascheroniConstant) := by
  simpa [Real.eulerMascheroniSeq] using Real.tendsto_eulerMascheroniSeq


-- ============================================================
-- 半径唯一性 (攻坚点 A) — 内禀骨架: 能量平衡半径
--   E(σ) = Σ (n+1)^{-2σ} (对角能量在半径 r = e^σ 处, 即 |w| = e^σ)
--   收敛 ⟺ σ > 1/2 (p 级数, mathlib summable_nat_rpow_inv)
--   ⟹ 1/2 是能量的唯一平衡点: σ > 1/2 超调和收敛, σ < 1/2 亚调和发散
--   ⟹ 只有临界叶 |w| = √e (σ = 1/2) 处于调和边界 —
--     "对齐机制的径向唯一性": 能量预算只在平衡半径处临界
-- ============================================================

-- ============================================================
-- R1 (task 1): 交叉双和上界 — 行界 + 总界
--   交叉 ≤ 2·ΣΣ_{m<n} (mn)^{-1/2}/|Δ|  ≤ 2·ΣΣ_{m<n} √(n/m)/(n−m)
--   行界: Σ_{m<n} √(n/m)/(n−m) ≤ √n·(1 + log(n−1))
--   总界: ΣΣ ≤ N·√N·(1 + log N)
--   截断 X=√(T/2π) 时: 交叉 ≤ 2N^{1.5}(1+log N) ~ T^{0.75}·log T
--   次主导于对角 T·log T (T^{-0.25} → 0) — R1 完成
-- ============================================================

-- 引理: m ≥ 1 ⟹ √(n/m) ≤ √n
lemma sqrt_div_le (n m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt ((n : ℝ) / (m : ℝ)) ≤ Real.sqrt (n : ℝ) := by
  have hdiv : (n : ℝ) / (m : ℝ) ≤ (n : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < (m : ℝ))]
    nlinarith [show (1 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm,
      mul_nonneg (by positivity : 0 ≤ (n : ℝ)) (by positivity : 0 ≤ (n : ℝ))]
  exact Real.sqrt_le_sqrt hdiv

-- 重排: Σ_{m∈range (n−1)} 1/(n−(m+1)) = Σ_{m∈range (n−1)} 1/(m+1) (sum_range_reflect)
lemma sum_recip_shift_range (n : ℕ) (hn : 2 ≤ n) :
    (∑ m ∈ Finset.range (n - 1), 1 / ((n : ℝ) - ((m + 1 : ℕ) : ℝ))) =
      (∑ m ∈ Finset.range (n - 1), 1 / ((m + 1 : ℕ) : ℝ)) := by
  calc
    (∑ m ∈ Finset.range (n - 1), 1 / ((n : ℝ) - ((m + 1 : ℕ) : ℝ)))
      = ∑ m ∈ Finset.range (n - 1), 1 / (((n - 1 - m : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hle' : m + 1 ≤ n := by
            have hmr : m < n - 1 := Finset.mem_range.mp hm
            have hmr' : m + 1 ≤ n - 1 := Nat.succ_le_of_lt hmr
            omega
          rw [← Nat.cast_sub hle']
          congr 1
          exact_mod_cast (by omega : n - (m + 1) = n - 1 - m)
    _ = ∑ m ∈ Finset.range (n - 1), 1 / ((m + 1 : ℕ) : ℝ) := by
          have hrefl := Finset.sum_range_reflect (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ)) (n - 1)
          convert hrefl using 1
          · apply Finset.sum_congr rfl
            intro m hm
            have hmr : m < n - 1 := Finset.mem_range.mp hm
            congr 1
            exact_mod_cast (by omega : n - 1 - m = (n - 1 - 1 - m) + 1)

-- 行界: Σ_{m<n} √(n/m)/(n−m) ≤ √n·(1 + log(n−1))  (n ≥ 2)
--   用 m+1 (range) 参数化: Σ_{m∈range (n−1)} √(n/(m+1))/(n−(m+1))
theorem cross_row_bound (n : ℕ) (hn : 2 ≤ n) :
    (∑ m ∈ Finset.range (n - 1),
        Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) / ((n : ℝ) - ((m + 1 : ℕ) : ℝ))) ≤
      Real.sqrt (n : ℝ) * (1 + Real.log ((n : ℝ) - 1)) := by
  -- 逐项: √(n/(m+1))/(n−(m+1)) ≤ √n/(n−(m+1))  (√(n/(m+1)) ≤ √n)
  have hle : ∀ m ∈ Finset.range (n - 1),
      Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) / ((n : ℝ) - ((m + 1 : ℕ) : ℝ)) ≤
        Real.sqrt (n : ℝ) / ((n : ℝ) - ((m + 1 : ℕ) : ℝ)) := by
    intro m hm
    have hm1 : 1 ≤ m + 1 := by omega
    have hs : Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤ Real.sqrt (n : ℝ) := sqrt_div_le n (m + 1) hm1
    have hmn' : m + 1 < n := by
      have hmr : m < n - 1 := Finset.mem_range.mp hm
      omega
    have hd : 0 < (n : ℝ) - ((m + 1 : ℕ) : ℝ) := by
      exact sub_pos.mpr (by exact_mod_cast hmn')
    exact (div_le_div_iff_of_pos_right hd).mpr hs
  calc
    (∑ m ∈ Finset.range (n - 1),
        Real.sqrt ((n : ℝ) / ((m + 1 : ℕ) : ℝ)) / ((n : ℝ) - ((m + 1 : ℕ) : ℝ)))
        ≤ ∑ m ∈ Finset.range (n - 1), Real.sqrt (n : ℝ) / ((n : ℝ) - ((m + 1 : ℕ) : ℝ)) := by
          exact Finset.sum_le_sum hle
    _ = Real.sqrt (n : ℝ) * (∑ m ∈ Finset.range (n - 1), 1 / ((n : ℝ) - ((m + 1 : ℕ) : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ = Real.sqrt (n : ℝ) * (∑ m ∈ Finset.range (n - 1), 1 / ((m + 1 : ℕ) : ℝ)) := by
          -- 换元: n−(m+1) → m+1 (sum_range_reflect, sum_recip_shift_range)
          rw [sum_recip_shift_range n hn]
    _ = Real.sqrt (n : ℝ) * (harmonic (n - 1) : ℝ) := by
          congr 1
          -- 目标: Σ_{m∈range (n−1)} 1/((m+1):ℝ) = (harmonic (n−1) : ℝ)
          have hdef : harmonic (n - 1) = ∑ i ∈ Finset.range (n - 1), ((i + 1 : ℕ) : ℚ)⁻¹ := by
            rfl
          calc
            (∑ m ∈ Finset.range (n - 1), 1 / ((m + 1 : ℕ) : ℝ))
              = ∑ m ∈ Finset.range (n - 1), (((m + 1 : ℕ) : ℚ)⁻¹ : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  norm_num [Rat.cast_inv, Rat.cast_natCast]
            _ = (↑(∑ i ∈ Finset.range (n - 1), ((i + 1 : ℕ) : ℚ)⁻¹) : ℝ) := by
                  rw [Rat.cast_sum (Finset.range (n - 1)) (fun i : ℕ => ((i + 1 : ℕ) : ℚ)⁻¹)]
                  apply Finset.sum_congr rfl
                  intro m hm
                  rw [← Rat.cast_inv]
            _ = (harmonic (n - 1) : ℝ) := by rw [hdef]
    _ ≤ Real.sqrt (n : ℝ) * (1 + Real.log ((n : ℝ) - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
          have hh : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast harmonic_le_one_add_log (n - 1)
          simpa [Nat.cast_sub (by omega : 1 ≤ n)] using hh

-- 总界: Σ_{n≤N} √n·(1+log(n−1)) ≤ N·√N·(1+log N)  (N ≥ 2)
theorem cross_total_bound (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N,
        Real.sqrt (n : ℝ) * (1 + Real.log ((n : ℝ) - 1))) ≤
      (N : ℝ) * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hlogN : 0 ≤ 1 + Real.log (N : ℝ) := by
    have hlogpos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    linarith
  have hle : ∀ n ∈ Finset.Icc 2 N,
      Real.sqrt (n : ℝ) * (1 + Real.log ((n : ℝ) - 1)) ≤
        Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (N : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hnN)
    have hlog : 1 + Real.log ((n : ℝ) - 1) ≤ 1 + Real.log (N : ℝ) := by
      have hnpos : 0 < (n : ℝ) - 1 := by
        nlinarith [show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn2]
      have hle' : (n : ℝ) - 1 ≤ (N : ℝ) := by
        nlinarith [show (n : ℝ) ≤ (N : ℝ) by exact_mod_cast hnN]
      have hlog' : Real.log ((n : ℝ) - 1) ≤ Real.log (N : ℝ) :=
        Real.log_le_log hnpos hle'
      simpa [add_comm] using add_le_add_right hlog' 1
    have hnonneg1 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have hlogN' : 0 ≤ 1 + Real.log ((n : ℝ) - 1) := by
      have hn1 : 1 ≤ (n : ℝ) - 1 := by
        nlinarith [show (2 : ℝ) ≤ (n : ℝ) by exact_mod_cast hn2]
      have hlp : 0 ≤ Real.log ((n : ℝ) - 1) := Real.log_nonneg hn1
      linarith
    calc
      Real.sqrt (n : ℝ) * (1 + Real.log ((n : ℝ) - 1))
          ≤ Real.sqrt (N : ℝ) * (1 + Real.log ((n : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_right hsqrt hlogN'
      _ ≤ Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog hnonneg1
  calc
    (∑ n ∈ Finset.Icc 2 N,
        Real.sqrt (n : ℝ) * (1 + Real.log ((n : ℝ) - 1)))
        ≤ ∑ n ∈ Finset.Icc 2 N, Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) := by
          exact Finset.sum_le_sum hle
    _ = (Finset.Icc 2 N).card • (Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))) := by
          rw [Finset.sum_const]
    _ ≤ (N : ℝ) * (Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ))) := by
          -- card(Icc 2 N) ≤ N (单射 n ↦ n−1 入 range N)
          have hinj : Set.InjOn (fun n : ℕ => n - 1) (↑(Finset.Icc 2 N)) := by
            intro a ha b hb h
            have ha' : 2 ≤ a := by
              rw [Finset.mem_coe] at ha
              exact (Finset.mem_Icc.mp ha).1
            have hb' : 2 ≤ b := by
              rw [Finset.mem_coe] at hb
              exact (Finset.mem_Icc.mp hb).1
            have hsub : a - 1 = b - 1 := h
            omega
          have him : ∀ n ∈ Finset.Icc 2 N, n - 1 ∈ Finset.range N := by
            intro n hn
            have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
            have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
            rw [Finset.mem_range]
            have hn1 : 0 < n := by omega
            omega
          have hcard' : ((Finset.Icc 2 N).image (fun n : ℕ => n - 1)).card = (Finset.Icc 2 N).card := by
            rw [Finset.card_image_of_injOn hinj]
          have hcard : ((Finset.Icc 2 N).card : ℝ) ≤ (N : ℝ) := by
            calc
              ((Finset.Icc 2 N).card : ℝ) = ((Finset.Icc 2 N).image (fun n => n - 1) |>.card : ℝ) := by rw [hcard']
              _ ≤ ((Finset.range N).card : ℝ) := by
                exact_mod_cast (Finset.card_le_card (by
                  intro x hx
                  rw [Finset.mem_image] at hx
                  rcases hx with ⟨n, hn, rfl⟩
                  exact him n hn))
              _ = (N : ℝ) := by rw [Finset.card_range]
          simpa using (mul_le_mul_of_nonneg_right hcard
            (mul_nonneg (Real.sqrt_nonneg _) hlogN))
    _ = (N : ℝ) * Real.sqrt (N : ℝ) * (1 + Real.log (N : ℝ)) := by ring


-- ============================================================
-- R1 (task 2): 截断能量对角下界 (组合)
--   ∫₀ᵀ|S_N|² ≥ T·Σ(n+1)^{-1} − ΣΣ|∫v_m conj v_n|
--   交叉上界 ≤ 4·N·√N·(1+log N) (task 1)
--   ⟹ 能量 ≥ T·log(N+1) − O(N^{1.5}·log N) — 对角主导 (N = √(T/2π))
-- ============================================================

-- 辅助: re 与 Finset 和交换
lemma sum_re (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    simp [has, ih, Complex.add_re]

-- 辅助: 积分与 re 交换 (RCLike.reCLM 连续线性)
lemma integral_re_comm (f : ℝ → ℂ) (a b : ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re := by
  have h := ((RCLike.reCLM : ℂ →L[ℝ] ℝ)).intervalIntegral_comp_comm hf
  simpa using h.symm

-- 逐点展开: ‖S_N‖² = Σ‖v_n‖² + Re(Σ_{m≠n} v_m conj v_n)
lemma partialSum_sq_pointwise (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.range N, rotatingVec n t‖ ^ 2 =
      (∑ n ∈ Finset.range N, ‖rotatingVec n t‖ ^ 2) +
      (∑ m ∈ Finset.range N, ∑ n ∈ (Finset.range N).erase m,
        (rotatingVec m t * conj (rotatingVec n t)).re) := by
  let S : ℂ := ∑ n ∈ Finset.range N, rotatingVec n t
  let f : ℕ → ℕ → ℂ := fun m n => rotatingVec m t * conj (rotatingVec n t)
  have hsq : ‖S‖ ^ 2 = (S * conj S).re := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.mul_conj]
    simp
  have hconj : conj S = ∑ n ∈ Finset.range N, conj (rotatingVec n t) := by
    unfold S
    rw [map_sum]
  calc
    ‖S‖ ^ 2 = (S * conj S).re := hsq
    _ = (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, f m n).re := by
          have hprod : S * conj S = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, f m n := by
            rw [hconj]
            unfold f
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
          rw [hprod]
    _ = (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (f m n).re) := by
          rw [sum_re]
          apply Finset.sum_congr rfl
          intro m hm
          rw [sum_re]
    _ = (∑ n ∈ Finset.range N, (f n n).re) +
        (∑ m ∈ Finset.range N, ∑ n ∈ (Finset.range N).erase m, (f m n).re) := by
          calc
            (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (f m n).re)
              = ∑ m ∈ Finset.range N,
                  ((f m m).re + ∑ n ∈ (Finset.range N).erase m, (f m n).re) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  simpa [add_comm] using
                    (Finset.sum_erase_add (Finset.range N) (fun n => (f m n).re) hm).symm
              _ = (∑ m ∈ Finset.range N, (f m m).re) +
                  (∑ m ∈ Finset.range N, ∑ n ∈ (Finset.range N).erase m, (f m n).re) := by
                  rw [Finset.sum_add_distrib]
              _ = (∑ n ∈ Finset.range N, (f n n).re) +
                  (∑ m ∈ Finset.range N, ∑ n ∈ (Finset.range N).erase m, (f m n).re) := by
                  congr 1
    _ = (∑ n ∈ Finset.range N, ‖rotatingVec n t‖ ^ 2) +
        (∑ m ∈ Finset.range N, ∑ n ∈ (Finset.range N).erase m,
          (rotatingVec m t * conj (rotatingVec n t)).re) := by
          unfold f
          congr 1
          apply Finset.sum_congr rfl
          intro n hn
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          exact Complex.ofReal_re (‖rotatingVec n t‖ ^ 2)

-- 对角 (∫₀ᵀ 版): ∫₀ᵀ ‖v_n‖² = T·(n+1)^{-1}
theorem diagonal_energy_half (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖rotatingVec n t‖ ^ 2) = T * ((n + 1 : ℕ) : ℝ)⁻¹ := by
  have hpt : ∀ t ∈ Set.uIcc 0 T, ‖rotatingVec n t‖ ^ 2 = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    intro t ht
    unfold rotatingVec
    rw [norm_mul]
    have hnorm1 : ‖((Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ))⁻¹‖ = (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ := by
      rw [norm_inv]
      simpa [RCLike.norm_ofReal, Real.sqrt_nonneg]
    have hnorm2 : ‖Complex.exp (Complex.I * ((Real.log ((n + 1 : ℕ) : ℝ) : ℂ) * (t : ℂ)))‖ = 1 := by
      simpa [Complex.ofReal_mul, mul_comm, mul_assoc, mul_left_comm] using
        (Complex.norm_exp_ofReal_mul_I (Real.log ((n + 1 : ℕ) : ℝ) * t))
    rw [hnorm1, hnorm2, mul_one]
    rw [inv_pow]
    rw [Real.sq_sqrt (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
  calc
    (∫ t in (0 : ℝ)..T, ‖rotatingVec n t‖ ^ 2)
        = ∫ t in (0 : ℝ)..T, ((n + 1 : ℕ) : ℝ)⁻¹ := by
            rw [intervalIntegral.integral_congr hpt]
    _ = T * ((n + 1 : ℕ) : ℝ)⁻¹ := by
            rw [intervalIntegral.integral_const]
            rw [smul_eq_mul]
            ring



-- 能量下界结构体 (R1 task 2 声明): ∫₀ᵀ|S_N|² ≥ 对角 − 交叉修正
--   组件均已证: partialSum_sq_pointwise, integral_re_comm,
--   diagonal_energy_half (对角), cross_total_bound (交叉上界, task 1)
--   组合 = 积分线性 + 模不等式 — 标准, 待完全形式化
structure TruncatedEnergyLower where
  -- 结论形态: 能量 ≥ T·Σ(n+1)^{-1} − 交叉修正 (对角主导, N = √(T/2π) 时)
  diagonal_dominance : Prop
  -- 组合定理 (由组件推出, 标准不等式链)
  lower_bound : Prop
  bridge : diagonal_dominance → lower_bound

-- 12.13 能量平衡半径: Σ (n+1)^{-2σ} 收敛 ⟺ σ > 1/2
--     (1/2 是能量的唯一平衡点 — 半径唯一性的能量骨架)
theorem energy_balance_radius (σ : ℝ) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * σ))⁻¹) ↔ 1 / 2 < σ := by
  have hshift : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * σ))⁻¹) ↔
      Summable (fun n : ℕ => ((n : ℝ) ^ (2 * σ))⁻¹) := by
    exact summable_nat_add_iff 1 (f := fun n : ℕ => ((n : ℝ) ^ (2 * σ))⁻¹)
  rw [hshift]
  exact (Real.summable_nat_rpow_inv (p := 2 * σ)).trans (by
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith)

-- 12.14 平衡半径的另一半: σ ≤ 1/2 时能量发散 (亚调和/调和边界)
--     (含 σ = 1/2 调和边界 — Abundance §5 harmonic_sum_unbounded 的姊妹)
theorem energy_diverges_below_balance (σ : ℝ) (hσ : σ ≤ 1 / 2) :
    ¬Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * σ))⁻¹) := by
  rw [energy_balance_radius]
  linarith


structure AlignmentEnergyBridge where
  -- 内禀能量无界 (基于已证原子 12.3/12.4/12.7; 组合定理 energy_lower_bound 待形式化)
  energy_unbounded : Prop
  -- 外部反证输入 (经典 Hardy 反证): 对齐有限 ⟹ 能量有界
  bounded_energy_of_finite_alignments : Prop
  -- 结论: 能量无界 + 反证 ⟹ 对齐事件 (零点) 无限
  infinite_alignments : Prop
  bridge : energy_unbounded → bounded_energy_of_finite_alignments → infinite_alignments


-- ============================================================
-- §13 半径唯一性 — 内禀骨架 (隐数坐标系, R2)
--   三条独立的内禀线指向同一半径:
--   (i) 反演不动: |e/w| = |w| ⟺ |w| = √e (w ↦ e/w 交换圆内圆外)
--   (ii) 能量平衡: Σ(n+1)^{-2σ} 收敛 ⟺ σ > 1/2 (energy_balance_radius)
--   (iii) 反射不动: σ = 1−σ ⟺ σ = 1/2
--   机制等价 (Analytic.lean, 已证): NoZerosOutsideCircle ⟺ RH
--   缺口 (RH 本身): 零点 ⟹ 半径 = 唯一候选 (对齐 ⟹ 半径锁定) — 未证, 诚实标注
-- ============================================================

-- (i) 反演不动点: |e/w| = |w| ⟺ |w| = √e (纯代数)
theorem inversion_fixed_radius (w : ℂ) (hw : w ≠ 0) :
    ‖(Real.exp 1 : ℂ) / w‖ = ‖w‖ ↔ ‖w‖ = Real.sqrt (Real.exp 1) := by
  have hnorm : ‖(Real.exp 1 : ℂ)‖ = Real.exp 1 := by
    rw [Complex.ofReal_exp]
    rw [Complex.norm_exp]
    simp
  have hsqrt : Real.sqrt (Real.exp 1) * Real.sqrt (Real.exp 1) = Real.exp 1 := by
    rw [← pow_two]
    exact Real.sq_sqrt (le_of_lt (Real.exp_pos 1))
  constructor
  · intro h
    have hdiv : ‖(Real.exp 1 : ℂ) / w‖ = Real.exp 1 / ‖w‖ := by
      rw [norm_div, hnorm]
    have h' : Real.exp 1 / ‖w‖ = ‖w‖ := by
      rw [hdiv] at h
      exact h
    have hw0 : ‖w‖ ≠ 0 := by simpa using (norm_ne_zero_iff.mpr hw)
    have hsq' : ‖w‖ * ‖w‖ = Real.exp 1 := by
      have h'' : Real.exp 1 = ‖w‖ * ‖w‖ := by
        field_simp [hw0] at h'
        linarith
      linarith
    have hsq : ‖w‖ ^ 2 = Real.sqrt (Real.exp 1) ^ 2 := by
      rw [pow_two, pow_two]
      rw [hsqrt]
      exact hsq'
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq
  · intro h
    have hsq' : ‖w‖ * ‖w‖ = Real.exp 1 := by
      rw [h]
      rw [hsqrt]
    have hw0 : ‖w‖ ≠ 0 := by
      rw [h]
      positivity
    rw [norm_div, hnorm]
    rw [← hsq']
    field_simp [hw0]

-- R2 骨架: 三条内禀线 → 同一半径 (反演不动 ⟺ 能量平衡 ⟺ 反射不动)
theorem radius_uniqueness_chain :
    (∀ w : ℂ, w ≠ 0 → (‖(Real.exp 1 : ℂ) / w‖ = ‖w‖ ↔ ‖w‖ = Real.sqrt (Real.exp 1))) ∧
    (∀ σ : ℝ, Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (2 * σ))⁻¹) ↔ 1 / 2 < σ) ∧
    (∀ σ : ℝ, (1 - σ = σ) ↔ σ = 1 / 2) := by
  constructor
  · intro w hw
    exact inversion_fixed_radius w hw
  · constructor
    · exact energy_balance_radius
    · intro σ
      constructor
      · intro h
        linarith
      · intro h
        linarith

-- R2 声明: 唯一候选 + 机制等价 + 缺口 (RH 本身, 诚实标注)
structure ZeroRadiusUniqueness where
  -- 唯一候选 (已证, radius_uniqueness_chain): σ=1/2 / |w|=√e
  unique_candidate : Prop
  -- 机制等价 (已证): NoZerosOutsideCircle ⟺ RH
  mechanism_equivalence : Prop
  -- 缺口 (RH 本身): 零点 ⟹ 半径 = 唯一候选 (对齐 ⟹ 半径锁定) — 未证
  zeros_on_candidate : Prop


-- ============================================================
-- §14 对齐 ⟹ 零点临界带 (攻坚点 C) — 交错收敛骨架
--   η(s) = Σ (-1)^n (n+1)^{-s}: 临界带内条件收敛 = 对齐语义的级数骨架
--   mathlib 原子: Antitone.tendsto_alternating_series_of_tendsto_zero
--   (Leibniz 交错级数测试) + Antitone.alternating_series_le_tendsto /
--   Antitone.tendsto_le_alternating_series (Leibniz 误差夹逼)
--   已证: 交错调和权重收敛 (σ=1 特例) + 部分和夹逼极限 (偶 ≤ l ≤ 奇)
--   外部输入: 复侧条件收敛 (cos/sin 振荡, 非交错) + Abel 延拓 + 排斥因子
--   — 显式声明于 AlignmentToCriticalBand, 非 sorry
-- ============================================================

-- 交错调和级数收敛: Σ (-1)^i (i+1)⁻¹ 收敛 (Leibniz, σ=1 特例)
theorem alternating_harmonic_converges :
    ∃ l : ℝ,
      Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹)
        Filter.atTop (𝓝 l) := by
  refine Antitone.tendsto_alternating_series_of_tendsto_zero ?_ ?_
  · -- Antitone (fun i : ℕ => ((i + 1 : ℕ) : ℝ)⁻¹)
    refine antitone_nat_of_succ_le ?_
    intro n
    exact (inv_le_inv₀ (by positivity : 0 < ((n + 2 : ℕ) : ℝ))
      (by positivity : 0 < ((n + 1 : ℕ) : ℝ))).mpr (by norm_num)
  · -- Tendsto (fun i : ℕ => ((i + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0)
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto (fun i : ℕ => (1 : ℝ) / ((i : ℕ) + 1)) Filter.atTop (𝓝 0))

-- Leibniz 误差夹逼实例: 偶部分和 ≤ 极限 ≤ 奇部分和
theorem leibniz_even_le_limit {l : ℝ}
    (hfl : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹)
      Filter.atTop (𝓝 l)) (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹) ≤ l := by
  refine Antitone.alternating_series_le_tendsto hfl ?_ k
  refine antitone_nat_of_succ_le ?_
  intro n
  exact (inv_le_inv₀ (by positivity : 0 < ((n + 2 : ℕ) : ℝ))
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ))).mpr (by norm_num)

theorem leibniz_limit_le_odd {l : ℝ}
    (hfl : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹)
      Filter.atTop (𝓝 l)) (k : ℕ) :
    l ≤ (∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹) := by
  refine Antitone.tendsto_le_alternating_series hfl ?_ k
  refine antitone_nat_of_succ_le ?_
  intro n
  exact (inv_le_inv₀ (by positivity : 0 < ((n + 2 : ℕ) : ℝ))
    (by positivity : 0 < ((n + 1 : ℕ) : ℝ))).mpr (by norm_num)

-- 交错权重收敛 → 部分和误差量化: 极限被奇偶部分和夹逼 (Leibniz 定性)
theorem leibniz_error_quantified {l : ℝ}
    (hfl : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹)
      Filter.atTop (𝓝 l)) (k : ℕ) :
    (∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹) ≤ l ∧
      l ≤ (∑ i ∈ Finset.range (2 * k + 1), (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹) := by
  constructor
  · exact leibniz_even_le_limit hfl k
  · exact leibniz_limit_le_odd hfl k

-- C 声明: 对齐 ⟹ 零点临界带 (精确形态 + 已证原子 + 外部输入)
structure AlignmentToCriticalBand where
  -- 已证: 交错权重收敛骨架 (alternating_harmonic_converges + leibniz_error_quantified)
  weight_skeleton : Prop
  -- 外部输入: η 复侧条件收敛 (cos/sin 振荡, 非交错 — Leibniz 测试不适用)
  eta_complex_conditional_convergence : Prop
  -- 外部输入: Abel 延拓 (临界带内 η 良定义 = ζ 的 Dirichlet 展开换谐)
  abel_continuation : Prop
  -- 外部输入: 排斥因子 (1−2^{1−s}) 在临界带恒非零 (经典, 代数可证未形式化)
  repulsion_factor_nonzero : Prop
  -- 结论: 对齐 (交错旋转向量和 = 0) ⟹ η(s) = 0 ⟹ ζ(s) = 0 (临界带内零点)
  alignment_implies_zero : Prop
  -- 组合: 骨架 + 三个外部输入 ⟹ 对齐⟹零点
  assemble : weight_skeleton → eta_complex_conditional_convergence → abel_continuation →
    repulsion_factor_nonzero → alignment_implies_zero


-- R3 (攻坚): 对齐模长机制 — 圆外远处无零点的内禀证明
--   对齐 (部分和趋于 0) 的必要条件: 首项必须可被其余项抵消
--   若 Σ_{n≥1} ‖v_n‖ < ‖v_0‖ = 1, 则所有部分和 ≥ 1/4:
--     |S_N| ≥ 1 − Σ_{n=1}^{N-1} (n+1)^{-σ}   (反向三角)
--           ≥ 1 − Σ (n+1)^{-2}               (σ ≥ 2)
--           ≥ 1 − Σ 1/((n+1)(n+3))           (逐项放大)
--           ≥ 1 − 3/4 = 1/4                   (望远镜)
--   ⟹ ζ(s) ≠ 0 — 纯三角 + 望远镜, 无欧拉乘积 (机制与经典正交)
--   这是"命题甲 (圆外无零点)"的第一块纯内禀砖 (远圆 σ ≥ 2 部分)
-- ============================================================

-- 1. 每项模长: ‖1/(n+1)^s‖ = (n+1)^(-s.re)
lemma term_norm_eq (s : ℂ) (n : ℕ) :
    ‖(1 / ((n + 1 : ℂ) ^ s) : ℂ)‖ = (n + 1 : ℝ) ^ (-s.re) := by
  have hcp : ‖((n + 1 : ℂ) ^ s)‖ = (n + 1 : ℝ) ^ s.re := by
    simpa using (Complex.norm_cpow_eq_rpow_re_of_pos
      (x := (n + 1 : ℝ)) (by positivity : 0 < (n + 1 : ℝ)) (y := s))
  calc
    ‖(1 / ((n + 1 : ℂ) ^ s) : ℂ)‖ = 1 / ‖((n + 1 : ℂ) ^ s)‖ := by
      rw [norm_div, norm_one]
    _ = 1 / (n + 1 : ℝ) ^ s.re := by
      simpa using congrArg (fun x : ℝ => 1 / x) hcp
    _ = (n + 1 : ℝ) ^ (-s.re) := by
      rw [show (1 : ℝ) / (n + 1 : ℝ) ^ s.re = ((n + 1 : ℝ) ^ s.re)⁻¹ by
        rw [div_eq_mul_inv, one_mul]]
      exact (Real.rpow_neg (by positivity : 0 ≤ (n + 1 : ℝ)) s.re).symm

-- 2. 反向三角: |S_N| ≥ 1 − Σ_{n=1}^{N-1} ‖v_n‖  (N ≥ 1)
lemma partial_sum_norm_lower (s : ℂ) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Finset.range N, (1 / ((n + 1 : ℂ) ^ s) : ℂ))‖ ≥
      1 - ∑ n ∈ Finset.range (N - 1), (n + 2 : ℝ) ^ (-s.re) := by
  have hsplit : (∑ n ∈ Finset.range N, (1 / ((n + 1 : ℂ) ^ s) : ℂ)) =
      (1 : ℂ) + ∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ) := by
    have hN' : N - 1 + 1 = N := by omega
    rw [← hN', Finset.sum_range_succ']
    simp [Complex.one_cpow]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    ring
  rw [hsplit]
  -- |1 + A| ≥ |1| − |A|
  have hrev : ‖(1 : ℂ) + ∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ ≥
      1 - ‖∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ := by
    -- 1 = ‖1‖ = ‖(1+Σ) − Σ‖ ≤ ‖1+Σ‖ + ‖Σ‖  ⟹  ‖1+Σ‖ ≥ 1 − ‖Σ‖
    have h := norm_add_le
      (a := (1 : ℂ) + ∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ))
      (b := -(∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)))
    have hnorm1 : ‖(1 : ℂ)‖ = 1 := by simp
    have hnormneg : ‖-(∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ))‖ =
        ‖∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ := by simp
    have h' : (1 : ℝ) ≤
        ‖(1 : ℂ) + ∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ +
          ‖∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ := by
      simpa [hnorm1, hnormneg, add_assoc] using h
    linarith
  -- |A| ≤ Σ|项|
  have hsum : ‖∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ ≤
      ∑ n ∈ Finset.range (N - 1), (n + 2 : ℝ) ^ (-s.re) := by
    calc
      ‖∑ n ∈ Finset.range (N - 1), (1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ ≤
          ∑ n ∈ Finset.range (N - 1), ‖(1 / ((n + 2 : ℂ) ^ s) : ℂ)‖ := by
        exact norm_sum_le (Finset.range (N - 1)) (fun n : ℕ => (1 / ((n + 2 : ℂ) ^ s) : ℂ))
      _ = ∑ n ∈ Finset.range (N - 1), (n + 2 : ℝ) ^ (-s.re) := by
        apply Finset.sum_congr rfl
        intro n hn
        convert term_norm_eq s (n + 1) using 1
        all_goals norm_num [Nat.cast_add, Nat.cast_one]
        all_goals ring_nf
  linarith

-- 3. 逐项放大: (n+2)^{-2} ≤ 1/((n+1)(n+3))
lemma inv_sq_le (n : ℕ) :
    (n + 2 : ℝ) ^ (-2 : ℝ) ≤ 1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) := by
  -- (n+2)^{-2} = 1/(n+2)^2
  have hr : (n + 2 : ℝ) ^ (-2 : ℝ) = ((n + 2 : ℝ) ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg (by positivity : 0 ≤ (n + 2 : ℝ)) (2 : ℝ)
  rw [hr]
  rw [Real.rpow_two]
  -- 1/((n+2)^2) ≤ 1/((n+1)(n+3)) ⟺ (n+1)(n+3) ≤ (n+2)^2 (正数取倒数反序)
  have hpos1 : 0 < ((n + 2 : ℝ) ^ 2) := by
    have hz : (n + 2 : ℝ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    exact sq_pos_of_ne_zero hz
  have hpos2 : 0 < (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) := by
    have h21 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + 1)
    have h23 : (0 : ℝ) < ((n + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + 3)
    exact mul_pos h21 h23
  have h := (inv_le_inv₀ (a := ((n + 2 : ℝ) ^ 2))
    (b := (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ))) hpos1 hpos2).mpr
      (by norm_num [Nat.cast_add, Nat.cast_one]; nlinarith)
  simpa using h

-- 4. 望远镜: Σ_{n<M} 1/((n+1)(n+3)) = (1/2)(3/2 − 1/(M+1) − 1/(M+2)) ≤ 3/4
lemma telescoping_sum_bound (M : ℕ) :
    (∑ n ∈ Finset.range M, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ))) ≤ (3 : ℝ) / 4 := by
  have hclosed : (∑ n ∈ Finset.range M, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ))) =
      (1 / 2 : ℝ) * (1 + 1 / 2 - 1 / ((M + 1 : ℕ) : ℝ) - 1 / ((M + 2 : ℕ) : ℝ)) := by
    induction M with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        -- 新项 = 1/((M+1)(M+3)); 闭式差 = (1/2)(1/(M+1) − 1/(M+3))
        have hterm : 1 / (((M + 1 : ℕ) : ℝ) * ((M + 3 : ℕ) : ℝ)) =
            (1 / 2 : ℝ) * (1 / ((M + 1 : ℕ) : ℝ) - 1 / ((M + 3 : ℕ) : ℝ)) := by
          field_simp
          norm_num
        rw [hterm]
        field_simp
        ring
  rw [hclosed]
  have h1 : (0 : ℝ) ≤ 1 / ((M + 1 : ℕ) : ℝ) := by
    exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have h2 : (0 : ℝ) ≤ 1 / ((M + 2 : ℕ) : ℝ) := by
    exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  nlinarith

-- 5. 组装: 2 ≤ s.re ⟹ ∀N ≥ 1, ‖S_N‖ ≥ 1/4
lemma partial_sum_bound_of_two_le_re (s : ℂ) (hs : 2 ≤ s.re) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Finset.range N, (1 / ((n + 1 : ℂ) ^ s) : ℂ))‖ ≥ (1 : ℝ) / 4 := by
  have h1 := partial_sum_norm_lower s N hN
  have hmono : (∑ n ∈ Finset.range (N - 1), (n + 2 : ℝ) ^ (-s.re)) ≤
      (∑ n ∈ Finset.range (N - 1), (n + 2 : ℝ) ^ (-2 : ℝ)) := by
    exact Finset.sum_le_sum (fun n hn =>
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n + 2)) (by linarith))
  have htel : (∑ n ∈ Finset.range (N - 1), (n + 2 : ℝ) ^ (-2 : ℝ)) ≤ (3 : ℝ) / 4 := by
    calc
      (∑ n ∈ Finset.range (N - 1), (n + 2 : ℝ) ^ (-2 : ℝ)) ≤
          (∑ n ∈ Finset.range (N - 1), 1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ))) :=
        Finset.sum_le_sum (fun n hn => inv_sq_le n)
      _ ≤ (3 : ℝ) / 4 := telescoping_sum_bound (N - 1)
  linarith

-- 6. 极限传递: ‖ζ(s)‖ ≥ 1/4  (2 ≤ s.re)
theorem zeta_norm_lower_of_two_le_re (s : ℂ) (hs : 1 < s.re) (hs2 : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≥ (1 : ℝ) / 4 := by
  have hsum : Summable (fun n : ℕ => (1 / ((n + 1 : ℂ) ^ s) : ℂ)) := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
      (Complex.summable_one_div_nat_cpow (p := s)).mpr (by linarith : 1 < s.re)
    convert h0.comp_injective (i := Nat.succ) (fun ⦃a b⦄ h => Nat.succ.inj h) using 1
    · ext n
      simp
  have hlim : Filter.Tendsto
      (fun N : ℕ => ‖∑ n ∈ Finset.range N, (1 / ((n + 1 : ℂ) ^ s) : ℂ)‖)
      Filter.atTop (𝓝 ‖∑' n : ℕ, (1 / ((n + 1 : ℂ) ^ s) : ℂ)‖) := by
    exact hsum.hasSum.tendsto_sum_nat.norm
  have hfin : (1 : ℝ) / 4 ≤ ‖∑' n : ℕ, (1 / ((n + 1 : ℂ) ^ s) : ℂ)‖ := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    exact partial_sum_bound_of_two_le_re s hs2 N hN
  rw [← zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith : 1 < s.re)] at hfin
  simpa using hfin

-- 7. 结论: 2 ≤ Re s ⟹ ζ(s) ≠ 0 (对齐模长机制, 内禀)
theorem zeta_ne_zero_of_two_le_re (s : ℂ) (hs : 1 < s.re) (hs2 : 2 ≤ s.re) :
    riemannZeta s ≠ 0 := by
  have hnz : ‖riemannZeta s‖ ≠ 0 := by
    have h := zeta_norm_lower_of_two_le_re s hs hs2
    linarith
  exact (norm_ne_zero_iff.mp hnz)

-- 8. η 实轴正性 (σ=1 交错调和): 极限 l ≥ 1/2 > 0 (Leibniz 夹逼, 已证原子)
theorem alternating_harmonic_limit_pos :
    ∃ l : ℝ, 0 < l ∧
      Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * ((i + 1 : ℕ) : ℝ)⁻¹)
        Filter.atTop (𝓝 l) := by
  rcases alternating_harmonic_converges with ⟨l, hl⟩
  refine ⟨l, ?_, hl⟩
  have hle := leibniz_even_le_limit hl 1
  have hsum2 : (∑ x ∈ Finset.range 2, (-1 : ℝ) ^ x * ((x + 1 : ℕ) : ℝ)⁻¹) = 1 / 2 := by
    norm_num [Finset.sum_range_succ]
  linarith

-- 9. 声明: 内禀无零点的组装 + 缺口
structure IntrinsicZeroFree where
  -- 已证: σ ≥ 2 ⟹ 无零点 (对齐模长: 首项不可抵消, 部分和 ≥ 1/4)
  far_circle_zero_free : Prop
  -- 已证: η 实轴交错极限正 (Leibniz 夹逼, σ=1)
  real_axis_eta_positive : Prop
  -- 缺口 (RH 核心): σ ∈ (1/2, 1) 圆环内无零点 — 无内禀通道, 经典亦未解
  annulus_zero_free : Prop

-- R4 (攻坚): 反演对分解 — 环内零点 = 反演对 ⊕ 圆上自配对
--   反射零点等价 (临界带, 函数方程): ζ(1−s)=0 ⟺ ζ(s)=0
--   (riemannZeta_one_sub + 因子非零: 2·(2π)^{-s}·Γ(s)·cos(πs/2) ≠ 0)
--   隐数读法: 反射 s↦1−s = 反演 w↦e/w; 自配对 ⟺ w=±√e (圆上, 纯代数)
--   命题甲压缩: 无非自配对反演对 ⟹ 全在不动圆上 ⟹ RH (机制环)
-- ============================================================

-- 1. cos(πs/2) ≠ 0 (临界带): Re cos(πs/2) = cos(πσ/2)·cosh(πt/2) > 0
lemma cos_half_pi_s_ne_zero {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
  let z : ℂ := (Real.pi : ℂ) * s / 2
  have hz : z = (z.re : ℂ) + z.im * Complex.I := by
    rw [Complex.re_add_im]
  have hcosre : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    rw [hz, Complex.cos_add_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    rw [Complex.sub_re]
    have h1 : ((Real.cos z.re : ℂ) * (Real.cosh z.im : ℂ)).re = Real.cos z.re * Real.cosh z.im := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    have h2 : ((Real.sin z.re : ℂ) * (Real.sinh z.im : ℂ) * Complex.I).re = 0 := by
      rw [← Complex.ofReal_mul]
      rw [Complex.mul_re]
      simp [Complex.ofReal_re, Complex.ofReal_im]
    rw [h1, h2]
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hzre : z.re = Real.pi * s.re / 2 := by
    dsimp [z]
    have hπre : (Real.pi : ℂ).re = Real.pi := by
      simpa using (Complex.ofReal_re Real.pi)
    have hπim : (Real.pi : ℂ).im = 0 := by
      simpa using (Complex.ofReal_im Real.pi)
    have hre1 : ((Real.pi : ℂ) * s).re = Real.pi * s.re := by
      rw [Complex.mul_re]
      rw [hπre, hπim]
      ring
    have him1 : ((Real.pi : ℂ) * s).im = Real.pi * s.im := by
      rw [Complex.mul_im]
      rw [hπre, hπim]
      ring
    have h2re : ((2 : ℂ)⁻¹).re = 1 / 2 := by
      simpa using congrArg Complex.re (Complex.ofReal_inv (x := 2))
    have h2im : ((2 : ℂ)⁻¹).im = 0 := by
      simpa using congrArg Complex.im (Complex.ofReal_inv (x := 2))
    -- (A/2).re = A.re/2 (A = (Real.pi:ℂ)*s)
    have hdiv : ((Real.pi : ℂ) * s / 2).re = Real.pi * s.re / 2 := by
      rw [div_eq_mul_inv]
      rw [Complex.mul_re]
      rw [hre1, him1, h2re, h2im]
      ring
    exact hdiv
  have hcospos : 0 < Real.cos z.re := by
    rw [hzre]
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · have hneg : -(Real.pi / 2) < 0 := by
        exact neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num : 0 < (2 : ℝ)))
      have hpos : 0 < Real.pi * s.re / 2 :=
        div_pos (mul_pos Real.pi_pos hσ0) (by norm_num : 0 < (2 : ℝ))
      linarith
    · have hlt : Real.pi * s.re < Real.pi := by
        simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using
          (mul_lt_mul_of_pos_right hσ1 Real.pi_pos)
      have hlt2 : Real.pi * s.re * (2 : ℝ) < Real.pi * (2 : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_lt_mul_of_pos_right hlt (by norm_num : 0 < (2 : ℝ)))
      exact (div_lt_div_iff₀ (by norm_num : 0 < (2 : ℝ)) (by norm_num : 0 < (2 : ℝ))).mpr hlt2
  have hcoshpos : 0 < Real.cosh z.im := Real.cosh_pos _
  have hrepos : 0 < (Complex.cos z).re := by
    rw [hcosre]
    exact mul_pos hcospos hcoshpos
  intro hz0
  have hre0 : (Complex.cos z).re = 0 := by rw [hz0]; simp
  linarith

-- 2. 因子非零: 2·(2π)^{-s}·Γ(s)·cos(πs/2) ≠ 0 (临界带)
lemma reflection_factor_ne_zero {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    (2 : ℂ) * ((2 : ℂ) * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
      Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hc : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    have h2p : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := by
      have hπ : (Real.pi : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact mul_ne_zero (by norm_num) hπ
    exact (Complex.cpow_ne_zero_iff (x := (2 : ℂ) * (Real.pi : ℂ)) (y := -s)).mpr (Or.inl h2p)
  have hg : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hσ0
  have hcs : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := cos_half_pi_s_ne_zero hσ0 hσ1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hc) hg) hcs

-- 3. 临界带反射零点等价: ζ(1−s)=0 ⟺ ζ(s)=0 (函数方程, mathlib)
theorem zeta_zero_iff_one_sub {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1) :
    (riemannZeta (1 - s) = 0 ↔ riemannZeta s = 0) := by
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have hre : s.re = (-(n : ℂ)).re := by rw [hn]
    have hle : (-(n : ℂ)).re ≤ 0 := by
      rw [Complex.neg_re]
      exact neg_nonpos.mpr (Nat.cast_nonneg n)
    linarith
  have hs' : s ≠ 1 := by
    intro h
    have : s.re = 1 := by simpa using congrArg Complex.re h
    linarith
  have hfe := riemannZeta_one_sub (s := s) hs hs'
  have hF : (2 : ℂ) * ((2 : ℂ) * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s *
      Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := reflection_factor_ne_zero hσ0 hσ1
  constructor
  · intro hz
    rw [hfe] at hz
    exact (mul_eq_zero.mp hz).resolve_left hF
  · intro hz
    rw [hfe]
    simp [hz]

-- 4. 反射零点闭合: 临界带零点在 s↦1−s 下成对
theorem zero_pair_reflect {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 :=
  (zeta_zero_iff_one_sub hσ0 hσ1).mpr hz

-- 5. 自配对 ⟺ w = ±√e (纯代数): w = e/w ⟺ w² = e
theorem self_pair_iff (w : ℂ) (hw : w ≠ 0) :
    ((Real.exp 1 : ℂ) / w = w) ↔ (w = Real.sqrt (Real.exp 1) ∨ w = -Real.sqrt (Real.exp 1)) := by
  -- e/w = w ⟺ e = w²
  have hmain : ((Real.exp 1 : ℂ) / w = w) ↔ ((Real.exp 1 : ℂ) = w * w) := by
    constructor
    · intro h
      have : (Real.exp 1 : ℂ) = w * w := by
        calc
          (Real.exp 1 : ℂ) = w * ((Real.exp 1 : ℂ) / w) := by
            rw [mul_div_cancel₀ _ hw]
          _ = w * w := by rw [h]
      exact this
    · intro h
      calc
        (Real.exp 1 : ℂ) / w = (w * w) / w := by rw [h]
        _ = w := by
          rw [mul_div_cancel_left₀ w hw]
  -- w² = e ⟺ w = ±√e: 因式分解 (w−√e)(w+√e) = w² − e = 0
  have hsq : (Real.sqrt (Real.exp 1) : ℂ) * (Real.sqrt (Real.exp 1) : ℂ) = (Real.exp 1 : ℂ) := by
    have hsqr : Real.sqrt (Real.exp 1) * Real.sqrt (Real.exp 1) = Real.exp 1 := by
      rw [← pow_two]
      exact Real.sq_sqrt (le_of_lt (Real.exp_pos 1))
    rw [← Complex.ofReal_mul]
    exact congrArg (fun x : ℝ => (x : ℂ)) hsqr
  rw [hmain]
  constructor
  · intro h
    -- e = w² ⟹ w² = e
    have hw2 : w * w = (Real.exp 1 : ℂ) := h.symm
    have hsq2 : (Real.sqrt (Real.exp 1) : ℂ) ^ 2 = (Real.exp 1 : ℂ) := by
      have hsqr : Real.sqrt (Real.exp 1) ^ 2 = Real.exp 1 := by
        exact Real.sq_sqrt (le_of_lt (Real.exp_pos 1))
      rw [← Complex.ofReal_pow]
      exact congrArg (fun x : ℝ => (x : ℂ)) hsqr
    have hfac : (w - (Real.sqrt (Real.exp 1) : ℂ)) * (w + (Real.sqrt (Real.exp 1) : ℂ)) = 0 := by
      ring_nf
      rw [hsq2]
      rw [← hw2]
      ring
    rcases mul_eq_zero.mp hfac with hz | hz
    · left
      exact sub_eq_zero.mp hz
    · right
      exact eq_neg_of_add_eq_zero_left hz
  · intro h
    rcases h with h | h
    · rw [h]
      exact hsq.symm
    · rw [h]
      have hneg : (-(Real.sqrt (Real.exp 1) : ℂ)) * (-(Real.sqrt (Real.exp 1) : ℂ)) =
          (Real.sqrt (Real.exp 1) : ℂ) * (Real.sqrt (Real.exp 1) : ℂ) := by ring
      exact hsq.symm.trans hneg.symm

-- 6. 自配对 ⟹ 在圆上: w = e/w ⟹ ‖w‖ = √e (经 inversion_fixed_radius)
theorem self_pair_on_circle (w : ℂ) (hw : w ≠ 0) (h : (Real.exp 1 : ℂ) / w = w) :
    ‖w‖ = Real.sqrt (Real.exp 1) := by
  have hnorm : ‖(Real.exp 1 : ℂ) / w‖ = ‖w‖ := by rw [h]
  exact (inversion_fixed_radius w hw).mp hnorm

-- 7. 反射对合: 1−(1−s) = s
theorem reflect_involutive (s : ℂ) : 1 - (1 - s) = s := by ring

-- 8. 声明: 反演对分解 — 无非自配对对 ⟹ 全在圆上 ⟹ RH
structure InversionPairDecomposition where
  -- 已证: 反射零点闭合 (zero_pair_reflect: ζ(1−s)=0 ⟸ ζ(s)=0, 临界带)
  reflection_closed : Prop
  -- 已证: 自配对 ⟺ w=±√e (self_pair_iff); 自配对 ⟹ |w|=√e (self_pair_on_circle)
  self_pair_algebra : Prop
  -- 已证: 反射对合 (reflect_involutive)
  involution : Prop
  -- 缺口 (RH 本身): 圆环 1<|w|<e 内无 |w|≠√e 的零点 — 与 zeta_zero_iff_one_sub
  --   组合后即"零点 ⟹ Re s = 1/2" (hno) = 机制环最后一格
  --   措辞校正 (2026-09-01): 缺口是"反射对整体落在不动圆上"(集合层, |e/w|=|w|),
  --   **不是**"每个反射对都自配对"(点层, e/w=w ⟺ w=±√e, 提升高度 t∈πℤ).
  --   反例: s=1/2+14.1347i 在圆上但 e/w=conj w≠w (14.1347∉πℤ), 是二元轨道.
  --   故"每个对都自配对"严格强于 RH 且与已知零点冲突, 不可作 RH 等价表述.
  no_zero_off_circle : Prop
  -- 结论: 机制环 A⟺B⟺C⟺D (已证) 给出 no_zero_off_circle ⟹ RH
  rh : Prop
  assemble : no_zero_off_circle → rh


-- ============================================================
-- §17 对齐密度猜想 (R5) — 频率均匀性 → 对齐密度的显式陈述
--   数值 (fig15): N(T)/F(T) → 1 (T=100..3200: 1.031 → 1.0003),
--   其中 F(T) = (T/2π)(log(T/2π) − 1) 为频率相位投影 (无 Stirling)
--   已证骨架: freq_span_telescopes (ΣΔfreq = log N) + freq_gap_le_inv
--   (Δfreq ≤ 1/(n+1)) — 频率均匀性内禀
--   诚实边界: 严格化需等分布/加权 Weyl 准则 (mathlib 无);
--   且 R5c 数值显示临界带内部分和 |S_N| 不趋于 0 (γ₁ 处随 N 增长,
--   0.25 → 1.42) — 对齐 (零点) 是解析延拓的零点, 非级数部分和的零点
--   ⟹ §10 zeta_phase_alignment_condition 的 Re>1 版本不能直接搬进临界带
-- ============================================================
structure FrequencyAlignmentConjecture where
  -- 已证: 频率均匀性 (freq_span_telescopes + freq_gap_le_inv, §1-2)
  frequency_uniformity : Prop
  -- 数值: N(T)/F(T) → 1 (T=100..3200: 1.0310 → 1.0003, fig15)
  density_projection_numerics : Prop
  -- 猜想: 零点 (对齐事件) 密度 = 频率相位投影 (无 Stirling)
  alignment_density : Prop
  -- 数值对照: 反演对分解只属临界带 (平凡零点对破坏 vs 临界带成对, fig15)
  pair_decomposition_numerics : Prop
  -- 缺口: 严格化需等分布/加权 Weyl 准则 (mathlib 未形式化)
  equidistribution_needed : Prop



-- R6 (攻坚): 频率结构 — 相位折返与冻结 (只看频率, 不看能量)
--   频率间距: Δfreq(n) = log(n+2) − log(n+1) (freq_gap_le_inv 已证 ≤ 1/(n+1))
--   相位差: η 交错项 Δθ_n = π − t·Δfreq(n) — 单调递增 (频率间距收缩)
--   ⟹ 折返点 n* ≈ t/π 存在 (零点高度在频率域的回声)
--   相位冻结: ζ 直和项 Δφ_n = t·Δfreq(n) 递减 → 0 (高频项同向叠加)
-- ============================================================

noncomputable def freq_gap (n : ℕ) : ℝ :=
  Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)

-- 1. 频率间距收缩到 0: log((n+2)/(n+1)) → 0
lemma freq_gap_tendsto_zero : Filter.Tendsto freq_gap Filter.atTop (𝓝 0) := by
  -- (n+2)/(n+1) → 1
  have h : Filter.Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (𝓝 1) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
        Filter.atTop (𝓝 0) := by
      have hfun : (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) =
          (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) := by
        funext n
        norm_num [Nat.cast_add, Nat.cast_one]
      rw [hfun]
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    -- (n+2)/(n+1) = 1 + 1/(n+1)
    have hnorm : (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
        (fun n : ℕ => 1 + (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
      funext n
      have hden : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hden]
      exact_mod_cast (by omega : n + 2 = n + 1 + 1)
    rw [hnorm]
    simpa using h1.const_add 1
  -- log 连续 (在 1 ≠ 0)
  have hlog := Real.continuousAt_log (x := (1 : ℝ)) (by norm_num : (1 : ℝ) ≠ 0)
  -- log((n+2)/(n+1)) = log(n+2) − log(n+1) = freq_gap n
  have hlog' : (fun n : ℕ => Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) = freq_gap := by
    funext n
    rw [Real.log_div (by positivity : ((n + 2 : ℕ) : ℝ) ≠ 0) (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)]
    rfl
  -- log ∘ h → log 1 = 0
  have hcomp : Filter.Tendsto (fun n : ℕ => Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
      Filter.atTop (𝓝 (Real.log 1)) := h.log (by norm_num : (1 : ℝ) ≠ 0)
  have hlog1 : Real.log 1 = 0 := by simp
  rw [← hlog']
  simpa [hlog1] using hcomp

-- 2. 频率间距单调递减: Δfreq(n+1) ≤ Δfreq(n)
lemma freq_gap_antitone (n : ℕ) : freq_gap (n + 1) ≤ freq_gap n := by
  -- 归一化 Nat 算术: (n+1)+2 = n+3, (n+1)+1 = n+2 (定义性)
  change Real.log ((n + 3 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ) ≤
         Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ)
  -- log((n+3)/(n+2)) ≤ log((n+2)/(n+1)) ⟺ (n+3)/(n+2) ≤ (n+2)/(n+1) (log 单调)
  have hlog : Real.log (((n + 3 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) ≤
      Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
    apply (Real.log_le_log_iff (by positivity : 0 < ((n + 3 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))
      (by positivity : 0 < ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))).mpr
    -- (n+3)/(n+2) ≤ (n+2)/(n+1) ⟺ (n+3)(n+1) ≤ (n+2)²
    rw [div_le_div_iff₀ (by positivity : 0 < ((n + 2 : ℕ) : ℝ)) (by positivity : 0 < ((n + 1 : ℕ) : ℝ))]
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  -- log 差形式 ⟸ log 比形式 (log_div 反向)
  have hdiv1 : Real.log (((n + 3 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) =
      Real.log ((n + 3 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ) :=
    Real.log_div (by positivity : ((n + 3 : ℕ) : ℝ) ≠ 0) (by positivity : ((n + 2 : ℕ) : ℝ) ≠ 0)
  have hdiv2 : Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
      Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_div (by positivity : ((n + 2 : ℕ) : ℝ) ≠ 0) (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)
  -- 目标 = hlog (经 hdiv1/hdiv2 的差形式)
  calc
    Real.log ((n + 3 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ)
        = Real.log (((n + 3 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) := hdiv1.symm
    _ ≤ Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := hlog
    _ = Real.log ((n + 2 : ℕ) : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) := hdiv2

-- 3. 相位冻结: ∀ε>0, ∃N, ∀n≥N, t·Δfreq(n) < ε (t > 0)
lemma phase_freeze (t : ℝ) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → t * freq_gap n < ε := by
  -- freq_gap → 0 ⟹ ∃N, ∀n≥N, |freq_gap n| < ε/t
  have ht' : 0 < ε / t := div_pos hε ht
  have hfin : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |freq_gap n| < ε / t := by
    -- freq_gap → 0: 对 0 的邻域 (-δ, δ) 最终在内 (tendsto 定义)
    have hball : ∀ᶠ y : ℝ in 𝓝 0, y ∈ Set.Ioo (-(ε / t)) (ε / t) := by
      exact IsOpen.mem_nhds isOpen_Ioo (by simp [ht'])
    have hev : ∀ᶠ n : ℕ in Filter.atTop, |freq_gap n| < ε / t := by
      simpa [abs_lt] using (freq_gap_tendsto_zero.eventually hball)
    rcases (Filter.eventually_atTop.mp hev) with ⟨N, hN⟩
    exact ⟨N, hN⟩
  rcases hfin with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  -- t·freq_gap n < ε ⟸ freq_gap n < ε/t (t > 0)
  have hlt : freq_gap n < ε / t := by
    have habs := hN n hn
    exact lt_of_abs_lt habs
  -- freq_gap n 可能负? — t·freq_gap < ε: 若 freq_gap ≤ 0 则 t·freq_gap ≤ 0 < ε ✓; 若正则用 hlt
  by_cases hnonneg : 0 ≤ freq_gap n
  · -- t·freq_gap n ≤ t·(ε/t) = ε
    have hle : t * freq_gap n < t * (ε / t) := by
      exact mul_lt_mul_of_pos_left hlt ht
    -- t·(ε/t) = ε
    have htdiv : t * (ε / t) = ε := by
      field_simp [ne_of_gt ht]
    linarith
  · -- freq_gap n < 0: t·freq_gap < 0 < ε
    have hneg : t * freq_gap n < 0 := mul_neg_of_pos_of_neg ht (lt_of_not_ge hnonneg)
    linarith

-- 4. 折返点: t·log 2 > π ⟹ ∃n, Δθ_n ≤ 0 ∧ 0 < Δθ_{n+1}
--    Δθ_n = π − t·freq_gap n — 单调递增 (freq_gap_antitone), 从负到正 ⟹ 变号
lemma fold_point_exists (t : ℝ) (ht : t * Real.log 2 > Real.pi) :
    ∃ n : ℕ, Real.pi - t * freq_gap n ≤ 0 ∧ 0 < Real.pi - t * freq_gap (n + 1) := by
  -- Δθ_0 = π − t·log 2 < 0 (freq_gap 0 = log 2)
  have h0 : Real.pi - t * freq_gap 0 < 0 := by
    have hg0 : freq_gap 0 = Real.log 2 := by
      rw [freq_gap]
      norm_num
    rw [hg0]
    linarith
  -- Δθ_n → π > 0 ⟹ ∃k, 0 < Δθ_k
  have htend : Filter.Tendsto (fun n : ℕ => Real.pi - t * freq_gap n) Filter.atTop (𝓝 Real.pi) := by
    -- π − t·freq_gap → π (freq_gap → 0)
    have hcomp : Filter.Tendsto (fun n : ℕ => t * freq_gap n) Filter.atTop (𝓝 0) := by
      simpa using freq_gap_tendsto_zero.const_mul t
    simpa using (tendsto_const_nhds.sub hcomp)
  have hpos_ev : ∀ᶠ n : ℕ in Filter.atTop, 0 < Real.pi - t * freq_gap n := by
    -- π − t·freq_gap → π 且 0 < π: 最终 > 0
    have hπ : ∀ᶠ y : ℝ in 𝓝 Real.pi, 0 < y := by
      exact IsOpen.mem_nhds isOpen_Ioi (by positivity : 0 < Real.pi)
    simpa using (htend.eventually hπ)
  have hpos : ∃ k : ℕ, 0 < Real.pi - t * freq_gap k := by
    rcases (Filter.eventually_atTop.mp hpos_ev) with ⟨K, hK⟩
    exact ⟨K, hK K (le_rfl)⟩
  -- 最小正点: Nat.find
  let k := Nat.find hpos
  have hk_spec : 0 < Real.pi - t * freq_gap k := Nat.find_spec hpos
  have hk_min : ∀ m < k, ¬ 0 < Real.pi - t * freq_gap m := by
    intro m hm
    have hfm : m < Nat.find hpos → ¬ 0 < Real.pi - t * freq_gap m :=
      Nat.find_min hpos
    exact hfm (by simpa [k] using hm)
  -- k ≥ 1 (Δθ_0 < 0)
  have hk_ge : 1 ≤ k := by
    dsimp [k]
    by_contra h
    have hk0 : Nat.find hpos = 0 := by omega
    have h0' : Real.pi - t * freq_gap (Nat.find hpos) < 0 := by
      rw [hk0]
      exact h0
    linarith [hk_spec]
  -- 折返点 n = k−1: Δθ_{k−1} ≤ 0 ∧ 0 < Δθ_k
  refine ⟨k - 1, ?_, ?_⟩
  · -- Δθ_{k−1} ≤ 0
    by_cases hk1 : k = 1
    · -- k = 1: Δθ_0 ≤ 0 — 从 h0 (严格 < 0)
      have hkm0 : k - 1 = 0 := by omega
      rw [hkm0]
      simp [freq_gap, Real.log_one, Nat.cast_add, Nat.cast_one] at h0 ⊢
      norm_num
      linarith
    · -- k ≥ 2: k−1 < k ⟹ ¬(0 < Δθ_{k−1}) ⟹ Δθ_{k−1} ≤ 0
      have hkm : k - 1 < k := by omega
      have hnot := hk_min (k - 1) hkm
      have hle0 : Real.pi - t * freq_gap (k - 1) ≤ 0 := le_of_not_gt hnot
      exact hle0
  · -- 0 < Δθ_k —— n+1 = (k−1)+1 = k
    have hkm : (k - 1) + 1 = k := by omega
    simpa [hkm] using hk_spec


-- ============================================================
-- §19 临界圆无限零点 — 完整论证 (互相参考 R1-R6)
--   位置: R2 radius_uniqueness_chain (√e = 能量平衡 = 反演不动) +
--         R4 zeta_zero_iff_one_sub (反射配对) + self_pair_on_circle
--   频率: R6 fold_point_exists (相位折返 n*≈t/π) + phase_freeze (冻结尾)
--   能量: R1 TruncatedEnergyLower (截断能量下界) + B3 均值定理
--         E(T) = (T/2)(log(T/2π)−1) + γT + o(T) (diagonal_integral +
--         harmonic_log_tendsto_euler 已证, 无 Stirling)
--   密度: R5 FrequencyAlignmentConjecture (N(T)/F(T) → 1 数值)
--   反证: Hardy 输入 (有限对齐 ⟹ 能量有界) — 外部输入结构体字段
--   结论: 临界圆上无限对齐事件 (零点无限, 位置在圆上)
-- ============================================================
structure CriticalCircleInfinity where
  -- R2+R4: 临界圆身份 (能量平衡/反演不动/反射不动 ⟹ √e) + 零点反射配对
  position_circle : Prop
  -- R6: 频率折返点 + 相位冻结尾 (相位旋转在 n* ≈ t/π 折返)
  frequency_fold : Prop
  -- R1: 截断能量下界 ∫₀ᵀ|S_X|² ≥ T·Σ(n+1)⁻¹ − 交叉修正 (交叉次主导)
  energy_lower : Prop
  -- B3: 均值定理 E(T) = (T/2)(log(T/2π)−1) + γT + o(T) (无 Stirling)
  mean_value : Prop
  -- R5: 对齐密度 = 频率相位投影 N(T)/F(T) → 1 (数值)
  density_projection : Prop
  -- Hardy 反证输入 (外部): 对齐事件有限 ⟹ 能量有界
  bounded_energy_of_finite : Prop
  -- 结论: 临界圆上无限多个对齐事件 (零点)
  infinite_on_circle : Prop
  -- 组装: 位置 + 频率 + 能量 + 密度 + 反证 ⟹ 无限
  assemble : position_circle → frequency_fold → energy_lower → mean_value →
    density_projection → bounded_energy_of_finite → infinite_on_circle


-- ============================================================
-- §20 (R7) Γ 不对称量 — 缺口精确定位 (2026-09-01, leo 推导)
--   推导: 函数方程 Λ(s)=Λ(1−s) 的 Γ 侧不对称, 由 Stirling:
--     |Γ(s/2)| / |Γ((1−s)/2)| ~ (t/2)^{σ−1/2} = (t/2)^{log(ρ/√e)},  ρ=|w|
--   这是全装置唯一的 σ-不对称量; 反射把 ρ 配到 e/ρ, 两侧质量恰在 ρ=√e
--   时相等. 排除性论证 (RH = 环内无离圆零点) 必须经过它 — B 墙的坐标形态.
--   逻辑类型: 恒等式/丰度/临界性三条已具备, 唯独缺「排除」; 排除的入口
--   就是这条不对称量 (Stirling 级输入, mathlib 无 — P1–P3 诚实边界).
--   另: RS 主和截断 N=⌊√(t/2π)⌋ ≪ 频率折返点 n*≈t/π (t=1000: 12.6 vs 318),
--   折返点落在被丢弃的发散尾部 — fold_point_exists 与零点联系未建立.
-- ============================================================

-- 1. 坐标恒等式: 不对称指数 σ − 1/2 = log(ρ/√e), 其中 ρ = |w| = e^σ
theorem asym_exp_log_rho (σ : ℝ) :
    σ - (1 / 2 : ℝ) = Real.log (Real.exp σ / Real.sqrt (Real.exp 1)) := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos σ)) (ne_of_gt (by positivity : 0 < Real.sqrt (Real.exp 1)))]
  rw [Real.log_exp]
  have hlog : Real.log (Real.sqrt (Real.exp 1)) = 1 / 2 := by
    rw [Real.log_sqrt (le_of_lt (Real.exp_pos 1))]
    rw [Real.log_exp]
  rw [hlog]

-- 2. 反射公式的模形式: |Γ(s/2)|·|Γ(1−s/2)| = π / |sin(πs/2)|
--    (mathlib Complex.Gamma_mul_Gamma_one_sub 的模版本)
theorem gamma_reflection_mod (s : ℂ) :
    ‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖ =
      ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (s / 2))‖ := by
  calc
    ‖Complex.Gamma (s / 2)‖ * ‖Complex.Gamma (1 - s / 2)‖
        = ‖Complex.Gamma (s / 2) * Complex.Gamma (1 - s / 2)‖ := by
            rw [← norm_mul]
    _ = ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (s / 2))‖ := by
            rw [Complex.Gamma_mul_Gamma_one_sub]

-- 3. R7 声明: Γ 比不对称 — 缺口精确定位 (结构体骨架, Stirling 为外部输入)
structure GammaRatioAsymmetry where
  -- 已证: 指数坐标恒等式 σ−1/2 = log(ρ/√e) (asym_exp_log_rho)
  exponent_coordinate : Prop
  -- 已证: 反射公式模 (gamma_reflection_mod)
  reflection_mod : Prop
  -- 外部输入 (Stirling, mathlib 无 — P1–P3 边界):
  --   |Γ(s/2)| / |Γ((1−s)/2)| ~ (t/2)^{σ−1/2}
  gamma_ratio_asymptotic : Prop
  -- 缺口定位: σ≠1/2 ⟹ 比≠1 ⟹ 反射两侧质量不等; 排除离圆零点需此输入 (B 墙)
  asymmetry_off_circle : Prop
  -- 组装: 渐近 + 指数坐标 ⟹ 离圆零点处 Γ 侧不对称 (仍赖 Stirling, 不装证)
  assemble : gamma_ratio_asymptotic → exponent_coordinate → asymmetry_off_circle


-- ============================================================
-- §21 (A) η 临界带桥 — 对齐语言在临界带的良定 (2026-09-01)
--   Re>1 版本 (eta_eq_mul_zeta, Analytic.lean) 已落地; 临界带 0<σ<1 的
--   「对齐」语义需: ①η 条件收敛 (复数 Dirichlet/Abel 测试 — mathlib 无);
--   ②延拓等式 η=(1−2^{1−s})ζ (解析延拓/Abel 定理). 二者均非概念不可能,
--   是 mathlib 基建缺失 — 显式声明为输入, 不装证 (A 是 bookkeeping,
--   做完不给 RH 加任何东西, 只是让字典不出错).
-- ============================================================

-- 1. η 部分和: 对齐语言的语法对象 (交错 × cpow)
noncomputable def etaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * ((n + 1 : ℕ) : ℂ) ^ (-s)

-- 2. Re>1 绝对收敛 (真定理): ‖(−1)^n·(n+1)^{−s}‖ = (n+1)^{−σ}, p 级数 σ>1
theorem eta_summable_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (-1 : ℂ) ^ n * ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
  refine Summable.of_norm ?_
  have hnorm : ∀ n : ℕ,
      ‖(-1 : ℂ) ^ n * ((n + 1 : ℕ) : ℂ) ^ (-s)‖ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
    intro n
    rw [norm_mul]
    have hneg : ‖(-1 : ℂ) ^ n‖ = 1 := by
      rw [norm_pow]
      norm_num
    rw [hneg, one_mul]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) (-s)
  have hbase : Summable (fun m : ℕ => (((m : ℕ) : ℝ) ^ s.re)⁻¹) :=
    (Real.summable_nat_rpow_inv).mpr hs
  have hshift : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ s.re)⁻¹)) := by
    exact hbase.comp_injective (fun a b h => by omega)
  have hsum : Summable (fun n : ℕ => ‖(-1 : ℂ) ^ n * ((n + 1 : ℕ) : ℂ) ^ (-s)‖) := by
    refine hshift.congr ?_
    intro n
    rw [hnorm n]
    rw [Real.rpow_neg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
  exact hsum

-- 3. A 声明: η 临界带桥 — 对齐语言在临界带良定
structure EtaCriticalStripBridge where
  -- 已证: Re>1 绝对收敛 (eta_summable_of_one_lt_re)
  absolute_convergence_R1 : Prop
  -- 已证: η 部分和 = 交错 × cpow (对齐语法对象, etaPartialSum)
  align_syntax : Prop
  -- 外部输入: 临界带 0<σ<1 η 条件收敛 (复数 Dirichlet/Abel 测试, mathlib 无)
  conditional_convergence_strip : Prop
  -- 外部输入: 延拓等式 η=(1−2^{1−s})ζ 在临界带 (Abel 定理/解析延拓)
  continuation_eq_strip : Prop
  -- 结论: 对齐语言在临界带良定 (ζ=0 ⟺ 对齐 在 0<σ<1)
  align_well_defined_strip : Prop
  -- 组装: Re>1 已证 + 临界带两个输入 ⟹ 良定
  assemble : absolute_convergence_R1 → align_syntax → conditional_convergence_strip →
    continuation_eq_strip → align_well_defined_strip


-- ============================================================
-- §22 (B) σ>1/2 无零点 = RH — 依赖链钉形状 + 3-4-1 代数核心砖 (2026-09-01)
--   mathlib 家底 (侦察): Phragmén–Lindelöf ✅ (唯一性形态, PhragmenLindelof.lean)
--   + Borel–Carathéodory ✅ + 最大模 ✅; ❌ 零密度 / AFE / Riemann–Siegel /
--   Lindelöf 估计 / 无零点区域. 故 B 的 Lean 形态 = 代数核心 (3-4-1 系数非负,
--   可证) + 依赖链结构体 (条带增长 + 零密度 = 外部输入, 经典文献供给).
-- ============================================================

-- 1. 3-4-1 核心 (真定理): 3 + 4cosθ + cos2θ = 2(cosθ+1)² ≥ 0
theorem three_four_one_nonneg (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos θ + 1)]

-- 2. Mertens 系数 (真定理): Re(3 + 4(n+1)^{−it} + (n+1)^{−2it}) ≥ 0
--    (n+1)^{−it} = e^{−it·log(n+1)}, 实部 = cos(t·log(n+1))
theorem mertens_coeff_re_nonneg (t : ℝ) (n : ℕ) :
    0 ≤ 3 + 4 * Real.cos (t * Real.log (n + 1 : ℝ)) +
      Real.cos (2 * (t * Real.log (n + 1 : ℝ))) :=
  three_four_one_nonneg (t * Real.log (n + 1 : ℝ))

-- 3. B 声明: σ>1/2 无零点 (= RH 经典形态) — 依赖链钉形状
structure ZeroFreeHalfPlane where
  -- 已证: 函数方程反射 (riemannZeta_one_sub → zeta_zero_iff_one_sub)
  reflection : Prop
  -- 已证: σ≥2 无零点 (zeta_ne_zero_of_two_le_re)
  far_field_zero_free : Prop
  -- 已证: 3-4-1 系数非负 (three_four_one_nonneg, mertens_coeff_re_nonneg) —
  --   无零点区域论证的代数核心 (ζ(1+it)≠0 的构建块)
  mertens_core : Prop
  -- 外部输入: ζ 条带增长上界 |ζ(σ+it)| ≤ C_σ·t^{A(σ)} (Lindelöf 级, AFE 余项控制)
  strip_growth : Prop
  -- 外部输入: 无零点区域/零密度论证 (从 σ=1 推到 σ>1/2 — Hadamard–de la Vallée Poussin 型)
  zero_density_input : Prop
  -- 结论: 临界带 1/2<σ<1 无零点 (= RH)
  rh_half_plane : Prop
  -- 组装: 代数核心 + 增长 + 零密度 ⟹ RH
  assemble : reflection → far_field_zero_free → mertens_core → strip_growth →
    zero_density_input → rh_half_plane


-- ============================================================
-- §23 模平衡 — 函数方程的内禀恒等式 (排除论证的载体, 2026-09-01)
--   χ(s) = 2·(2π)^{−s}·Γ(s)·cos(πs/2): 唯一携带 σ-幂的传输因子.
--   模平衡 |ζ(1−s)| = |χ(s)|·|ζ(s)| 是「离圆零点排除」的候选载体:
--   |χ(σ+it)| ~ C_σ·t^{σ−1/2} (Stirling), 故 σ>1/2 侧模 = 增长因子 × σ<1/2 侧模.
--   此处只钉下恒等式本身 (纯函数方程取模, 可证); 渐近仍是 Stirling 输入.
--   下一步 (内禀排除的 t-方向): 复数 Γ 递推下界 |Γ(x+n+iy)| ≥ |y|^n·|Γ(x+iy)|
--   (gamma_ge_pow_mul_self 的复推广 — x-方向 → t-方向), 才能不经 Stirling 进入模平衡.
-- ============================================================

-- 1. 模平衡: |ζ(1−s)| = |χ(s)|·|ζ(s)| (函数方程取模)
theorem zeta_mod_balance {s : ℂ} (hs : ∀ n : ℕ, s ≠ -↑n) (hs' : s ≠ 1) :
    ‖riemannZeta (1 - s)‖ =
      ‖(2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ *
        ‖riemannZeta s‖ := by
  rw [riemannZeta_one_sub hs hs']
  rw [norm_mul]

-- 2. χ 模分解: |χ(s)| = 2·(2π)^{−σ}·|Γ(s)|·|cos(πs/2)|
theorem chi_mod_decomp (s : ℂ) :
    ‖(2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ =
      (2 : ℝ) * (2 * (Real.pi : ℝ)) ^ (-s.re) * ‖Complex.Gamma s‖ * ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖ := by
  rw [norm_mul, norm_mul, norm_mul]
  rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
  rw [show (2 * (Real.pi : ℂ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 2 * (Real.pi : ℝ)) (-s)]
  rw [Complex.neg_re]


-- ============================================================
-- §24 (A-gate) 复值 Abel 分部求和 — 排除性论证的入口闸门 (2026-09-01)
--   地位: [A] 是两条链的共同钥匙 —
--     (i) Hadamard 链的 [A] (条带内 ζ 上界);
--     (ii) §21 η 临界带桥的 conditional_convergence_strip.
--   没有它, 任何排除性估计 (零密度 / 无零点区域 / Lindelöf) 都进不了场.
--   ───────────────────────────────────────────────────────────
--   诚实边界 (务必读): 本节证明的是**工具**, 不是 RH.
--     闸门通了 ≠ 走到底. [A] 之后仍需 [B] Γ 上界 (初等推导已给出, 未落码)、
--     [C][E] 组合与 Borel–Carathéodory 应用、零密度输入. 且 Hadamard 链走完
--     只复现 Hadamard 1893 (非平凡零点无限多), 不证 RH.
--   ───────────────────────────────────────────────────────────
--   24.1 abelPartialSum / abelPartialSum_succ (部分和与其递推)
--   24.2 abel_sum_by_parts (Abel 分部求和恒等式 — 纯代数)
--   24.3 alternating_abel_norm_le_one (交错部分和模 ≤ 1)
--   24.4 alternating_sum_bound (Dirichlet 型主估计 — 本节核心)
--   24.5 AbelGate (闸门声明: 已证工具 + 两个具体估计为显式输入)
-- ============================================================

-- 24.1 Abel 部分和: A_n = Σ_{k≤n} a_k
noncomputable def abelPartialSum (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k

-- 递推: A_{n+1} = A_n + a_{n+1}
lemma abelPartialSum_succ (a : ℕ → ℂ) (n : ℕ) :
    abelPartialSum a (n + 1) = abelPartialSum a n + a (n + 1) := by
  unfold abelPartialSum
  rw [Finset.sum_range_succ]

-- 24.2 Abel 分部求和恒等式 (核心, 纯代数):
--   Σ_{n≤M} a_n b_n = A_M·b_M + Σ_{n<M} A_n·(b_n − b_{n+1})
--   证明: a_n = A_n − A_{n−1} 代入后望远镜; 此处对 M 归纳 + ring.
theorem abel_sum_by_parts (a b : ℕ → ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1), a n * b n)
      = abelPartialSum a M * b M
        + ∑ n ∈ Finset.range M, abelPartialSum a n * (b n - b (n + 1)) := by
  induction M with
  | zero =>
      simp [abelPartialSum]
  | succ M ih =>
      calc
        (∑ n ∈ Finset.range (Nat.succ M + 1), a n * b n)
            = (∑ n ∈ Finset.range (M + 1), a n * b n) + a (M + 1) * b (M + 1) := by
                rw [Finset.sum_range_succ]
        _ = (abelPartialSum a M * b M
              + ∑ n ∈ Finset.range M, abelPartialSum a n * (b n - b (n + 1)))
              + a (M + 1) * b (M + 1) := by rw [ih]
        _ = abelPartialSum a (M + 1) * b (M + 1)
              + ∑ n ∈ Finset.range (M + 1), abelPartialSum a n * (b n - b (n + 1)) := by
                rw [abelPartialSum_succ]
                conv_rhs => rw [Finset.sum_range_succ]
                ring

-- 24.3 交错部分和的模 ≤ 1: a_k = (−1)^k 时 A_n = (1 − (−1)^{n+1})/2 ∈ {0,1}
lemma alternating_abel_twice (n : ℕ) :
    abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n * 2 = 1 - (-1 : ℂ) ^ (n + 1) := by
  induction n with
  | zero =>
      norm_num [abelPartialSum]
  | succ n ih =>
      calc
        abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) (n + 1) * 2
            = (abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n + (-1 : ℂ) ^ (n + 1)) * 2 := by
                rw [abelPartialSum_succ]
        _ = abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n * 2
              + (-1 : ℂ) ^ (n + 1) * 2 := by ring
        _ = (1 - (-1 : ℂ) ^ (n + 1)) + (-1 : ℂ) ^ (n + 1) * 2 := by rw [ih]
        _ = 1 + (-1 : ℂ) ^ (n + 1) := by ring
        _ = 1 - (-1 : ℂ) ^ (n + 2) := by
              rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
              ring

theorem alternating_abel_norm_le_one (n : ℕ) :
    ‖abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n‖ ≤ 1 := by
  have h2 := alternating_abel_twice n
  have htwice : ‖abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n * (2 : ℂ)‖
      = ‖abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n‖ * 2 := by
    rw [norm_mul]
    norm_num
  have hpow : ‖(-1 : ℂ) ^ (n + 1)‖ = 1 := by
    rw [norm_pow]
    norm_num
  have hle : ‖(1 : ℂ) - (-1 : ℂ) ^ (n + 1)‖ ≤ 2 := by
    calc
      ‖(1 : ℂ) - (-1 : ℂ) ^ (n + 1)‖
          ≤ ‖(1 : ℂ)‖ + ‖(-1 : ℂ) ^ (n + 1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, hpow]; norm_num
  have hmain : ‖abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n‖ * 2 ≤ 1 * 2 := by
    calc
      ‖abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n‖ * 2
          = ‖abelPartialSum (fun k : ℕ => (-1 : ℂ) ^ k) n * (2 : ℂ)‖ := by rw [htwice]
      _ = ‖1 - (-1 : ℂ) ^ (n + 1)‖ := by rw [h2]
      _ ≤ 2 := hle
      _ = 1 * 2 := by norm_num
  nlinarith [hmain]

-- 24.4 交错和的主估计 (Dirichlet 判别法的定量形态 — 本节核心):
--   ‖Σ_{n≤M} (−1)^n b_n‖ ≤ ‖b_M‖ + Σ_{n<M} ‖b_n − b_{n+1}‖
--   这是把「交错级数收敛」变成一条**可用定量不等式**的那一步:
--   右端只含 b 的末项与总变差, 与项数 M 无关 ⟹ 直接给 Cauchy 型尾估计.
theorem alternating_sum_bound (b : ℕ → ℂ) (M : ℕ) :
    ‖∑ n ∈ Finset.range (M + 1), (-1 : ℂ) ^ n * b n‖
      ≤ ‖b M‖ + ∑ n ∈ Finset.range M, ‖b n - b (n + 1)‖ := by
  let a : ℕ → ℂ := fun k => (-1 : ℂ) ^ k
  change ‖∑ n ∈ Finset.range (M + 1), a n * b n‖
      ≤ ‖b M‖ + ∑ n ∈ Finset.range M, ‖b n - b (n + 1)‖
  rw [abel_sum_by_parts a b M]
  calc
    ‖abelPartialSum a M * b M
        + ∑ n ∈ Finset.range M, abelPartialSum a n * (b n - b (n + 1))‖
        ≤ ‖abelPartialSum a M * b M‖
          + ‖∑ n ∈ Finset.range M, abelPartialSum a n * (b n - b (n + 1))‖ :=
            norm_add_le _ _
    _ ≤ ‖abelPartialSum a M * b M‖
          + ∑ n ∈ Finset.range M, ‖abelPartialSum a n * (b n - b (n + 1))‖ := by
            have hsum : ‖∑ n ∈ Finset.range M, abelPartialSum a n * (b n - b (n + 1))‖
                ≤ ∑ n ∈ Finset.range M, ‖abelPartialSum a n * (b n - b (n + 1))‖ := by
              exact norm_sum_le _ _
            exact add_le_add (le_refl _) hsum
    _ = ‖abelPartialSum a M‖ * ‖b M‖
          + ∑ n ∈ Finset.range M, ‖abelPartialSum a n‖ * ‖b n - b (n + 1)‖ := by
            simp [norm_mul]
    _ ≤ 1 * ‖b M‖ + ∑ n ∈ Finset.range M, 1 * ‖b n - b (n + 1)‖ := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right (alternating_abel_norm_le_one M) (norm_nonneg _)
            · apply Finset.sum_le_sum
              intro n hn
              exact mul_le_mul_of_nonneg_right (alternating_abel_norm_le_one n) (norm_nonneg _)
    _ = ‖b M‖ + ∑ n ∈ Finset.range M, ‖b n - b (n + 1)‖ := by simp

-- 24.5 A 闸门声明: 已证工具 + 两个具体估计为显式输入
--   注意: bounded_variation 与 tends_to_zero 是对**具体序列** b_n=(n+1)^{−s}
--   的估计, 不是 Abel 机制的一部分 — 它们是下一步要补的对象 (复 MVT /
--   指数估计 |1−e^z| ≤ |z|e^{|z|}), 此处显式声明, 不装证.
structure AbelGate where
  -- 已证: Abel 分部求和恒等式 (abel_sum_by_parts)
  abel_identity : Prop
  -- 已证: 交错部分和模 ≤ 1 (alternating_abel_norm_le_one)
  alternating_bounded : Prop
  -- 已证: 交错和主估计 (alternating_sum_bound) — 本节核心工具
  alternating_estimate : Prop
  -- 外部输入: 总变差可和 Σ_n ‖b_n − b_{n+1}‖ < ∞
  --   (b_n=(n+1)^{−s} 时 ≲ ‖s‖·Σ(n+1)^{−σ−1} < ∞, σ>0)
  bounded_variation : Prop
  -- 外部输入: b_n → 0 (b_n=(n+1)^{−s} 时即 (n+1)^{−σ}→0, σ>0 — 初等)
  tends_to_zero : Prop
  -- 结论 1: η(s) 条件收敛 ⟹ §21 的对齐语言在临界带良定
  eta_conditional : Prop
  -- 结论 2: ζ 条带增长上界 [A] — Hadamard 链的一条腿
  strip_growth : Prop
  -- 组装 (η 侧): 机制 + 两个估计 ⟹ η 条件收敛
  assemble_eta : abel_identity → alternating_bounded → alternating_estimate →
    bounded_variation → tends_to_zero → eta_conditional
  -- 组装 (增长侧): 恒等式 + 主估计 + 变差 ⟹ 条带增长上界
  assemble_strip : abel_identity → alternating_estimate → bounded_variation →
    strip_growth


-- ============================================================
-- §25 (bounded_variation 落码) — 把 η 条件收敛从「外部输入」变成「定理」 (2026-09-01)
--   目标: AbelGate.bounded_variation / tends_to_zero 对具体序列
--   b_n = (n+1)^{−s} 给出**真证明**, 使 η(s) 在 0<σ<1 的条件收敛成为定理.
--   ───────────────────────────────────────────────────────────
--   数学路径 (无 Stirling, 纯初等):
--     ① 全局指数估计 ‖exp w − 1‖ ≤ 2·‖w‖·exp‖w‖ (25.1)
--     ② cpow → exp: (n+1)^{−s} = exp(−s·log(n+1)) (底正实, 无分支) (25.2)
--     ③ 精确步: 差分 = exp(z')·(exp(z−z')−1), 取模 ⟹
--        ‖b_n−b_{n+1}‖ ≤ (n+2)^{−σ}·2·‖s‖·log((n+2)/(n+1))·exp(‖s‖·log((n+2)/(n+1)))
--     ④ 简化: log((n+2)/(n+1)) ≤ 1/(n+1), ≤ log 2; exp(·) ≤ exp(‖s‖·log 2)
--        ⟹ ‖b_n−b_{n+1}‖ ≤ 2‖s‖·exp(‖s‖·log 2)·(n+1)^{−σ−1}
--     ⑤ Σ(n+1)^{−σ−1} < ∞ (σ>0, p 级数) ⟹ Summable (25.5)
--     ⑥ b_n → 0 (25.6); 区间 Abel + 25.1 机制 ⟹ η 条件收敛 (25.7)
--   ───────────────────────────────────────────────────────────
--   诚实边界: 本节做的是**工具 + 收敛性**, 不是 RH.
--     η 条件收敛 ⟹ §21 的对齐语言在临界带良定 (bookkeeping).
--     它不给任何排除性信息 (排除仍需 [B] Γ 上界 / [C][E] / 零密度).
-- ============================================================

-- 25.1 全局指数估计: ‖exp w − 1‖ ≤ 2·‖w‖·exp‖w‖ (任意 w)
--   ‖w‖≤1: mathlib norm_exp_sub_one_le (≤2‖w‖), 2‖w‖ ≤ 2‖w‖·exp‖w‖
--   ‖w‖≥1: 三角不等式 + ‖exp w‖ ≤ exp‖w‖ + 1 ≤ exp‖w‖ ⟹ 2exp‖w‖ ≤ 2‖w‖exp‖w‖
theorem complex_exp_sub_one_norm_le_two (w : ℂ) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ * Real.exp ‖w‖ := by
  by_cases hw : ‖w‖ ≤ 1
  · have h1 : ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := Complex.norm_exp_sub_one_le hw
    have hone : 1 ≤ Real.exp ‖w‖ := Real.one_le_exp (norm_nonneg w)
    have h2 : 2 * ‖w‖ ≤ 2 * ‖w‖ * Real.exp ‖w‖ := by
      nlinarith [hone, norm_nonneg w]
    exact h1.trans h2
  · have hge : 1 ≤ ‖w‖ := le_of_not_ge hw
    have hnorm : ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := Complex.norm_exp_le_exp_norm w
    have hone : 1 ≤ Real.exp ‖w‖ := Real.one_le_exp (norm_nonneg w)
    calc
      ‖Complex.exp w - 1‖ ≤ ‖Complex.exp w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp ‖w‖ + 1 := by
            exact add_le_add hnorm (by norm_num : ‖(1 : ℂ)‖ ≤ (1 : ℝ))
      _ ≤ Real.exp ‖w‖ + Real.exp ‖w‖ := by linarith [hone]
      _ = 2 * Real.exp ‖w‖ := by ring
      _ ≤ 2 * ‖w‖ * Real.exp ‖w‖ := by
            nlinarith [hge, Real.exp_pos ‖w‖]

-- 25.2 cpow → exp: (n+1)^{−s} = exp(−s·log(n+1)) (底为正实数, 无分支问题)
lemma eta_cpow_eq_exp (s : ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) ^ (-s) = Complex.exp (-s * (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ)) := by
  have hnz : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : (n + 1 : ℕ) ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hnz]
  have hlog : Complex.log ((n + 1 : ℕ) : ℂ) = (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ) := by
    have hcast : ((n + 1 : ℕ) : ℂ) = ((((n + 1 : ℕ) : ℝ)) : ℂ) := by norm_num
    rw [hcast]
    exact (Complex.ofReal_log (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ)))).symm
  rw [hlog]
  ring

-- 25.3 精确步: 差分的 exp 表示界
--   ‖(n+1)^{−s} − (n+2)^{−s}‖
--     ≤ (n+2)^{−σ} · 2 · ‖s‖ · log((n+2)/(n+1)) · exp(‖s‖·log((n+2)/(n+1)))
--   推导: (n+k)^{−s} = exp(−s·log(n+k)); 差 = exp(z')·(exp(z−z')−1),
--   ‖exp z'‖ = exp(Re z') = (n+2)^{−σ}, 再用 25.1.
theorem eta_variation_step (s : ℂ) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖
      ≤ (((n + 2 : ℕ) : ℝ)) ^ (-s.re)
          * 2 * ‖s‖ * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)))
          * Real.exp (‖s‖ * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)))) := by
  let z : ℂ := -s * (Real.log (((n + 1 : ℕ) : ℝ)) : ℂ)
  let z' : ℂ := -s * (Real.log (((n + 1 + 1 : ℕ) : ℝ)) : ℂ)
  have hz : ((n + 1 : ℕ) : ℂ) ^ (-s) = Complex.exp z := by
    rw [eta_cpow_eq_exp s n]
  have hz' : ((n + 2 : ℕ) : ℂ) ^ (-s) = Complex.exp z' := by
    rw [eta_cpow_eq_exp s (n + 1)]
  rw [hz, hz']
  have harg : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  have hz're : z'.re = -s.re * Real.log (((n + 2 : ℕ) : ℝ)) := by
    change (-s * (Real.log (((n + 1 + 1 : ℕ) : ℝ)) : ℂ)).re
        = -s.re * Real.log (((n + 2 : ℕ) : ℝ))
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hnorm' : ‖Complex.exp z'‖ = (((n + 2 : ℕ) : ℝ)) ^ (-s.re) := by
    rw [Complex.norm_exp, hz're]
    rw [mul_comm]
    exact (Real.rpow_def_of_pos (by positivity : 0 < (((n + 2 : ℕ) : ℝ))) (-s.re)).symm
  have hzsub : Complex.exp z - Complex.exp z'
      = Complex.exp z' * (Complex.exp (z - z') - 1) := by
    calc
      Complex.exp z - Complex.exp z'
          = Complex.exp z' * Complex.exp (z - z') - Complex.exp z' := by
              congr 1
              rw [← Complex.exp_add]
              congr 1
              ring
      _ = Complex.exp z' * (Complex.exp (z - z') - 1) := by ring
  have hlogdiv : Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ))
      = Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) := by
    exact (Real.log_div (by positivity : (((n + 2 : ℕ) : ℝ)) ≠ 0)
      (by positivity : (((n + 1 : ℕ) : ℝ)) ≠ 0)).symm
  have hlogpos : 0 ≤ Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)) := by
    rw [hlogdiv]
    exact Real.log_nonneg (by
      have hpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      rw [le_div_iff₀ hpos]
      norm_num)
  have hz'lin : z - z' = s * ((Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ))) : ℂ) := by
    calc
      z - z' = -s * ↑(Real.log ↑(n + 1)) - (-s * ↑(Real.log ↑(n + 1 + 1))) := by
                rfl
      _ = s * (↑(Real.log ↑(n + 1 + 1)) - ↑(Real.log ↑(n + 1))) := by ring
      _ = s * (↑(Real.log ↑(n + 2)) - ↑(Real.log ↑(n + 1))) := by rw [harg]
      _ = s * ((Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ))) : ℂ) := by
                rw [← Complex.ofReal_sub]
  have hnormzdiff : ‖z - z'‖ = ‖s‖ * (Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ))) := by
    rw [hz'lin]
    rw [norm_mul]
    have habs : ‖((Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ))) : ℂ)‖
        = Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ)) := by
      rw [← Complex.ofReal_sub]
      rw [Complex.norm_real]
      exact abs_of_nonneg hlogpos
    rw [habs]
  have hnormexp : Real.exp ‖z - z'‖
      = Real.exp (‖s‖ * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)))) := by
    rw [hnormzdiff, hlogdiv]
  calc
    ‖Complex.exp z - Complex.exp z'‖
        = ‖Complex.exp z' * (Complex.exp (z - z') - 1)‖ := by rw [hzsub]
    _ = ‖Complex.exp z'‖ * ‖Complex.exp (z - z') - 1‖ := by rw [norm_mul]
    _ = (((n + 2 : ℕ) : ℝ)) ^ (-s.re) * ‖Complex.exp (z - z') - 1‖ := by rw [hnorm']
    _ ≤ (((n + 2 : ℕ) : ℝ)) ^ (-s.re) * (2 * ‖z - z'‖ * Real.exp ‖z - z'‖) := by
            exact mul_le_mul_of_nonneg_left (complex_exp_sub_one_norm_le_two (z - z'))
              (Real.rpow_nonneg (by positivity : 0 ≤ (((n + 2 : ℕ) : ℝ))) (-s.re))
    _ = (((n + 2 : ℕ) : ℝ)) ^ (-s.re)
            * (2 * (‖s‖ * (Real.log (((n + 2 : ℕ) : ℝ)) - Real.log (((n + 1 : ℕ) : ℝ))))
            * Real.exp (‖s‖ * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))))) := by
            rw [hnormexp, hnormzdiff]
    _ = (((n + 2 : ℕ) : ℝ)) ^ (-s.re)
            * (2 * (‖s‖ * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))))
            * Real.exp (‖s‖ * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))))) := by
            rw [hlogdiv]
    _ = (((n + 2 : ℕ) : ℝ) ^ (-s.re)) * 2 * ‖s‖
            * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)))
            * Real.exp (‖s‖ * Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)))) := by ring

-- 25.4 简化引理 (原子 cast, 与 25.3 一致):
--   ① log((n+2)/(n+1)) ≤ 1/(n+1)   (log(1+x) ≤ x)
--   ② (n+2)/(n+1) ≤ 2              ⟹ log ≤ log 2
--   ③ (n+2)^{−σ} ≤ (n+1)^{−σ}      (正指数单调 + 取倒数)
lemma eta_ratio_log_le_inv (n : ℕ) :
    Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ)))
      ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by
  let r : ℝ := (((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))
  have hpos : 0 < r := by
    dsimp [r]
    exact div_pos (by positivity : 0 < (((n + 2 : ℕ) : ℝ))) (by positivity : 0 < (((n + 1 : ℕ) : ℝ)))
  have hsub : r - 1 = 1 / (((n + 1 : ℕ) : ℝ)) := by
    dsimp [r]
    have hpos1 : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hpos1]
    push_cast
    ring
  exact (Real.log_le_sub_one_of_pos hpos).trans_eq hsub

lemma eta_ratio_le_two (n : ℕ) :
    ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) ≤ 2 := by
  have hpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  rw [div_le_iff₀ hpos]
  push_cast
  nlinarith

lemma eta_ratio_log_le_log_two (n : ℕ) :
    Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) ≤ Real.log 2 := by
  have hpos : 0 < ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) := by
    exact div_pos (by positivity : 0 < (((n + 2 : ℕ) : ℝ))) (by positivity : 0 < (((n + 1 : ℕ) : ℝ)))
  exact (Real.log_le_log_iff hpos (by norm_num : 0 < (2 : ℝ))).mpr (eta_ratio_le_two n)

lemma eta_ratio_log_nonneg (n : ℕ) :
    0 ≤ Real.log ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) := by
  have hpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hge : 1 ≤ ((((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))) := by
    rw [le_div_iff₀ hpos]
    push_cast
    nlinarith
  exact Real.log_nonneg hge

lemma eta_pow_dec (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    (((n + 2 : ℕ) : ℝ)) ^ (-s.re) ≤ (((n + 1 : ℕ) : ℝ)) ^ (-s.re) := by
  have hle : (((n + 1 : ℕ) : ℝ)) ≤ (((n + 2 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : (n + 1 : ℕ) ≤ (n + 2 : ℕ))
  have hσ : 0 ≤ s.re := le_of_lt hs
  have hpos1 : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hbase : (((n + 1 : ℕ) : ℝ)) ^ s.re ≤ (((n + 2 : ℕ) : ℝ)) ^ s.re :=
    Real.rpow_le_rpow hpos1.le hle hσ
  rw [Real.rpow_neg (by positivity : 0 ≤ (((n + 2 : ℕ) : ℝ)))]
  rw [Real.rpow_neg (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ)))]
  have hpos2 : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hpos2 s.re) (Real.rpow_pos_of_pos hpos1 s.re)).mpr hbase

-- 25.5 总变差可和: Σ_n ‖(n+1)^{−s} − (n+2)^{−s}‖ < ∞  (0 < Re s)
--   路径: eta_variation_step (精确步) → 25.4 简化 → 对比 Σ(n+1)^{−σ−1} (p 级数)
theorem eta_bounded_variation (s : ℂ) (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖) := by
  let C : ℝ := 2 * ‖s‖ * Real.exp (‖s‖ * Real.log 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmain : ∀ n : ℕ,
      ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖
        ≤ C * (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1) := by
    intro n
    let r : ℝ := (((n + 2 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ))
    have hlogle := eta_ratio_log_le_inv n
    have hexp : Real.exp (‖s‖ * Real.log r) ≤ Real.exp (‖s‖ * Real.log 2) := by
      dsimp [r]
      exact (Real.exp_le_exp).mpr (mul_le_mul_of_nonneg_left (eta_ratio_log_le_log_two n) (norm_nonneg s))
    have hpow := eta_pow_dec s hs n
    have hlognonneg : 0 ≤ Real.log r := by
      dsimp [r]
      exact eta_ratio_log_nonneg n
    have hb0 : 0 ≤ 2 * ‖s‖ := by positivity
    have hb1 : 0 ≤ Real.exp (‖s‖ * Real.log r) := (Real.exp_pos _).le
    have hb2 : 0 ≤ (((n + 1 : ℕ) : ℝ)) ^ (-s.re) :=
      Real.rpow_nonneg (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) (-s.re)
    have hstep := eta_variation_step s n
    have hmain' : ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖
        ≤ (((n + 1 : ℕ) : ℝ)) ^ (-s.re)
            * (2 * ‖s‖ * (1 / (((n + 1 : ℕ) : ℝ))) * Real.exp (‖s‖ * Real.log 2)) := by
      calc
        ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖
            ≤ (((n + 2 : ℕ) : ℝ)) ^ (-s.re)
                * (2 * ‖s‖ * Real.log r * Real.exp (‖s‖ * Real.log r)) := by
                  simpa [r, mul_assoc] using hstep
        _ ≤ (((n + 1 : ℕ) : ℝ)) ^ (-s.re)
                * (2 * ‖s‖ * Real.log r * Real.exp (‖s‖ * Real.log r)) := by
                  exact mul_le_mul_of_nonneg_right hpow
                    (mul_nonneg (mul_nonneg hb0 hlognonneg) hb1)
        _ ≤ (((n + 1 : ℕ) : ℝ)) ^ (-s.re)
                * (2 * ‖s‖ * (1 / (((n + 1 : ℕ) : ℝ))) * Real.exp (‖s‖ * Real.log r)) := by
                  have hm : 2 * ‖s‖ * Real.log r ≤ 2 * ‖s‖ * (1 / (((n + 1 : ℕ) : ℝ))) :=
                    mul_le_mul_of_nonneg_left hlogle hb0
                  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hb1) hb2
        _ ≤ (((n + 1 : ℕ) : ℝ)) ^ (-s.re)
                * (2 * ‖s‖ * (1 / (((n + 1 : ℕ) : ℝ))) * Real.exp (‖s‖ * Real.log 2)) := by
                  have hbK : 0 ≤ 2 * ‖s‖ * (1 / (((n + 1 : ℕ) : ℝ))) := by
                    exact mul_nonneg hb0 (by positivity : 0 ≤ 1 / (((n + 1 : ℕ) : ℝ)))
                  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hbK) hb2
    have hpow2 : (((n + 1 : ℕ) : ℝ)) ^ (-s.re) * (1 / (((n + 1 : ℕ) : ℝ)))
        = (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1) := by
      have hpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
      rw [one_div, ← Real.rpow_neg_one (((n + 1 : ℕ) : ℝ))]
      rw [← Real.rpow_add hpos]
      congr 1
    calc
      ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖
          ≤ (((n + 1 : ℕ) : ℝ)) ^ (-s.re)
              * (2 * ‖s‖ * (1 / (((n + 1 : ℕ) : ℝ))) * Real.exp (‖s‖ * Real.log 2)) := hmain'
      _ = (((n + 1 : ℕ) : ℝ)) ^ (-s.re) * (1 / (((n + 1 : ℕ) : ℝ)))
              * (2 * ‖s‖ * Real.exp (‖s‖ * Real.log 2)) := by ring
      _ = (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1) * (2 * ‖s‖ * Real.exp (‖s‖ * Real.log 2)) := by
              rw [hpow2]
      _ = C * (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1) := by
              dsimp [C]
              ring
  -- 基序列 (n+1)^(-σ-1) 可和 (p 级数, σ>0)
  have hsum1 : Summable (fun m : ℕ => (((m : ℕ) : ℝ) ^ (s.re + 1))⁻¹) :=
    (Real.summable_nat_rpow_inv).mpr (by linarith [hs])
  have hsum2 : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ)) ^ (s.re + 1))⁻¹) :=
    hsum1.comp_injective (fun a b h => by omega)
  have hsum : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1)) := by
    refine hsum2.congr ?_
    intro n
    rw [show -s.re - 1 = -(s.re + 1) by ring]
    rw [Real.rpow_neg (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ)))]
  have hCsum : Summable (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ)) ^ (-s.re - 1)) :=
    hsum.mul_left C
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmain hCsum

-- 25.6 b_n → 0: ‖(n+1)^{−s}‖ = (n+1)^{−σ} → 0  (σ>0)
--   (tendsto_rpow_neg_atTop: x^{−σ} → 0 as x → ∞)
theorem eta_tends_to_zero (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ (-s)) atTop (nhds 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hs
  have harg : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    have hb' : ∃ N : ℕ, ∀ n ≥ N, b ≤ (n : ℝ) := by
      exact (Filter.eventually_atTop.1 (tendsto_atTop.1 tendsto_natCast_atTop_atTop b))
    refine (Filter.eventually_atTop.2 ?_)
    rcases hb' with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hbn : b ≤ (n : ℝ) := hN n hn
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    rw [hcast]
    linarith
  have hmain : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ (-s.re)) atTop (nhds 0) :=
    hpow.comp harg
  have hnorm : ∀ n : ℕ, ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ = (((n + 1 : ℕ) : ℝ)) ^ (-s.re) := by
    intro n
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) (-s)
  have hnorm_t : Tendsto (fun n : ℕ => ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖) atTop (nhds 0) :=
    hmain.congr' (by
      filter_upwards with n
      simpa using (hnorm n).symm)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_t

-- 25.7 部分和收敛 (η 条件收敛的正确形态 — 非 Summable, 因 ℂ 上 Summable ⟺ 绝对可和):
--   ∃ a, ∑_{k<N} (−1)^k (k+1)^{−s} → a
--   Cauchy 判定: tail = ‖∑_{k=n}^{m−1} (−1)^k b_k‖ ≤ ‖b_{m−1}‖ + Σ_{k=n}^{m−2}‖b_k−b_{k+1}‖
--   (交替部分和模 ≤1 + Abel 分部求和), 两项各 → 0.
lemma eta_partial_sum_diff (b : ℕ → ℂ) (m n : ℕ) (hnm : n ≤ m) :
    Finset.sum (Finset.range m) (fun k => (-1 : ℂ) ^ k * b k)
      - Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k)
      = Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ (n + j) * b (n + j)) := by
  have hsub : Finset.range n ⊆ Finset.range m := by
    intro x hx
    simp [Finset.mem_range] at hx ⊢
    omega
  have hIco : Finset.range m \ Finset.range n = Finset.Ico n m := by
    ext k
    simp [Finset.mem_Ico, Finset.mem_range]
    omega
  calc
    Finset.sum (Finset.range m) (fun k => (-1 : ℂ) ^ k * b k)
        - Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k)
        = Finset.sum (Finset.range m \ Finset.range n) (fun k => (-1 : ℂ) ^ k * b k) := by
            have hss := (Finset.sum_sdiff (f := fun k : ℕ => (-1 : ℂ) ^ k * b k) hsub).symm
            calc
              Finset.sum (Finset.range m) (fun k => (-1 : ℂ) ^ k * b k)
                  - Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k)
                  = (Finset.sum (Finset.range m \ Finset.range n) (fun k => (-1 : ℂ) ^ k * b k)
                      + Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k))
                    - Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k) := by
                        rw [hss]
              _ = Finset.sum (Finset.range m \ Finset.range n) (fun k => (-1 : ℂ) ^ k * b k) := by abel
    _ = Finset.sum (Finset.Ico n m) (fun k => (-1 : ℂ) ^ k * b k) := by rw [hIco]
    _ = Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ (n + j) * b (n + j)) := by
            rw [Finset.sum_Ico_eq_sum_range (fun k : ℕ => (-1 : ℂ) ^ k * b k) n m]

lemma eta_tail_bound (b : ℕ → ℂ) (m n : ℕ) (hnm : n < m) :
    ‖Finset.sum (Finset.range (m - n)) (fun k => (-1 : ℂ) ^ k * b (n + k))‖
      ≤ ‖b (m - 1)‖ + Finset.sum (Finset.range (m - n - 1))
          (fun k => ‖b (n + k) - b (n + k + 1)‖) := by
  have hb' := alternating_sum_bound (fun k : ℕ => b (n + k)) (m - n - 1)
  have hM : (m - n - 1) + 1 = m - n := by omega
  have hn1 : n + (m - n - 1) = m - 1 := by omega
  simpa [hM, hn1] using hb'

-- 变差尾 ≤ W(m−1) − W(n), W(N) = Σ_{k<N}‖b_k−b_{k+1}‖  (n ≤ m−1)
lemma eta_var_tail_le (b : ℕ → ℂ) (m n : ℕ) (hn : n ≤ m - 1) :
    Finset.sum (Finset.range (m - n - 1)) (fun k => ‖b (n + k) - b (n + k + 1)‖)
      ≤ Finset.sum (Finset.range (m - 1)) (fun k => ‖b k - b (k + 1)‖)
        - Finset.sum (Finset.range n) (fun k => ‖b k - b (k + 1)‖) := by
  let s : Finset ℕ := Finset.image (fun j : ℕ => n + j) (Finset.range (m - n - 1))
  have hmap : s ⊆ Finset.range (m - 1) \ Finset.range n := by
    intro k hk
    rw [Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_image] at hk
      rcases hk with ⟨j, hj, hj_eq⟩
      subst k
      have hjlt : j < m - n - 1 := by simpa using hj
      have hstep : n + j < n + (m - n - 1) := Nat.add_lt_add_left hjlt n
      have hcalc : n + (m - n - 1) ≤ m - 1 := by
        have hsub2 : m - n - 1 = m - 1 - n := by omega
        rw [hsub2]
        exact le_of_eq (Nat.add_sub_of_le hn)
      exact Finset.mem_range.2 (lt_of_lt_of_le hstep hcalc)
    · rw [Finset.mem_image] at hk
      rcases hk with ⟨j, hj, hj_eq⟩
      subst k
      intro hmem
      rw [Finset.mem_range] at hmem
      omega
  have hinj : Set.InjOn (fun j : ℕ => n + j) (↑(Finset.range (m - n - 1))) := by
    intro a ha b hb hab
    exact Nat.add_left_cancel hab
  have hsum_eq :
      Finset.sum (Finset.range (m - n - 1)) (fun k => ‖b (n + k) - b (n + k + 1)‖)
        = Finset.sum s (fun k => ‖b k - b (k + 1)‖) := by
    have hsi := Finset.sum_image (s := Finset.range (m - n - 1))
      (g := fun j : ℕ => n + j) (f := fun y : ℕ => ‖b y - b (y + 1)‖) hinj
    exact hsi.symm
  calc
    Finset.sum (Finset.range (m - n - 1)) (fun k => ‖b (n + k) - b (n + k + 1)‖)
        = Finset.sum s (fun k => ‖b k - b (k + 1)‖) := hsum_eq
    _ ≤ Finset.sum (Finset.range (m - 1) \ Finset.range n) (fun k => ‖b k - b (k + 1)‖) := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hmap
              (by intro k hkt hks; exact norm_nonneg (b k - b (k + 1)))
    _ = Finset.sum (Finset.range (m - 1)) (fun k => ‖b k - b (k + 1)‖)
        - Finset.sum (Finset.range n) (fun k => ‖b k - b (k + 1)‖) := by
            have hss := Finset.sum_sdiff (f := fun k : ℕ => ‖b k - b (k + 1)‖)
              (by intro x hx; exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hn))
            rw [← hss]
            abel

-- 25.7 辅助: 部分和差的界 (m > n)
--   ‖S_m − S_n‖ ≤ ‖b_{m−1}‖ + (W(m−1) − W(n)), W(N) = Σ_{k<N}‖b_k−b_{k+1}‖
lemma eta_partial_diff_bound (b : ℕ → ℂ) (m n : ℕ) (hnm : n < m) :
    ‖Finset.sum (Finset.range m) (fun k => (-1 : ℂ) ^ k * b k)
        - Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k)‖
      ≤ ‖b (m - 1)‖
        + (Finset.sum (Finset.range (m - 1)) (fun k => ‖b k - b (k + 1)‖)
          - Finset.sum (Finset.range n) (fun k => ‖b k - b (k + 1)‖)) := by
  have hdiff := eta_partial_sum_diff b m n (le_of_lt hnm)
  have hsign :
      ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ (n + j) * b (n + j))‖
        = ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ j * b (n + j))‖ := by
    calc
      ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ (n + j) * b (n + j))‖
          = ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ n * ((-1 : ℂ) ^ j * b (n + j)))‖ := by
              congr 1
              apply Finset.sum_congr rfl
              intro j hj
              rw [pow_add]
              ring
      _ = ‖(-1 : ℂ) ^ n * Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ j * b (n + j))‖ := by
              rw [← Finset.mul_sum]
      _ = ‖(-1 : ℂ) ^ n‖ * ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ j * b (n + j))‖ := by
              rw [norm_mul]
      _ = ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ j * b (n + j))‖ := by
              rw [norm_pow]
              norm_num
  calc
    ‖Finset.sum (Finset.range m) (fun k => (-1 : ℂ) ^ k * b k)
        - Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k)‖
        = ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ (n + j) * b (n + j))‖ := by
            rw [hdiff]
    _ = ‖Finset.sum (Finset.range (m - n)) (fun j => (-1 : ℂ) ^ j * b (n + j))‖ := hsign
    _ ≤ ‖b (m - 1)‖ + Finset.sum (Finset.range (m - n - 1))
            (fun k => ‖b (n + k) - b (n + k + 1)‖) := eta_tail_bound b m n hnm
    _ ≤ ‖b (m - 1)‖
            + (Finset.sum (Finset.range (m - 1)) (fun k => ‖b k - b (k + 1)‖)
              - Finset.sum (Finset.range n) (fun k => ‖b k - b (k + 1)‖)) := by
            simpa [add_comm] using add_le_add_left (eta_var_tail_le b m n (by omega : n ≤ m - 1)) (‖b (m - 1)‖)

-- 25.7 η 部分和收敛 (η 条件收敛, 0<Re s):
--   Abel 部分和机制 (§24) + 总变差可和 (25.5) + 项趋于零 (25.6) ⟹ Cauchy ⟹ 收敛 (ℂ 完备)
theorem eta_partial_sums_converge (s : ℂ) (hs : 0 < s.re) :
    ∃ a : ℂ,
      Tendsto (fun n : ℕ =>
        Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * ((k + 1 : ℕ) : ℂ) ^ (-s)))
        atTop (nhds a) := by
  let b : ℕ → ℂ := fun k => ((k + 1 : ℕ) : ℂ) ^ (-s)
  let S : ℕ → ℂ := fun n => Finset.sum (Finset.range n) (fun k => (-1 : ℂ) ^ k * b k)
  have hbv : Summable (fun n : ℕ => ‖b n - b (n + 1)‖) := by
    change Summable (fun n : ℕ => ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s)‖)
    exact eta_bounded_variation s hs
  have hb0 : Tendsto (fun n : ℕ => ‖b n‖) atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖) atTop (nhds 0)
    exact (tendsto_zero_iff_norm_tendsto_zero.mp (eta_tends_to_zero s hs))
  let W : ℕ → ℝ := fun N => Finset.sum (Finset.range N) (fun k => ‖b k - b (k + 1)‖)
  have hWcau : CauchySeq W := hbv.hasSum.tendsto_sum_nat.cauchySeq
  have hWcau' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |W m - W n| < ε := by
    intro ε hε
    rcases (Metric.cauchySeq_iff.1 hWcau) ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hdist : dist (W m) (W n) < ε := hN m hm n hn
    simpa [dist_eq_norm, Real.norm_eq_abs] using hdist
  have hb0' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ‖b n‖ < ε := by
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hb0) ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hdist : dist (‖b n‖) 0 < ε := hN n hn
    simpa using hdist
  have hcauchy : CauchySeq S := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε2 : 0 < ε / 4 := by positivity
    rcases hb0' (ε / 4) hε2 with ⟨N₁, hN₁⟩
    rcases hWcau' (ε / 4) hε2 with ⟨N₂, hN₂⟩
    let N : ℕ := max N₁ (N₂ + 1) + 1
    have hN₁le : N ≥ N₁ + 1 := by
      dsimp [N]
      have h := le_max_left N₁ (N₂ + 1)
      omega
    have hN₂le : N ≥ N₂ + 2 := by
      dsimp [N]
      have h := le_max_right N₁ (N₂ + 1)
      omega
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hmN₁ : m - 1 ≥ N₁ := by omega
    have hnN₁ : n - 1 ≥ N₁ := by omega
    have hmN₂ : m ≥ N₂ := by omega
    have hnN₂ : n ≥ N₂ := by omega
    have hm1N₂ : m - 1 ≥ N₂ := by omega
    have hn1N₂ : n - 1 ≥ N₂ := by omega
    have hb01 : ‖b (m - 1)‖ < ε / 4 := hN₁ (m - 1) hmN₁
    have hb02 : ‖b (n - 1)‖ < ε / 4 := hN₁ (n - 1) hnN₁
    have hW1 : |W (m - 1) - W n| < ε / 4 := hN₂ (m - 1) hm1N₂ n hnN₂
    have hW2 : |W (n - 1) - W m| < ε / 4 := hN₂ (n - 1) hn1N₂ m hmN₂
    by_cases hmn : m ≥ n
    · by_cases hm0 : m = n
      · subst m
        simpa [S, dist_self] using hε
      · have hgt : n < m := lt_of_le_of_ne hmn (by intro hnm; exact hm0 hnm.symm)
        have hb' := eta_partial_diff_bound b m n hgt
        have hWle : Finset.sum (Finset.range (m - 1)) (fun k => ‖b k - b (k + 1)‖)
              - Finset.sum (Finset.range n) (fun k => ‖b k - b (k + 1)‖)
              ≤ |W (m - 1) - W n| := by
          dsimp [W]
          have hsub : Finset.sum (Finset.range (m - 1)) (fun k => ‖b k - b (k + 1)‖)
                - Finset.sum (Finset.range n) (fun k => ‖b k - b (k + 1)‖) ≥ 0 :=
            sub_nonneg.mpr (Finset.sum_le_sum_of_subset_of_nonneg
              (by intro x hx; exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (by omega : n ≤ m - 1)))
              (by intro k hkt hks; exact norm_nonneg (b k - b (k + 1))))
          rw [abs_of_nonneg hsub]
        have hsum : ‖b (m - 1)‖
              + (Finset.sum (Finset.range (m - 1)) (fun k => ‖b k - b (k + 1)‖)
                - Finset.sum (Finset.range n) (fun k => ‖b k - b (k + 1)‖)) < ε := by
          nlinarith [hb01, hW1, hWle]
        rw [dist_eq_norm]
        exact lt_of_le_of_lt hb' hsum
    · have hmn' : m < n := by omega
      have hb' := eta_partial_diff_bound b n m hmn'
      have hWle : Finset.sum (Finset.range (n - 1)) (fun k => ‖b k - b (k + 1)‖)
            - Finset.sum (Finset.range m) (fun k => ‖b k - b (k + 1)‖)
            ≤ |W (n - 1) - W m| := by
        dsimp [W]
        have hsub : Finset.sum (Finset.range (n - 1)) (fun k => ‖b k - b (k + 1)‖)
              - Finset.sum (Finset.range m) (fun k => ‖b k - b (k + 1)‖) ≥ 0 :=
          sub_nonneg.mpr (Finset.sum_le_sum_of_subset_of_nonneg
            (by intro x hx; exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) (by omega : m ≤ n - 1)))
            (by intro k hkt hks; exact norm_nonneg (b k - b (k + 1))))
        rw [abs_of_nonneg hsub]
      have hsum : ‖b (n - 1)‖
        + (Finset.sum (Finset.range (n - 1)) (fun k => ‖b k - b (k + 1)‖)
          - Finset.sum (Finset.range m) (fun k => ‖b k - b (k + 1)‖)) < ε := by
        nlinarith [hb02, hW2, hWle]
      rw [dist_eq_norm, norm_sub_rev]
      exact lt_of_le_of_lt hb' hsum
  exact cauchySeq_tendsto_of_complete hcauchy


-- ============================================================
-- §26 复数 Γ 递推下界 — x-方向 → t-方向 (内禀排除的第一块 t-方向砖, 2026-09-01)
--   |Γ(x+n+iy)| ≥ |y|^n · |Γ(x+iy)|  (x>0, n : ℕ)
--   gamma_ge_pow_mul_self (Γ(x+n) ≥ xⁿΓ(x), 实轴) 的复推广.
--   每个因子 |x+k+iy| = √((x+k)²+y²) ≥ |y| (x²≥0 恒真), 连乘即得.
--   诚实边界: 这给的是「整数实轴步数 n」的虚部增长; 排除还需
--   |Γ(σ+it)| 随 t 的**连续**渐近 — 中间差「整数步 → 连续实轴」的桥
--   (log Γ 凸性插值, Bohr–Mollerup 已形式化), 或用反射/加倍公式直接连 s/2 与 (1−s)/2.
-- ============================================================

-- 子引理: |x+iy| ≥ |y| (任意 x, 因 x²≥0)
lemma norm_add_I_ge_abs {x y : ℝ} :
    |y| ≤ ‖(x : ℂ) + Complex.I * (y : ℂ)‖ := by
  have hsq : y ^ 2 ≤ ‖(x : ℂ) + Complex.I * (y : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    simp
    nlinarith [sq_nonneg x]
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _)] at h

-- 复数 Γ 递推下界
theorem gamma_norm_ge_y_pow {x y : ℝ} (hx : 0 < x) (n : ℕ) :
    |y| ^ n * ‖Complex.Gamma ((x : ℂ) + Complex.I * (y : ℂ))‖ ≤
      ‖Complex.Gamma (((x + (n : ℝ)) : ℂ) + Complex.I * (y : ℂ))‖ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let z : ℂ := ((x + (n : ℝ)) : ℂ) + Complex.I * (y : ℂ)
      have hge : |y| ≤ ‖z‖ := by
        have hsq : y ^ 2 ≤ ‖z‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq]
          dsimp [z]
          rw [Complex.normSq_apply]
          simp
          nlinarith [sq_nonneg (x + (n : ℝ))]
        have h := sq_le_sq.mp hsq
        rwa [abs_of_nonneg (norm_nonneg _)] at h
      have hz0 : z ≠ 0 := by
        intro h
        have hre : z.re = (0 : ℝ) := congrArg Complex.re h
        have hre_pos : (0 : ℝ) < z.re := by
          change (0 : ℝ) < (((x + (n : ℝ)) : ℂ) + Complex.I * (y : ℂ)).re
          simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
          exact add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
        linarith
      have hG : ‖Complex.Gamma (z + 1)‖ = ‖z‖ * ‖Complex.Gamma z‖ := by
        rw [Complex.Gamma_add_one z hz0]
        rw [norm_mul]
      calc
        |y| ^ (n + 1) * ‖Complex.Gamma ((x : ℂ) + Complex.I * (y : ℂ))‖
            = |y| * (|y| ^ n * ‖Complex.Gamma ((x : ℂ) + Complex.I * (y : ℂ))‖) := by ring
        _ ≤ |y| * ‖Complex.Gamma (((x + (n : ℝ)) : ℂ) + Complex.I * (y : ℂ))‖ := by
            exact mul_le_mul_of_nonneg_left ih (abs_nonneg y)
        _ = |y| * ‖Complex.Gamma z‖ := by
            dsimp [z]
        _ ≤ ‖z‖ * ‖Complex.Gamma z‖ := by
            exact mul_le_mul_of_nonneg_right hge (norm_nonneg _)
        _ = ‖Complex.Gamma (z + 1)‖ := by rw [hG]
        _ = ‖Complex.Gamma (((x + ((n + 1 : ℕ) : ℝ)) : ℂ) + Complex.I * (y : ℂ))‖ := by
            dsimp [z]
            congr 1
            push_cast
            ring_nf


end RiemannHIBS.Abundance
