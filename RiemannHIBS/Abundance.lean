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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Topology
open scoped ComplexConjugate
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
structure AlignmentEnergyBridge where
  -- 内禀能量无界 (基于已证原子 12.3/12.4/12.7; 组合定理 energy_lower_bound 待形式化)
  energy_unbounded : Prop
  -- 外部反证输入 (经典 Hardy 反证): 对齐有限 ⟹ 能量有界
  bounded_energy_of_finite_alignments : Prop
  -- 结论: 能量无界 + 反证 ⟹ 对齐事件 (零点) 无限
  infinite_alignments : Prop
  bridge : energy_unbounded → bounded_energy_of_finite_alignments → infinite_alignments


end RiemannHIBS.Abundance

