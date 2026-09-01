-- RiemannHIBS.RadialEnergy — 隐数径向偏移的正定能量路线 (2026-09-01)
--
-- 主路线 (leo 指示, 替换"有限 Dirichlet 部分和统一逼近"路线):
--   零点 ρ = 1/2 + u + iθ,  u = 径向偏移 (隐数空间独有变量), θ = 高度.
--   排除结构 = 显式公式 + 正性 + 总量为零 ⟹ 径向偏移为零:
--     E_T = Σ_{|θ_ρ|≤T} K_T(θ_ρ)·u_ρ²,  K_T > 0
--     若从显式公式 (素数侧/ξ 积分侧) 推出 E_T = 0,
--     则每项 K_T·u² = 0 ⟹ u_ρ = 0 ⟹ 零点在临界线.
--   理由: 有限 Dirichlet 部分和在临界带结构性失败 (不绝对收敛 + 近似可能
--   接近零, HiddenExclusion.critical_lifted_terms_not_summable 已钉死);
--   正定能量把"排除"拆成"恒等式 + 正性 + 总量为零"三条腿, 每条独立可攻.
--
-- 本轮落码: ①加权能量接口 (有限零点多重集) ②测试核正定 (tentKernel)
--   ③RadialExplicitFormula 钉形状 ④条件定理 (能量恒为零 ⟹ 零点在临界线).
--   诚实: 显式公式本身 (E_T=0 的来源) 是外部输入, 未构造.

import RiemannHIBS.HiddenExclusion

open scoped Topology BigOperators
open RiemannHIBS.HiddenExclusion

namespace RiemannHIBS.RadialEnergy

noncomputable section

-- 1. 临界带零点 (非平凡零点): ζ(s) = 0 ∧ 0 < Re(s) < 1
def criticalBandZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (0 : ℝ) < s.re ∧ s.re < 1

-- 2. 加权径向能量 (有限零点多重集, 隐数坐标):
--    E = Σ_{s∈Z} K(θ_s)·u_s²,  u_s = Re(s) − 1/2,  θ_s = Im(s)
def weightedRadialEnergy (Z : Finset ℂ) (K : ℝ → ℝ) : ℝ :=
  ∑ s ∈ Z, K s.im * (radialDisplacement s) ^ 2

-- 3. 正定核 ⟹ 能量恒为零 ⟹ 每个零点径向偏移为零 (真定理)
--    这是"排除"的核心逻辑: 加权和每项非负, 总和为零 ⟹ 每项为零,
--    核严格正 ⟹ u²=0 ⟹ u=0.
theorem on_critical_line_of_weighted_energy_eq_zero
    {Z : Finset ℂ} {K : ℝ → ℝ}
    (hK : ∀ s ∈ Z, 0 < K s.im)
    (hE : weightedRadialEnergy Z K = 0) :
    ∀ s ∈ Z, radialDisplacement s = 0 := by
  intro s hs
  have hterms : ∀ s' ∈ Z, 0 ≤ K s'.im * (radialDisplacement s') ^ 2 := by
    intro s' hs'
    exact mul_nonneg (le_of_lt (hK s' hs')) (sq_nonneg _)
  have hzeros : ∀ s' ∈ Z, K s'.im * (radialDisplacement s') ^ 2 = 0 := by
    intro s' hs'
    exact (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hE s' hs'
  have hKne : K s.im ≠ 0 := ne_of_gt (hK s hs)
  have hu2 : (radialDisplacement s) ^ 2 = 0 := by
    exact (mul_eq_zero.mp (hzeros s hs)).resolve_left hKne
  exact sq_eq_zero_iff.mp hu2

-- 4. 组合: 临界带零点 + 能量恒为零 ⟹ 零点在临界线 (真定理)
theorem zeros_on_critical_line_of_energy_zero
    {Z : Finset ℂ} {K : ℝ → ℝ}
    (_hZ : ∀ s ∈ Z, criticalBandZero s)
    (hK : ∀ s ∈ Z, 0 < K s.im)
    (hE : weightedRadialEnergy Z K = 0) :
    ∀ s ∈ Z, s.re = (1 / 2 : ℝ) := by
  intro s hs
  exact (radialDisplacement_eq_zero_iff s).mp
    (on_critical_line_of_weighted_energy_eq_zero hK hE s hs)

-- 5. 测试核: 三角核 K_T(θ) = max(0, 1 − |θ|/T), T > 0.
--    非负 (max 定义) 且在 |θ| < T 时严格正 — 正定核的显式实例.
def tentKernel (T : ℝ) (θ : ℝ) : ℝ := max 0 (1 - |θ| / T)

theorem tentKernel_nonneg (T θ : ℝ) : 0 ≤ tentKernel T θ := by
  exact le_max_left _ _

theorem tentKernel_pos_of_lt (T θ : ℝ) (hT : 0 < T) (hθ : |θ| < T) :
    0 < tentKernel T θ := by
  unfold tentKernel
  have hdiv : |θ| / T < 1 := (div_lt_one hT).mpr hθ
  have hpos : 0 < 1 - |θ| / T := sub_pos.mpr hdiv
  exact lt_max_of_lt_right hpos

-- 6. 径向显式公式结构 (非空接口): 零点侧能量 = 解析侧 = 素数侧.
--    修正 (leo 指示): 字段必须是真等式 (依赖 Z, K), 不再有 energy_zero 字段 —
--    把 "E_T=0" 放进假设等于把 RH 放进假设 (显式公式的解析侧是非零量,
--    由素数/Γ因子/ξ 积分决定). primeSide / analyticValue 是外部输入 (实数),
--    zero_side / analytic_side 是真正依赖 Z, K 的等式.
structure RadialExplicitFormula (Z : Finset ℂ) (K : ℝ → ℝ) (T : ℝ) where
  -- 测试核在高度窗口内严格正
  kernel_pos : ∀ θ, |θ| ≤ T → 0 < K θ
  -- 素数侧/ξ 积分侧显式公式值 (外部输入, 非零量)
  primeSide : ℝ
  -- 解析侧能量
  analyticValue : ℝ
  -- 零点侧能量 = 解析侧: Σ_{s∈Z} K(θ_s)·u_s² = analyticValue (真等式, 依赖 Z,K)
  zero_side : weightedRadialEnergy Z K = analyticValue
  -- 解析侧 = 素数侧 (显式公式恒等式)
  analytic_side : analyticValue = primeSide

-- 7. 条件定理 (真): 具体核 (tentKernel) + 有限窗口能量恒为零 ⟹ 零点在临界线.
--    这把结构体的 assemble 从"Prop 函数"提升为可真证的定理:
--      E_T = 0 ⟹ ∀ρ 临界带零点, Re(ρ) = 1/2.
--    剩余缺口 (外部输入): 从 ζ/ξ 的显式公式证明 E_T = 0.
theorem zeros_on_critical_line_of_explicit_formula
    {T : ℝ} {Z : Finset ℂ}
    (hT : 0 < T)
    (hZ : ∀ s ∈ Z, criticalBandZero s)
    (hwindow : ∀ s ∈ Z, |s.im| < T)
    (hE : weightedRadialEnergy Z (tentKernel T) = 0) :
    ∀ s ∈ Z, s.re = (1 / 2 : ℝ) := by
  apply zeros_on_critical_line_of_energy_zero (K := tentKernel T) hZ
  · intro s hs
    exact tentKernel_pos_of_lt T s.im hT (hwindow s hs)
  · exact hE

end

end RiemannHIBS.RadialEnergy
