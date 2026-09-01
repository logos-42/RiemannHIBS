-- RiemannHIBS.WeilPositivity — Weil 正性判据的条件排除定理 (2026-09-01)
--
-- leo 修正: 不追求"显式公式推出 E_T = 0" (那几乎等价于直接推出 RH, 循环假设;
-- 一般显式公式的解析侧是非零量, 由素数/Γ因子/ξ 积分决定). 改攻"正性矛盾":
--   若存在离圆零点 ⟹ ∃ 测试函数 f, zeroSide f < 0 (负贡献, 可带符号)
--   显式公式给出 zeroSide f = analyticSide f ≥ 0 (Weil 正性)
--   矛盾 ⟹ 无离圆零点.
-- 隐数坐标作用: ρ = 1/2 + u + iθ 把离圆信息明确编码为 u ≠ 0
-- (radialDisplacement), 测试函数选关于 (u,θ)↦(−u,−θ) 对称的.
--
-- 本轮: 抽象 Weil 正性证书 + 条件排除定理 (纯逻辑, 可真证).
--   诚实: explicit_identity / analytic_nonneg / off_circle_witness 均为外部输入
--   (由显式公式恒等式 + 素数侧正性 + 测试函数构造给出), 未构造 — 这是真正的
--   RH 难点, 不放进假设假装闭合.

import RiemannHIBS.RadialEnergy

open scoped Topology BigOperators
open RiemannHIBS.HiddenExclusion
open RiemannHIBS.RadialEnergy

namespace RiemannHIBS.WeilPositivity

noncomputable section

-- 1. 离圆 ⟺ 径向偏移非零 (隐数坐标编码: u = Re(s) − 1/2)
theorem off_circle_iff_radial_ne_zero (ρ : ℂ) :
    ρ.re ≠ (1 / 2 : ℝ) ↔ radialDisplacement ρ ≠ 0 := by
  unfold radialDisplacement
  constructor
  · intro h hz
    apply h
    linarith
  · intro h hρ
    apply h
    linarith

-- 2. Weil 正性证书 (抽象): 测试函数 + 两侧泛函 + 恒等式 + 正性 + 离圆负贡献
--    修正 (leo 指示): analytic_nonneg 限制在 admissible 测试函数类上,
--    不过强到任意 TestFunc.
structure WeilPositivityCertificate where
  -- 测试函数类型 (关于 (u,θ) ↦ (−u,−θ) 对称的测试函数空间)
  TestFunc : Type
  -- 允许的测试函数类 (正则性/衰减, 由显式公式的适用性决定)
  admissible : TestFunc → Prop
  -- 显式公式侧泛函 (由素数/Γ因子/ξ 积分决定的显式公式)
  analyticSide : TestFunc → ℝ
  -- 零点侧泛函 (Σ m_ρ F(ρ), F = 测试函数的变换, 可带符号)
  zeroSide : TestFunc → ℝ
  -- 显式公式恒等式: 零点侧 = 解析侧 (仅对允许的测试函数)
  explicit_identity : ∀ f : TestFunc, admissible f → zeroSide f = analyticSide f
  -- 解析侧非负 (Weil 正性, 仅对允许的测试函数)
  analytic_nonneg : ∀ f : TestFunc, admissible f → 0 ≤ analyticSide f
  -- 离圆零点 ⟹ 存在允许的测试函数使零点侧为负 (负贡献分离单个离圆零点)
  off_circle_witness :
    ∀ ρ : ℂ, criticalBandZero ρ → ρ.re ≠ (1 / 2 : ℝ) →
      ∃ f : TestFunc, admissible f ∧ zeroSide f < 0

-- 3. 条件排除定理 (真定理): Weil 正性证书 ⟹ 无离圆零点 (= 临界带内 RH)
theorem no_off_circle_zero_of_weil_certificate
    (C : WeilPositivityCertificate) :
    ∀ ρ : ℂ, criticalBandZero ρ → ρ.re = (1 / 2 : ℝ) := by
  intro ρ hρ
  by_contra hne
  obtain ⟨f, hfadm, hneg⟩ := C.off_circle_witness ρ hρ hne
  have hpos : 0 ≤ C.zeroSide f := by
    rw [C.explicit_identity f hfadm]
    exact C.analytic_nonneg f hfadm
  linarith

-- 4. 隐数径向形态: 结论等价于每个临界带零点径向偏移为零 (u = 0)
theorem zero_radial_displacement_of_weil_certificate
    (C : WeilPositivityCertificate) :
    ∀ ρ : ℂ, criticalBandZero ρ → radialDisplacement ρ = 0 := by
  intro ρ hρ
  exact (radialDisplacement_eq_zero_iff ρ).mpr
    (no_off_circle_zero_of_weil_certificate C ρ hρ)

-- 5. 具体测试函数接口 (Weil 判据的测试函数族, leo 指示):
--    value : ℝ → ℂ 是测试函数 (关于高度轴), even 编码 (u,θ)↦(−u,−θ) 反射对称.
structure WeilTestFunction where
  value : ℝ → ℂ
  even : ∀ x : ℝ, value (-x) = value x
  admissible : Prop

-- 6. 高斯测试函数实例: value x = exp(−x²), 反射对称可真证.
--    这是具体测试函数族的第一步 (高斯/有理核), 用于将来构造 off_circle_witness 的见证.
noncomputable def gaussTestFunction : WeilTestFunction where
  value x := Complex.exp (-(x : ℂ) ^ 2)
  even x := by
    congr 1
    rw [Complex.ofReal_neg]
    ring
  admissible := True

-- 7. 带重数的有限零点侧: Z_f = Σ_{ρ∈Z} m_ρ · Φ_f(ρ),  ρ = 1/2 + u + iθ
--    m_ρ = 零点重数 (外部输入: 由 ξ'/ξ 的留数定义, mathlib 无零点重数理论);
--    Φ_f(ρ) = 测试函数在零点 ρ 处的贡献 (外部输入: 围道公式的留数权重).
--    关键: K(θ)·u² 不是全纯函数 (u² = (Re ρ − 1/2)² 依赖共轭), 不能直接作为
--    ξ'/ξ 的留数权重; 必须先积分全纯测试函数, 再用反射对称转成 u 的正定式
--    — 这正是 Weil/Li 型判据比裸 RadialEnergy 更合适的原因.
def zeroSideSum (Z : Finset ℂ) (m : ℂ → ℕ)
    (Φ : WeilTestFunction → ℂ → ℝ) (f : WeilTestFunction) : ℝ :=
  ∑ ρ ∈ Z, (m ρ : ℝ) * Φ f ρ

-- 8. 有限高度零点集: Z 的元素都是高度 |Im ρ| ≤ T 的临界带零点
def heightBoundedZeros (T : ℝ) (Z : Finset ℂ) : Prop :=
  ∀ ρ ∈ Z, criticalBandZero ρ ∧ |ρ.im| ≤ T

-- 9. 离圆零点 ⟹ 带重数总零点和为负 (见证函数的完整形态, 外部输入):
--    不是单个零点的局部项为负, 而是包含全部零点贡献的总和 Z_f < 0.
--    这是 off_circle_witness 的具体化: WeilTestFunction 实例化 TestFunc,
--    admissible 实例化允许类, zeroSideSum 实例化 zeroSide.
structure WeilWitness (Z : Finset ℂ) (m : ℂ → ℕ) where
  -- 见证测试函数 (允许的)
  witness : WeilTestFunction
  witness_admissible : witness.admissible
  -- 测试函数在零点处的贡献映射 (由围道公式决定)
  Phi : WeilTestFunction → ℂ → ℝ
  -- 总零点和为负: Z_witness = Σ m_ρ·Φ_witness(ρ) < 0
  total_negative : zeroSideSum Z m Phi witness < 0

end

end RiemannHIBS.WeilPositivity
