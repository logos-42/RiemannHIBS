-- RiemannHIBS.HiddenExclusion
--
-- 隐数排除路线的第一轮可验证接口：
--   u = Re(s) - 1/2 是偏离临界圆的径向坐标；
--   theta = Im(s) 是万有覆盖中的未折叠高度；
--   UniformNonvanishingCertificate 把“近似 + 余项”接到真正的无零点结论。
--
-- 本文件只证明接口层的逻辑桥，不提供 RH 所需的分析性下界。

import RiemannHIBS.Analytic
import RiemannHIBS.Abundance

noncomputable section
open scoped Topology
open scoped ComplexConjugate
open scoped BigOperators

namespace RiemannHIBS.HiddenExclusion

open RiemannHIBS.Analytic
open RiemannHIBS.Abundance
open Filter

-- 隐数覆盖中的径向/角度坐标。
def radialDisplacement (s : ℂ) : ℝ := s.re - (1 / 2 : ℝ)

def hiddenRadius (s : ℂ) : ℝ := Real.exp s.re

-- 完成 ζ 函数在隐数坐标 (u, theta) 中的提升。
def hiddenXi (u theta : ℝ) : ℂ :=
  xiEntire (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))

-- 未完成 ζ 的提升及其有限旋转向量近似。
def hiddenZeta (u theta : ℝ) : ℂ :=
  riemannZeta (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))

def hiddenDirichletApproximant (N : ℕ) (u theta : ℝ) : ℂ :=
  dirichletPartialSumLine N (1 / 2 + u) theta

def hiddenDirichletSeries (u theta : ℝ) : ℂ :=
  ∑' n : ℕ, rotVecOnLine (1 / 2 + u) n theta

def hiddenDirichletRemainder (N : ℕ) (u theta : ℝ) : ℂ :=
  hiddenZeta u theta - hiddenDirichletApproximant N u theta

-- 余项定义给出精确分解；真正困难是为 remainder 建立统一下界/上界。
theorem hiddenZeta_eq_approximant_add_remainder (N : ℕ) (u theta : ℝ) :
    hiddenZeta u theta =
      hiddenDirichletApproximant N u theta + hiddenDirichletRemainder N u theta := by
  unfold hiddenDirichletRemainder
  ring

-- 在绝对收敛半平面，有限旋转向量的极限确实等于 ζ；这是逼近路线
-- 可以无条件启动的区域。临界带不能由此定理直接延伸。
theorem hiddenZeta_eq_dirichletSeries {u theta : ℝ}
    (hu : 1 < (1 / 2 : ℝ) + u) :
    hiddenZeta u theta = hiddenDirichletSeries u theta := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))
  have hs : 1 < s.re := by
    dsimp [s]
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    simpa using hu
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs
  unfold hiddenZeta hiddenDirichletSeries
  rw [hz]
  apply tsum_congr
  intro n
  dsimp [s]
  simpa [rotVecOnLine] using dirichlet_term_rotating_vector n (1 / 2 + u) theta

-- 绝对收敛区内，有限近似按高度 N 趋近隐数 ζ。
theorem hiddenDirichletApproximant_tendsto_hiddenZeta {u theta : ℝ}
    (hu : 1 < (1 / 2 : ℝ) + u) :
    Tendsto (fun N : ℕ => hiddenDirichletApproximant N u theta)
      atTop (nhds (hiddenZeta u theta)) := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))
  have hs : 1 < s.re := by
    dsimp [s]
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    simpa using hu
  have hbase : Summable (fun n : ℕ =>
      (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ s)) := by
    have h0 : Summable (fun n : ℕ =>
        (1 : ℂ) / ((n : ℂ) ^ s)) :=
      (Complex.summable_one_div_nat_cpow).2 hs
    exact (summable_nat_add_iff (G := ℂ)
      (f := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ s)) 1).mpr h0
  have hsum : Summable (fun n : ℕ => rotVecOnLine (1 / 2 + u) n theta) := by
    refine hbase.congr ?_
    intro n
    dsimp [s]
    simpa [rotVecOnLine] using
      dirichlet_term_rotating_vector n (1 / 2 + u) theta
  have hlim := hsum.hasSum.tendsto_sum_nat
  rw [hiddenZeta_eq_dirichletSeries hu]
  simpa [hiddenDirichletApproximant, dirichletPartialSumLine,
    hiddenDirichletSeries] using hlim

-- 临界叶上的单项模长精确为 n^(-1/2)。
theorem critical_lifted_term_norm (n : ℕ) (theta : ℝ) :
    ‖rotVecOnLine (1 / 2 : ℝ) n theta‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold rotVecOnLine
  rw [Complex.norm_mul]
  have h1 : ‖(((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
  have h2 : ‖Complex.exp (-(Complex.I * (theta : ℂ)) *
      (Real.log ((n + 1 : ℝ)) : ℂ))‖ = 1 := by
    have harg : -(Complex.I * (theta : ℂ)) *
        (Real.log ((n + 1 : ℝ)) : ℂ) =
        ((Real.log ((n + 1 : ℝ)) * (-theta) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [h1, h2, mul_one]

-- 因而临界叶上的普通绝对尾项不可能趋于零：这是绝对逼近路线
-- 不能直接跨过临界叶的结构性失败。
theorem critical_lifted_terms_not_summable (theta : ℝ) :
    ¬ Summable (fun n : ℕ => ‖rotVecOnLine (1 / 2 : ℝ) n theta‖) := by
  intro h
  have h' : Summable (fun n : ℕ =>
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) := by
    refine h.congr ?_
    intro n
    exact critical_lifted_term_norm n theta
  exact critical_leaf_not_absolutely_convergent h'

-- η 的交错部分和可以在 Re(s)>0 条件收敛；这是跨过绝对收敛边界的
-- 第二种近似对象，但它仍未给出 ζ 的统一非零下界。
def hiddenEtaPartialSum (N : ℕ) (u theta : ℝ) : ℂ :=
  etaPartialSum
    (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ)) N

theorem hiddenEtaPartialSum_tends_some {u theta : ℝ}
    (hu : 0 < (1 / 2 : ℝ) + u) :
    ∃ a : ℂ,
      Tendsto (fun N : ℕ => hiddenEtaPartialSum N u theta)
        atTop (nhds a) := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))
  have hs : 0 < s.re := by
    dsimp [s]
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    simpa using hu
  obtain ⟨a, ha⟩ := eta_partial_sums_converge s hs
  refine ⟨a, ?_⟩
  simpa [hiddenEtaPartialSum, s, etaPartialSum] using ha

-- 在绝对收敛区，η 部分和的极限可以精确识别为
-- (1−2^(1−s))ζ(s)；这一步不能自动延伸到临界带。
theorem hiddenEtaPartialSum_tends_mul_zeta {u theta : ℝ}
    (hu : (1 / 2 : ℝ) < u) :
    Tendsto (fun N : ℕ => hiddenEtaPartialSum N u theta) atTop
      (nhds ((1 - (2 : ℂ) ^ (1 -
        (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ)))) *
          hiddenZeta u theta)) := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))
  have hs : 1 < s.re := by
    dsimp [s]
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  have hsum := eta_summable_of_one_lt_re hs
  have hlim := hsum.hasSum.tendsto_sum_nat
  have hη : etaSeries s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s :=
    eta_eq_mul_zeta hs
  have hsumEq :
      (∑' n : ℕ, (-1 : ℂ) ^ n * ((n + 1 : ℕ) : ℂ) ^ (-s)) =
        etaSeries s := by
    unfold etaSeries
    apply tsum_congr
    intro n
    rw [Complex.cpow_neg]
    rfl
  change Tendsto (fun N : ℕ => hiddenEtaPartialSum N u theta) atTop
    (nhds ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s))
  rw [← hη]
  rw [← hsumEq]
  simpa [hiddenEtaPartialSum, hiddenZeta, s, etaPartialSum, etaSeries,
    div_eq_mul_inv, Complex.cpow_neg] using hlim

-- 远右半平面的基准下界：u ≥ 3/2 等价于 Re(s) ≥ 2。
theorem hiddenZeta_norm_lower_of_u_ge_three_halves {u theta : ℝ}
    (hu : (3 / 2 : ℝ) ≤ u) :
    ‖hiddenZeta u theta‖ ≥ (1 : ℝ) / 4 := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))
  have hs : 1 < s.re := by
    dsimp [s]
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  have hs2 : 2 ≤ s.re := by
    dsimp [s]
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  simpa [hiddenZeta, s] using
    (zeta_norm_lower_of_two_le_re s hs hs2)

theorem hiddenZeta_ne_zero_of_u_ge_three_halves {u theta : ℝ}
    (hu : (3 / 2 : ℝ) ≤ u) : hiddenZeta u theta ≠ 0 := by
  exact norm_ne_zero_iff.mp (ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
      (hiddenZeta_norm_lower_of_u_ge_three_halves hu)))

-- 远右半平面中，去掉首项后的 ζ 尾项有统一的 3/4 上界。
set_option maxHeartbeats 1000000 in
theorem zeta_sub_one_norm_le_three_fourths_of_re_ge_two
    {s : ℂ} (hs2 : (2 : ℝ) ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ (3 : ℝ) / 4 := by
  have hs : 1 < s.re := by linarith
  have hsum : Summable (fun n : ℕ =>
      (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ s)) := by
    have h0 : Summable (fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ s)) :=
      (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
    convert h0.comp_injective (i := Nat.succ)
      (fun ⦃a b⦄ h => Nat.succ.inj h) using 1
  have hsplit :
      (1 : ℂ) + ∑' n : ℕ, (1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s) =
        ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ s) := by
    convert hsum.sum_add_tsum_nat_add 1 using 1 <;>
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc]
  have hsplit' :
      (1 : ℂ) + ∑' n : ℕ, (1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s) =
        ∑' n : ℕ, (1 : ℂ) / (((n : ℂ) + 1) ^ s) := by
    simpa [Nat.cast_add, Nat.cast_one] using hsplit
  have htail :
      riemannZeta s - 1 =
        ∑' n : ℕ, (1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    rw [← hsplit']
    ring
  rw [htail]
  have hnormSummable : Summable (fun n : ℕ =>
      ‖(1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s)‖) := by
    have hshift : Summable (fun n : ℕ =>
        (1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s)) := by
      exact (summable_nat_add_iff (G := ℂ)
        (f := fun n : ℕ => (1 : ℂ) / (((n : ℕ) : ℂ) ^ s)) 2).mpr
        ((Complex.summable_one_div_nat_cpow (p := s)).mpr hs)
    exact hshift.norm
  have hnorm : ‖∑' n : ℕ,
      (1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s)‖ ≤
      ∑' n : ℕ, ‖(1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s)‖ :=
    norm_tsum_le_tsum_norm hnormSummable
  have hnorm_eq : ∀ n : ℕ,
      ‖(1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s)‖ =
        (n + 2 : ℝ) ^ (-s.re) := by
    intro n
    convert term_norm_eq s (n + 1) using 1
    all_goals norm_num [Nat.cast_add, Nat.cast_one]
    all_goals ring_nf
  have htailReal : ∑' n : ℕ, (n + 2 : ℝ) ^ (-s.re) ≤ (3 : ℝ) / 4 := by
    apply Real.tsum_le_of_sum_range_le
    · intro n
      positivity
    · intro N
      calc
        ∑ n ∈ Finset.range N, (n + 2 : ℝ) ^ (-s.re) ≤
            ∑ n ∈ Finset.range N, (n + 2 : ℝ) ^ (-2 : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          exact Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast (by omega : 1 ≤ n + 2)) (by linarith)
        _ ≤ ∑ n ∈ Finset.range N,
            1 / (((n + 1 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          exact inv_sq_le n
        _ ≤ (3 : ℝ) / 4 := telescoping_sum_bound N
  calc
    ‖∑' n : ℕ, (1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s)‖ ≤
        ∑' n : ℕ, ‖(1 : ℂ) / (((n + 2 : ℕ) : ℂ) ^ s)‖ := hnorm
    _ = ∑' n : ℕ, (n + 2 : ℝ) ^ (-s.re) := by
      apply tsum_congr
      intro n
      exact hnorm_eq n
    _ ≤ (3 : ℝ) / 4 := htailReal

-- 把 A=1 的远右半平面证书提升到隐数坐标。
theorem hiddenZeta_sub_one_norm_le_three_fourths_of_u_ge_three_halves
    {u theta : ℝ} (hu : (3 / 2 : ℝ) ≤ u) :
    ‖hiddenZeta u theta - 1‖ ≤ (3 : ℝ) / 4 := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ))
  have hs2 : (2 : ℝ) ≤ s.re := by
    dsimp [s]
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  simpa [hiddenZeta, s] using
    (zeta_sub_one_norm_le_three_fourths_of_re_ge_two hs2)

-- 这是一个实际的 Rouché 型排除结果，而不只是近似接口：A=1 的模长恒为 1，
-- 余项统一小于 1，因此隐数远右半平面没有 ζ 零点。
theorem hiddenZeta_ne_zero_of_u_ge_three_halves_via_rouche
    {u theta : ℝ} (hu : (3 / 2 : ℝ) ≤ u) : hiddenZeta u theta ≠ 0 := by
  intro hz
  have h := hiddenZeta_sub_one_norm_le_three_fourths_of_u_ge_three_halves
    (u := u) (theta := theta) hu
  rw [hz] at h
  norm_num at h

-- 临界圆就是径向偏差为 0 的叶层。
theorem radialDisplacement_eq_zero_iff (s : ℂ) :
    radialDisplacement s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  unfold radialDisplacement
  constructor <;> intro h <;> linarith

-- 隐数半径的坐标恒等式：exp(1/2 + u) = sqrt(e)·exp(u)。
theorem hiddenRadius_eq_envelopeRadius_mul_exp (u : ℝ) :
    Real.exp ((1 / 2 : ℝ) + u) = envelopeRadius * Real.exp u := by
  rw [envelopeRadius, ← exp_half_eq_sqrt_exp_one]
  rw [← Real.exp_add]

-- u=0 恰好落在反演不动圆上。
theorem hiddenRadius_zero_eq_envelopeRadius :
    Real.exp ((1 / 2 : ℝ) + 0) = envelopeRadius := by
  simpa using exp_half_eq_sqrt_exp_one

-- 函数方程反射在隐数坐标中变成 (u,theta) ↦ (-u,-theta)。
theorem hiddenXi_reflect (u theta : ℝ) :
    hiddenXi (-u) (-theta) = hiddenXi u theta := by
  unfold hiddenXi
  have harg :
      (((1 / 2 + -u : ℝ) : ℂ) + Complex.I * ((-theta : ℝ) : ℂ)) =
        1 - (((1 / 2 + u : ℝ) : ℂ) + Complex.I * (theta : ℂ)) := by
    push_cast
    ring
  rw [harg, xiEntire_one_sub]

-- 固定径向距离与有限高度的提升窗口。
def offCircleWindow (delta T : ℝ) : Set (ℝ × ℝ) :=
  {p | delta ≤ |p.1| ∧ |p.1| < (1 / 2 : ℝ) ∧ |p.2| ≤ T}

-- 一致逼近的最小接口。F 是目标函数，A 是近似，R=F-A 是余项。
structure UniformApproximation
    (F A : ℝ × ℝ → ℂ) (delta T epsilon : ℝ) : Prop where
  error_bound : ∀ p ∈ offCircleWindow delta T, ‖F p - A p‖ ≤ epsilon

-- 排除证书：近似在整个窗口上有统一非零余量，且余项小于该余量。
structure UniformNonvanishingCertificate
    (F A : ℝ × ℝ → ℂ) (delta T epsilon : ℝ) : Prop where
  approximation : UniformApproximation F A delta T epsilon
  positive_margin : 0 ≤ epsilon
  approximant_lower_bound :
    ∀ p ∈ offCircleWindow delta T, epsilon < ‖A p‖

-- 这是第一条真正的排除桥：误差小于近似值下界，就能排除目标函数零点。
theorem nonzero_of_uniform_certificate
    {F A : ℝ × ℝ → ℂ} {delta T epsilon : ℝ}
    (h : UniformNonvanishingCertificate F A delta T epsilon) :
    ∀ p ∈ offCircleWindow delta T, F p ≠ 0 := by
  intro p hp hF
  have herr := h.approximation.error_bound p hp
  have hA : ‖A p‖ ≤ epsilon := by
    rw [hF] at herr
    simpa [norm_neg] using herr
  exact (not_le_of_gt (h.approximant_lower_bound p hp)) hA

-- 逻辑反例：有限近似逐项非零且收敛，并不推出极限非零。
-- 因而“部分和趋于某个极限”本身不能替代统一正下界。
theorem nonzero_approximants_can_converge_to_zero :
    ∃ f : ℕ → ℂ,
      (∀ n, f n ≠ 0) ∧ Tendsto f atTop (nhds 0) := by
  refine ⟨fun n => ((n + 1 : ℕ) : ℂ)⁻¹, ?_, ?_⟩
  · intro n
    apply inv_ne_zero
    intro h
    have h' := congrArg Complex.re h
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    norm_num at h'
    linarith
  · simpa using
      (Filter.tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => ((n : ℕ) : ℂ)⁻¹) 1).mpr
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ))

-- 径向能量的单点原子：非负，且只有落在临界线时才为零。
def radialEnergyAtom (s : ℂ) : ℝ := (radialDisplacement s) ^ 2

theorem radialEnergyAtom_nonneg (s : ℂ) : 0 ≤ radialEnergyAtom s := by
  exact sq_nonneg _

theorem radialEnergyAtom_eq_zero_iff (s : ℂ) :
    radialEnergyAtom s = 0 ↔ s.re = (1 / 2 : ℝ) := by
  unfold radialEnergyAtom
  rw [sq_eq_zero_iff]
  exact radialDisplacement_eq_zero_iff s

-- 有限零点样本的径向总能量。
def radialEnergy (Z : Finset ℂ) : ℝ :=
  ∑ s ∈ Z, radialEnergyAtom s

theorem radialEnergy_nonneg (Z : Finset ℂ) : 0 ≤ radialEnergy Z := by
  unfold radialEnergy
  exact Finset.sum_nonneg (fun s hs => radialEnergyAtom_nonneg s)

-- 正定路线的逻辑桥：若某个有限样本的径向能量恒为零，
-- 则样本中的每个点都在临界线上。
theorem on_critical_line_of_radialEnergy_eq_zero
    {Z : Finset ℂ} (hE : radialEnergy Z = 0) :
    ∀ s ∈ Z, s.re = (1 / 2 : ℝ) := by
  have hterms : ∀ s ∈ Z, 0 ≤ radialEnergyAtom s := by
    intro s hs
    exact radialEnergyAtom_nonneg s
  have hsumzero : (∑ s ∈ Z, radialEnergyAtom s) = 0 := by
    simpa [radialEnergy] using hE
  have hzeros : ∀ s ∈ Z, radialEnergyAtom s = 0 := by
    intro s hs
    exact (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsumzero s hs
  intro s hs
  exact (radialEnergyAtom_eq_zero_iff s).mp (hzeros s hs)

theorem radialEnergy_eq_zero_iff
    {Z : Finset ℂ} :
    radialEnergy Z = 0 ↔ ∀ s ∈ Z, s.re = (1 / 2 : ℝ) := by
  constructor
  · exact on_critical_line_of_radialEnergy_eq_zero
  · intro hall
    unfold radialEnergy
    apply Finset.sum_eq_zero
    intro s hs
    exact (radialEnergyAtom_eq_zero_iff s).mpr (hall s hs)

-- 谱路线的最小接口：自伴性应当负责产生实谱，
-- 这里仅保留“零点由实高度参数精确表示”的外部证书字段。
-- 这不是存在性定理，也不声明对应的自伴算子已经找到。
structure HiddenSelfAdjointRealization (Z : Set ℂ) : Prop where
  zero_parameter_correspondence :
    ∀ s ∈ Z, ∃ gamma : ℝ,
      s = (((1 / 2 : ℝ) : ℂ) + (gamma : ℂ) * Complex.I)

end RiemannHIBS.HiddenExclusion
