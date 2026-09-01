-- RiemannHIBS.ContourFormula — 围道公式第一步: 零点重数的 logDeriv 主项 (2026-09-01)
--
-- 路线: Weil 判据的最小具体化需要"有限高度 ξ 围道显式公式"
--   (zeroSide = analyticSide 的来源). 围道公式的核心原子是:
--   零点 ρ 处 logDeriv f = m/(z−ρ) + 解析项 (m = 零点重数),
--   再对 logDeriv f 沿绕 ρ 的小圆积分得到 2πi·m (局部辐角原理).
--
-- 本轮落码: ①logDeriv 主项 (logDeriv_mul + logDeriv_fun_pow, 真定理)
--   ②积分原子: ∮ 1/(z−c) = 2πi (包装 mathlib 的
--   circleIntegral.integral_sub_inv_of_mem_ball, 真定理).
--   侦察结论: mathlib 有柯西积分公式/局部留数积分, 但无绕数/完整辐角原理 —
--   全局围道公式 (矩形边界 = 全体零点) 需后续轮次.

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import RiemannHIBS.Analytic

noncomputable section

open scoped Topology BigOperators Interval Set
open Metric
open RiemannHIBS.Analytic

namespace RiemannHIBS.ContourFormula

-- 1. 零点重数的 logDeriv 主项 (围道公式原子, 真定理):
--    f z = (z−z0)^m·g z  (m 重零点分解, g z0 ≠ 0)
--    ⟹ 在 z ≠ z0 处: logDeriv f z = m/(z−z0) + logDeriv g z
--    这是"零点和"出现在围道公式中的机制: 每个零点 ρ 贡献 m_ρ/(z−ρ) 主项.
theorem logDeriv_of_zero_factor {f g : ℂ → ℂ} {z0 z : ℂ} {m : ℕ}
    (hfg : ∀ w, f w = (w - z0) ^ m * g w)
    (hz : z ≠ z0) (hgz : g z ≠ 0)
    (hdg : DifferentiableAt ℂ g z) :
    logDeriv f z = (m : ℂ) / (z - z0) + logDeriv g z := by
  have hpow : (z - z0) ^ m ≠ 0 := by
    by_cases hm : m = 0
    · rw [hm, pow_zero]
      norm_num
    · intro hz0
      exact hz (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz0))
  calc
    logDeriv f z = logDeriv (fun w : ℂ => (w - z0) ^ m * g w) z := by
      congr 1
      exact funext hfg
    _ = logDeriv (fun w : ℂ => (w - z0) ^ m) z + logDeriv g z := by
      exact logDeriv_mul (f := fun w : ℂ => (w - z0) ^ m) (g := g) z hpow hgz
        (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => (w - z0) ^ m) z) hdg
    _ = (m : ℂ) / (z - z0) + logDeriv g z := by
      congr 1
      have hf : DifferentiableAt ℂ (fun z : ℂ => z - z0) z := by fun_prop
      have h := logDeriv_fun_pow (f := fun z : ℂ => z - z0) (x := z) hf m
      rw [h]
      rw [logDeriv_apply]
      simp
      rw [div_eq_mul_inv]

-- 2. logDeriv 的解析性 (局部辐角原理"解析项积分消失"所需):
--    g 在 s 可微且非零 ⟹ logDeriv g = deriv g / g 在 s 可微.
--    关键: mathlib 的 DifferentiableOn.deriv (柯西积分公式推论) 给复可微 ⟹ deriv 可微.
theorem differentiableOn_logDeriv {g : ℂ → ℂ} {s : Set ℂ}
    (hdg : DifferentiableOn ℂ g s) (hs : IsOpen s) (hg : ∀ z ∈ s, g z ≠ 0) :
    DifferentiableOn ℂ (logDeriv g) s := by
  intro z hz
  have hd_deriv : DifferentiableAt ℂ (deriv g) z :=
    (hdg.deriv hs).differentiableAt (hs.mem_nhds hz)
  have hd_g : DifferentiableAt ℂ g z := hdg.differentiableAt (hs.mem_nhds hz)
  have hdiv : DifferentiableAt ℂ (fun w : ℂ => deriv g w / g w) z :=
    hd_deriv.div hd_g (hg z hz)
  simpa [logDeriv] using hdiv.differentiableWithinAt

-- 3. 局部辐角原理的积分原子 (真定理, 包装 mathlib):
--    ∮_{|z−c|=R} (z−c)⁻¹ dz = 2πi  (R > 0)
theorem circleIntegral_sub_inv_two_pi_I {c : ℂ} {R : ℝ} (hR : 0 < R) :
    circleIntegral (fun z : ℂ => (z - c)⁻¹) c R = (2 * Real.pi * Complex.I : ℂ) := by
  exact circleIntegral.integral_sub_inv_of_mem_ball (c := c) (w := c) (R := R)
    (by simp [hR])

-- 4. 解析项积分消失 (局部辐角原理关键步): g 在开盘解析非零 + 闭盘连续
--    ⟹ ∮ logDeriv g = 0 (Cauchy-Goursat 圆版).
--    连续性 (logDeriv g 在闭盘连续) 由 g 的解析性给出 — 外部输入 (零点结构的正则性).
theorem circleIntegral_logDeriv_eq_zero
    {g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r)
    (hdg : DifferentiableOn ℂ g (ball c r))
    (hgz : ∀ z ∈ ball c r, g z ≠ 0)
    (hc_logDeriv : ContinuousOn (logDeriv g) (closedBall c r)) :
    circleIntegral (logDeriv g) c r = 0 := by
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
    hc_logDeriv
    (fun z hz =>
      (differentiableOn_logDeriv hdg isOpen_ball hgz).differentiableAt
        (isOpen_ball.mem_nhds hz.1))

-- 5. circleIntegral 常数提取: ∮ (a·f) = a·∮ f
theorem circleIntegral_const_mul {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (a : ℂ) :
    circleIntegral (fun z => a * f z) c R = a * circleIntegral f c R := by
  unfold circleIntegral
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  ext θ
  ring

-- 6. circleIntegral 加法: ∮ (f + g) = ∮ f + ∮ g (可积性假设显式给出)
theorem circleIntegral_add {c : ℂ} {R : ℝ} {f g : ℂ → ℂ}
    (hf : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap c R) θ * f (circleMap c R θ))
        MeasureTheory.volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap c R) θ * g (circleMap c R θ))
        MeasureTheory.volume 0 (2 * Real.pi)) :
    circleIntegral (fun z => f z + g z) c R =
      circleIntegral f c R + circleIntegral g c R := by
  unfold circleIntegral
  simp only [smul_eq_mul, mul_add]
  exact intervalIntegral.integral_add hf hg

-- 7. 主项积分: ∮ (m·(z−c)⁻¹) = 2πi·m (m 重零点的留数贡献)
theorem circleIntegral_const_mul_inv {c : ℂ} {r : ℝ} (hr : 0 < r) (m : ℕ) :
    circleIntegral (fun z : ℂ => (m : ℂ) * (z - c)⁻¹) c r =
      (2 * Real.pi * Complex.I) * (m : ℂ) := by
  rw [circleIntegral_const_mul]
  rw [circleIntegral_sub_inv_two_pi_I hr]
  ring

-- 8. 局部辐角原理 (围道公式第一定理): 若 f = (·−c)^m·g 全空间分解, g 在圆盘解析非零,
--    g 在球面可微, 则 ∮ logDeriv f = 2πi·m — "圆内只有 c 一个 m 重零点"的积分签名.
--    可积性 (hint_f / hint_ldg) 由 logDeriv f, logDeriv g 在球面连续给出 (外部输入).
theorem circleIntegral_logDeriv_eq_two_pi_I_mul
    {f g : ℂ → ℂ} {c : ℂ} {r : ℝ} {m : ℕ}
    (hr : 0 < r)
    (hfg : ∀ w, f w = (w - c) ^ m * g w)
    (hgz : ∀ z ∈ sphere c r, g z ≠ 0)
    (hdg_sph : ∀ z ∈ sphere c r, DifferentiableAt ℂ g z)
    (hdg : DifferentiableOn ℂ g (ball c r))
    (hgz_ball : ∀ z ∈ ball c r, g z ≠ 0)
    (hc_logDeriv : ContinuousOn (logDeriv g) (closedBall c r))
    (hint_main : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap c r) θ * ((m : ℂ) * (circleMap c r θ - c)⁻¹))
        MeasureTheory.volume 0 (2 * Real.pi))
    (hint_ldg : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap c r) θ * logDeriv g (circleMap c r θ))
        MeasureTheory.volume 0 (2 * Real.pi)) :
    circleIntegral (logDeriv f) c r = (2 * Real.pi * Complex.I) * (m : ℂ) := by
  -- 1. 球面上逐点: logDeriv f = m/(z−c) + logDeriv g (logDeriv 主项)
  have hld : ∀ z ∈ sphere c r,
      logDeriv f z = (m : ℂ) / (z - c) + logDeriv g z := by
    intro z hz
    have hzne : z ≠ c := by
      have hd : ‖z - c‖ = r := by
        simpa [dist_eq_norm] using (Metric.mem_sphere.mp hz)
      intro hz0
      rw [hz0, sub_self, norm_zero] at hd
      linarith
    exact logDeriv_of_zero_factor (f := f) (g := g) (z0 := c) (z := z) (m := m)
      hfg hzne (hgz z hz) (hdg_sph z hz)
  -- 2. congr: ∮ logDeriv f = ∮ (m/(·−c) + logDeriv g) (球面上 integrand 逐点相等)
  have hcongr : circleIntegral (logDeriv f) c r =
      circleIntegral (fun z : ℂ => (m : ℂ) / (z - c) + logDeriv g z) c r := by
    unfold circleIntegral
    congr 1
    ext θ
    simp [hld (circleMap c r θ) (circleMap_mem_sphere c (le_of_lt hr) θ)]
  -- 3. 线性拆开 + 主项积分 + 解析项消失
  calc
    circleIntegral (logDeriv f) c r
        = circleIntegral (fun z : ℂ => (m : ℂ) / (z - c) + logDeriv g z) c r := hcongr
    _ = circleIntegral (fun z : ℂ => (m : ℂ) * (z - c)⁻¹) c r
          + circleIntegral (logDeriv g) c r := by
          simpa [div_eq_mul_inv] using
            (circleIntegral_add (f := fun z : ℂ => (m : ℂ) * (z - c)⁻¹)
              (g := logDeriv g) hint_main hint_ldg)
    _ = (2 * Real.pi * Complex.I) * (m : ℂ) + 0 := by
          rw [circleIntegral_const_mul_inv hr m]
          rw [circleIntegral_logDeriv_eq_zero (le_of_lt hr) hdg hgz_ball hc_logDeriv]
    _ = (2 * Real.pi * Complex.I) * (m : ℂ) := by ring

-- 9. ξ 的零点结构 (外部输入): ρ 是 xiEntire 的 m 重零点.
--    factor = 因子分解 xiEntire = (·−ρ)^m·g (圆内无其他零点 ⟹ g 在圆内非零);
--    g 整性 = 零点外解析 + ρ 处可去奇点 (RemovableSingularity 理论, 外部输入).
--    零点性 xiEntire ρ = 0 从 factor 自动推出 (m > 0 时), 见下方推论.
structure XiZeroStructure (ρ : ℂ) (m : ℕ) where
  g : ℂ → ℂ
  factor : ∀ w : ℂ, xiEntire w = (w - ρ) ^ m * g w
  g_ne_zero : g ρ ≠ 0
  g_differentiable : Differentiable ℂ g

-- 9.1 推论: m 重零点分解 ⟹ ρ 确为零点
theorem xiEntire_zero_of_XiZeroStructure {ρ : ℂ} {m : ℕ}
    (Z : XiZeroStructure ρ m) (hm : 0 < m) :
    xiEntire ρ = 0 := by
  rw [Z.factor ρ]
  rw [sub_self, zero_pow (ne_of_gt hm)]
  ring

-- 10. 局部辐角原理接 ξ (围道公式第一定理的目标形态):
--     若 ρ 是 ξ 的 m 重零点且圆内无其他零点, 则 ∮ logDeriv ξ = 2πi·m.
--     纯拼接: 把 f := xiEntire, c := ρ, g := Z.g 喂进通用局部辐角原理,
--     g 的球面可微/开盘解析从 Z.g_differentiable (整性) 自动给出.
theorem circleIntegral_logDeriv_xiEntire_eq_two_pi_I_mul
    {ρ : ℂ} {m : ℕ} (Z : XiZeroStructure ρ m) (r : ℝ)
    (hr : 0 < r)
    (hgz : ∀ z ∈ sphere ρ r, Z.g z ≠ 0)
    (hgz_ball : ∀ z ∈ ball ρ r, Z.g z ≠ 0)
    (hc_logDeriv : ContinuousOn (logDeriv Z.g) (closedBall ρ r))
    (hint_main : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap ρ r) θ * ((m : ℂ) * (circleMap ρ r θ - ρ)⁻¹))
        MeasureTheory.volume 0 (2 * Real.pi))
    (hint_ldg : IntervalIntegrable
      (fun θ : ℝ => deriv (circleMap ρ r) θ * logDeriv Z.g (circleMap ρ r θ))
        MeasureTheory.volume 0 (2 * Real.pi)) :
    circleIntegral (logDeriv xiEntire) ρ r = (2 * Real.pi * Complex.I) * (m : ℂ) := by
  exact circleIntegral_logDeriv_eq_two_pi_I_mul (f := xiEntire) (g := Z.g) (c := ρ) (r := r)
    (m := m) hr Z.factor hgz
    (fun z hz => Z.g_differentiable.differentiableAt)
    Z.g_differentiable.differentiableOn
    hgz_ball hc_logDeriv hint_main hint_ldg

-- 11. 矩形边界积分 (全局围道公式的载体): ∮_∂R f = 4 条边 intervalIntegral 之和 (带方向).
--     与 mathlib Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
--     的边界表达式逐项一致 (后者的 LHS 即此定义).
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
    (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
    Complex.I * (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

-- 12. Cauchy-Goursat 矩形版 (封装 mathlib): 复可微函数在矩形内解析 ⟹ 边界积分 = 0.
--     全局围道公式的"带孔区域积分消失"依赖这个 (对挖孔后的解析函数应用).
theorem rectBoundaryIntegral_eq_zero_of_holomorphicOn
    {f : ℂ → ℂ} {z w : ℂ}
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im),
      DifferentiableAt ℂ f x) :
    rectBoundaryIntegral f z w = 0 := by
  unfold rectBoundaryIntegral
  simpa [smul_eq_mul] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅
      Set.countable_empty Hc (fun x hx => Hd x hx.1))

-- 13. 全局围道公式 (条件定理): 矩形内零点有限 (带重数) + 网格拆分 + 各子矩形局部辐角原理
--     ⟹ ∮_∂R logDeriv ξ = 2πi·Σ_{ρ∈Z} m_ρ.
--     grid_split = 网格拆分 (外部输入: 把 R 细分成含单个零点的子矩形 box ρ, 内部边抵消;
--       真基础 = 水平/垂直拆分可加性 [已真证: rectBoundaryIntegral_horizontal_split /
--       rectBoundaryIntegral_vertical_split] + 无零点子矩形积分消失 [Cauchy-Goursat 逐块, 外部输入];
--       细分到"每矩形一个零点"的拓扑构造 + 圆↔矩形同伦 [mathlib 无绕数] 是剩余硬 gap);
--     subrect_contour = 子矩形的局部辐角原理 (外部输入: 矩形版 ∮_∂box = 2πi·m, 由局部辐角原理
--       + 圆↔矩形连接给出 — 已真证的圆版是 circleIntegral_logDeriv_xiEntire_eq_two_pi_I_mul);
--     assemble 是真定理: 纯代数和 (sum_congr + Finset.mul_sum).
structure GlobalContourFormula (z w : ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) where
  box : ℂ → ℂ × ℂ
  zeros : ∀ ρ ∈ Z, xiEntire ρ = 0
  grid_split : rectBoundaryIntegral (logDeriv xiEntire) z w =
    ∑ ρ ∈ Z, rectBoundaryIntegral (logDeriv xiEntire) (box ρ).1 (box ρ).2
  subrect_contour : ∀ ρ ∈ Z,
    rectBoundaryIntegral (logDeriv xiEntire) (box ρ).1 (box ρ).2 =
      (2 * Real.pi * Complex.I) * (m ρ : ℂ)

theorem global_contour_formula_of_certificate
    {z w : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} (C : GlobalContourFormula z w Z m) :
    rectBoundaryIntegral (logDeriv xiEntire) z w =
      (2 * Real.pi * Complex.I) * (∑ ρ ∈ Z, (m ρ : ℂ)) := by
  rw [C.grid_split]
  rw [Finset.sum_congr rfl (fun ρ hρ => C.subrect_contour ρ hρ)]
  rw [← Finset.mul_sum]

-- 14. 矩形边界积分的拓扑核心: 矩形拆分 ⟹ 边界积分相加 (公共边抵消).
--     辅助引理: 垂直边相邻区间合并 — ∫_{m..b} + ∫_{a..m} = ∫_{a..b} (a ≤ m ≤ b)
lemma rect_vertical_add {f : ℂ → ℂ} {a m b : ℝ} (x : ℂ)
    (ham : a ≤ m) (hmb : m ≤ b)
    (hint_am : IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) MeasureTheory.volume a m)
    (hint_mb : IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) MeasureTheory.volume m b) :
    (∫ y in m..b, f (x + y * Complex.I)) + (∫ y in a..m, f (x + y * Complex.I))
      = ∫ y in a..b, f (x + y * Complex.I) := by
  rw [add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals hint_am hint_mb

-- 14.1 矩形水平拆分 (z 左下, w 右上, 沿 y = m 拆成上/下两块):
--     ∮_∂R f = ∮_∂R_上 f + ∮_∂R_下 f
theorem rectBoundaryIntegral_horizontal_split
    {f : ℂ → ℂ} {z w : ℂ} (m : ℝ)
    (ham : z.im ≤ m) (hmb : m ≤ w.im)
    (hint_ram : IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) MeasureTheory.volume z.im m)
    (hint_rmb : IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) MeasureTheory.volume m w.im)
    (hint_lam : IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) MeasureTheory.volume z.im m)
    (hint_lmb : IntervalIntegrable (fun y : ℝ => f (z.re + y * Complex.I)) MeasureTheory.volume m w.im) :
    rectBoundaryIntegral f z w =
      rectBoundaryIntegral f (z + Complex.I * (m - z.im)) w +
      rectBoundaryIntegral f z (w - Complex.I * (w.im - m)) := by
  unfold rectBoundaryIntegral
  calc
    (∫ x in z.re..w.re, f (x + z.im * Complex.I)) -
        (∫ x in z.re..w.re, f (x + w.im * Complex.I)) +
        Complex.I * (∫ y in z.im..w.im, f (w.re + y * Complex.I)) -
        Complex.I * (∫ y in z.im..w.im, f (z.re + y * Complex.I))
        = (∫ x in z.re..w.re, f (x + z.im * Complex.I)) -
            (∫ x in z.re..w.re, f (x + w.im * Complex.I)) +
            Complex.I * ((∫ y in m..w.im, f (w.re + y * Complex.I)) + (∫ y in z.im..m, f (w.re + y * Complex.I))) -
            Complex.I * ((∫ y in m..w.im, f (z.re + y * Complex.I)) + (∫ y in z.im..m, f (z.re + y * Complex.I))) := by
          rw [← rect_vertical_add (f := f) (x := w.re) ham hmb hint_ram hint_rmb]
          rw [← rect_vertical_add (f := f) (x := z.re) ham hmb hint_lam hint_lmb]
    _ = (∫ x in z.re..w.re, f (x + m * Complex.I)) -
            (∫ x in z.re..w.re, f (x + w.im * Complex.I)) +
            Complex.I * (∫ y in m..w.im, f (w.re + y * Complex.I)) -
            Complex.I * (∫ y in m..w.im, f (z.re + y * Complex.I)) +
        ((∫ x in z.re..w.re, f (x + z.im * Complex.I)) -
            (∫ x in z.re..w.re, f (x + m * Complex.I)) +
            Complex.I * (∫ y in z.im..m, f (w.re + y * Complex.I)) -
            Complex.I * (∫ y in z.im..m, f (z.re + y * Complex.I))) := by
          ring
    _ = rectBoundaryIntegral f (z + Complex.I * (m - z.im)) w +
        rectBoundaryIntegral f z (w - Complex.I * (w.im - m)) := by
          unfold rectBoundaryIntegral
          simp

-- 14.2 辅助引理: 水平边相邻区间合并 — ∫_{n..b} + ∫_{a..n} = ∫_{a..b} (a ≤ n ≤ b)
lemma rect_horizontal_add {f : ℂ → ℂ} {a n b : ℝ} (y : ℝ)
    (han : a ≤ n) (hnb : n ≤ b)
    (hint_an : IntervalIntegrable (fun x : ℝ => f (x + y * Complex.I)) MeasureTheory.volume a n)
    (hint_nb : IntervalIntegrable (fun x : ℝ => f (x + y * Complex.I)) MeasureTheory.volume n b) :
    (∫ x in n..b, f (x + y * Complex.I)) + (∫ x in a..n, f (x + y * Complex.I))
      = ∫ x in a..b, f (x + y * Complex.I) := by
  rw [add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals hint_an hint_nb

-- 14.3 矩形垂直拆分 (沿竖直线 x = n 拆成右/左两块): ∮_∂R f = ∮_∂R_右 f + ∮_∂R_左 f
theorem rectBoundaryIntegral_vertical_split
    {f : ℂ → ℂ} {z w : ℂ} (n : ℝ)
    (hzn : z.re ≤ n) (hnw : n ≤ w.re)
    (hint_ban : IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) MeasureTheory.volume z.re n)
    (hint_bnb : IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) MeasureTheory.volume n w.re)
    (hint_tan : IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) MeasureTheory.volume z.re n)
    (hint_tnb : IntervalIntegrable (fun x : ℝ => f (x + w.im * Complex.I)) MeasureTheory.volume n w.re) :
    rectBoundaryIntegral f z w =
      rectBoundaryIntegral f (z + (n - z.re)) w +
      rectBoundaryIntegral f z (w - (w.re - n)) := by
  unfold rectBoundaryIntegral
  calc
    (∫ x in z.re..w.re, f (x + z.im * Complex.I)) -
        (∫ x in z.re..w.re, f (x + w.im * Complex.I)) +
        Complex.I * (∫ y in z.im..w.im, f (w.re + y * Complex.I)) -
        Complex.I * (∫ y in z.im..w.im, f (z.re + y * Complex.I))
        = (∫ x in n..w.re, f (x + z.im * Complex.I)) + (∫ x in z.re..n, f (x + z.im * Complex.I)) -
            ((∫ x in n..w.re, f (x + w.im * Complex.I)) + (∫ x in z.re..n, f (x + w.im * Complex.I))) +
            Complex.I * (∫ y in z.im..w.im, f (w.re + y * Complex.I)) -
            Complex.I * (∫ y in z.im..w.im, f (z.re + y * Complex.I)) := by
          rw [← rect_horizontal_add (f := f) (y := z.im) hzn hnw hint_ban hint_bnb]
          rw [← rect_horizontal_add (f := f) (y := w.im) hzn hnw hint_tan hint_tnb]
    _ = (∫ x in n..w.re, f (x + z.im * Complex.I)) -
            (∫ x in n..w.re, f (x + w.im * Complex.I)) +
            Complex.I * (∫ y in z.im..w.im, f (w.re + y * Complex.I)) -
            Complex.I * (∫ y in z.im..w.im, f (n + y * Complex.I)) +
        ((∫ x in z.re..n, f (x + z.im * Complex.I)) -
            (∫ x in z.re..n, f (x + w.im * Complex.I)) +
            Complex.I * (∫ y in z.im..w.im, f (n + y * Complex.I)) -
            Complex.I * (∫ y in z.im..w.im, f (z.re + y * Complex.I))) := by
          ring
    _ = rectBoundaryIntegral f (z + (n - z.re)) w +
        rectBoundaryIntegral f z (w - (w.re - n)) := by
          unfold rectBoundaryIntegral
          simp

end RiemannHIBS.ContourFormula
