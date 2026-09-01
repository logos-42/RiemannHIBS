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

noncomputable section

open scoped Topology BigOperators
open Metric

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
    (by simpa [hR])

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

end RiemannHIBS.ContourFormula
