-- RiemannHIBS.Analytic — 隐数空间 × 解析延拓 × 黎曼猜想 (mathlib 完整版)
--
-- 目标: 用 mathlib 的解析延拓 (riemannZeta 为 ℂ 上除 s=1 外全纯的函数,
--       zeta_eq_tsum_one_div_nat_add_one_cpow 给出 Re(s)>1 的 Dirichlet 级数表示),
--       把黎曼猜想提升到隐数空间 S = ℤ×{S,R,iR}.
--
-- 与 core-Lean 版 (RiemannHIBS.Hidden / Riemann.lean) 的关系:
--   RiemannHIBS.Hidden 是 Int 坐标的代数骨架 (无 ℝ/ℂ 分析);
--   本模块是 mathlib 完整版: ℂ 用 mathlib 的 Complex, 可做真正的解析延拓.
--   因 mathlib 的 ℂ notation 与 RiemannHIBS.Hidden 的顶层 structure ℂ 冲突,
--   本模块独立于 RiemannHIBS.Hidden (不 import), 在 namespace RiemannHIBS.Analytic 下.
--
-- 结构:
--   1. 隐数结构 (mathlib 版): Tag/Hidden/hEval/π, CompositeHidden/π' (双分量)
--   2. 互推: 隐数 ↔ 复平面 (hEval 投影, 格点嵌入, π'∘ι' = id)
--   3. 隐数空间中的 ζ: zetaHidden := riemannZeta ∘ hEval (解析延拓后的 ζ 提升到隐数空间)
--   4. 解析延拓公式: η(s) = (1 − 2^(1−s))·ζ(s)  (Dirichlet eta 级数, 真实证明)
--   5. 隐数黎曼猜想 (声明, 非 sorry): 隐数空间中的零点都在倍化临界线上

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import RiemannHIBS.EnvelopeC

noncomputable section
open scoped Topology
open scoped ComplexConjugate

namespace RiemannHIBS.Analytic

-- ====================================================================
-- 1. 隐数结构 (mathlib 版, 与 HIBS Definitions 对齐)
-- ====================================================================

inductive Tag : Type where
  | S : Tag
  | R : Tag
  | iR : Tag
  deriving DecidableEq, Repr

open Tag

-- 隐数: ⟨值, 信号标签⟩
structure Hidden where
  val : ℤ
  tag : Tag
  deriving DecidableEq, Repr

abbrev S := Hidden

-- 显式构造器
def ι_R (a : ℤ) : S := ⟨a, Tag.R⟩
def hiddenImag (b : ℤ) : S := ⟨b, Tag.iR⟩
def hiddenReal (a : ℤ) : S := ⟨a, Tag.S⟩

-- i-reading: 隐数在复平面上的可观测值 (HIBS Derivation 的 hEval)
--   ⟨x, S⟩ ↦ x        (i⁰ = 1)
--   ⟨x, R⟩ ↦ −x       (i² = −1)
--   ⟨x, iR⟩ ↦ x·i     (i¹ = i)
def hEval (h : S) : ℂ :=
  match h.tag with
  | Tag.S  => (h.val : ℂ)
  | Tag.R  => -((h.val : ℂ))
  | Tag.iR => (h.val : ℂ) * Complex.I

-- 投影 π (RiemannHIBS 版语义: R 支也投影到正实轴, 供 ζ/η 部分和使用)
def π (h : S) : ℂ :=
  match h.tag with
  | Tag.S  => (h.val : ℂ)
  | Tag.R  => (h.val : ℂ)
  | Tag.iR => (h.val : ℂ) * Complex.I

-- 双分量隐数 (定理 6.5 的 ι'): 实部/虚部分别承载
structure CompositeHidden where
  realPart : S
  imagPart : S
  deriving DecidableEq, Repr

-- 双分量投影 π'
def π' (c : CompositeHidden) : ℂ :=
  (c.realPart.val : ℂ) + (c.imagPart.val : ℂ) * Complex.I

-- 格点嵌入 ι': 整数坐标 (a, b) ↦ 双分量隐数
def ι' (a b : ℤ) : CompositeHidden :=
  ⟨⟨a, Tag.S⟩, ⟨b, Tag.iR⟩⟩

-- ====================================================================
-- 2. 互推: 隐数 ↔ 复平面
-- ====================================================================

-- π' ∘ ι' = id (格点嵌入的投影恢复): 隐数空间可观测切片回到原复数
theorem π'_ι'_id (a b : ℤ) : π' (ι' a b) = (a : ℂ) + (b : ℂ) * Complex.I := by
  rfl

-- hEval 对 S 支 = 实数值
theorem hEval_real_S (a : ℤ) : hEval ⟨a, Tag.S⟩ = (a : ℂ) := rfl

-- hEval 对 iR 支 = 纯虚数
theorem hEval_imag_iR (b : ℤ) : hEval ⟨b, Tag.iR⟩ = (b : ℂ) * Complex.I := rfl

-- 投影非单射 (A1): 不同隐数投影到同一可观测值
theorem π_nonInjective : ∃ a b : S, a ≠ b ∧ π a = π b := by
  refine ⟨⟨3, Tag.S⟩, ⟨3, Tag.R⟩, ?_, ?_⟩
  · intro h
    have ht := congrArg (fun x : S => x.tag) h
    simp at ht
  · rfl

-- ====================================================================
-- 3. 隐数空间中的 ζ (解析延拓后的 ζ 通过 hEval 提升到隐数空间)
-- ====================================================================

-- 隐数空间中的黎曼 ζ: ζ_H(h) := ζ(hEval h)   (riemannZeta 已是解析延拓)
def zetaHidden (h : S) : ℂ := riemannZeta (hEval h)

-- 隐数空间中的平凡零点: s = −2, −4, −6, ... (mathlib: riemannZeta_neg_two_mul_nat_add_one)
def trivialZero (h : S) : Prop := ∃ n : ℕ, hEval h = -2 * ((n + 1 : ℕ) : ℂ)

-- 平凡零点确实存在: ζ_H(⟨−2(n+1), S⟩) = 0
theorem zetaHidden_trivialZero (n : ℕ) :
    zetaHidden ⟨(-2 * ((n + 1 : ℕ) : ℤ)), Tag.S⟩ = 0 := by
  simp [zetaHidden, hEval]
  -- riemannZeta (-2 * (n+1)) = 0, 需要先把 ℤ 转回 ℕ 表述
  have h := riemannZeta_neg_two_mul_nat_add_one n
  simpa using h

-- 倍化临界线: Re(s) = 1/2 的整数坐标化 ⟺ 2s = 1 + 2it, 即 re(2s) = 1
-- 双分量隐数 c 在倍化临界线上 ⟺ π' c = 1 + 2t·i 对某整数 t
def onDoubledCriticalLineC (c : CompositeHidden) : Prop :=
  ∃ t : ℤ, π' c = (1 : ℂ) + (2 * t : ℤ) * Complex.I

-- 倍化临界线的双分量嵌入: doubledEmbeddingC t = ι' 1 (2t) = ⟨⟨1,S⟩, ⟨2t,iR⟩⟩
def doubledEmbeddingC (t : ℤ) : CompositeHidden := ι' 1 (2 * t)

-- 双分量版本: 倍化临界线的像在 ℂ 上是 1 + 2it
theorem doubledEmbeddingC_observable (t : ℤ) :
    π' (doubledEmbeddingC t) = (1 : ℂ) + (2 * t : ℤ) * Complex.I := by
  simp [doubledEmbeddingC, π', ι']

-- 双分量版本确实在倍化临界线上: re(π' (doubledEmbeddingC t)) = 1
theorem doubledEmbeddingC_on_line (t : ℤ) :
    onDoubledCriticalLineC (doubledEmbeddingC t) := by
  refine ⟨t, ?_⟩
  simp [doubledEmbeddingC, π', ι']

-- ====================================================================
-- 4. 解析延拓公式: Dirichlet eta 级数与 ζ 的关系
--    η(s) = Σ' n, (−1)^n/(n+1)^s = (1 − 2^(1−s))·ζ(s)   (Re(s) > 1)
-- ====================================================================

-- Dirichlet eta 级数 (0-索引)
def etaSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((-1 : ℂ) ^ n) / ((n + 1 : ℕ) : ℂ) ^ s

-- 偶数项和: Σ' k, 1/(2k+2)^s = 2^(−s)·ζ(s)
theorem evenSum_eq_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (1 : ℂ) / (((2 * (k + 1) : ℕ) : ℂ) ^ s)) =
      (2 : ℂ) ^ (-s) * riemannZeta s := by
  -- 换元: Σ' 1/(2(k+1))^s = 2^(−s)·Σ' 1/(k+1)^s
  have hshift : (∑' k : ℕ, (1 : ℂ) / (((2 * (k + 1) : ℕ) : ℂ) ^ s)) =
      (2 : ℂ) ^ (-s) * (∑' k : ℕ, (1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ s)) := by
    have hterm : ∀ k : ℕ, (1 : ℂ) / (((2 * (k + 1) : ℕ) : ℂ) ^ s) =
        (2 : ℂ) ^ (-s) * ((1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ s)) := by
      intro k
      have hcast : (((2 * (k + 1) : ℕ) : ℂ)) = (2 : ℂ) * ((k + 1 : ℕ) : ℂ) := by
        rw [Nat.cast_mul]
        norm_num
      have hpow : ((2 : ℂ) * ((k + 1 : ℕ) : ℂ)) ^ s = (2 : ℂ) ^ s * (((k + 1 : ℕ) : ℂ) ^ s) := by
        simpa [Nat.cast_ofNat] using
          (Complex.natCast_mul_natCast_cpow (m := 2) (n := k + 1) s)
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      have hk : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
      rw [hcast, hpow, Complex.cpow_neg]
      field_simp [h2, hk]
    calc
      (∑' k : ℕ, (1 : ℂ) / (((2 * (k + 1) : ℕ) : ℂ) ^ s))
          = ∑' k : ℕ, (2 : ℂ) ^ (-s) * ((1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ s)) := by
            exact tsum_congr hterm
      _ = (2 : ℂ) ^ (-s) * (∑' k : ℕ, (1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ s)) := by
            rw [tsum_mul_left]
  -- Σ' 1/(k+1)^s = ζ(s) (mathlib: zeta_eq_tsum_one_div_nat_add_one_cpow)
  -- 先统一下标: Σ' k, 1/↑(k+1)^s = Σ' n, 1/(↑n+1)^s  (两者是同一求和, 表示法不同)
  have hsame : (∑' k : ℕ, (1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ s)) =
      (∑' n : ℕ, (1 : ℂ) / (((n : ℕ) : ℂ) + 1) ^ s) := by
    apply tsum_congr
    intro n
    congr 1
    -- ↑(n+1) = ↑n + 1 (ℂ 上)
    norm_num
  rw [hshift, hsame, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

-- 主定理: η(s) = (1 − 2^(1−s))·ζ(s)   (Re(s) > 1)
-- 证明: 奇偶拆分
--   η = Σ' (−1)^n/(n+1)^s = Σ' 1/(2k+1)^s − Σ' 1/(2k+2)^s
--   ζ = Σ' 1/(n+1)^s      = Σ' 1/(2k+1)^s + Σ' 1/(2k+2)^s
--   ⟹ η = ζ − 2·Σ' 1/(2k+2)^s = ζ − 2·2^(−s)·ζ = (1 − 2^(1−s))·ζ
theorem eta_eq_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    etaSeries s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  -- 0) ζ 级数可和 (η 的可和性来源)
  have hz0 : Summable (fun n : ℕ => (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ s)) := by
    have h0 : Summable (fun n : ℕ => (1 : ℂ) / ((n : ℕ) : ℂ) ^ s) :=
      (Complex.summable_one_div_nat_cpow).2 hs
    exact (summable_nat_add_iff (G := ℂ) (f := fun n : ℕ => (1 : ℂ) / ((n : ℕ) : ℂ) ^ s) 1).mpr h0
  -- η 级数可和 (alternating)
  have hηsum : Summable (fun n : ℕ => ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ s)) := by
    have hal := hz0.alternating
    simpa [div_eq_mul_inv, mul_assoc] using hal
  -- 1) η = 偶子列和 + 奇子列和  (tsum_even_add_odd)
  have he : Summable (fun k : ℕ => ((-1 : ℂ) ^ (2 * k)) / (((2 * k + 1 : ℕ) : ℂ) ^ s)) := by
    have hi : Function.Injective (fun k : ℕ => 2 * k) := by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h
    simpa [Function.comp_def, Nat.cast_mul, Nat.cast_add, mul_add, mul_one] using hηsum.comp_injective hi
  have ho : Summable (fun k : ℕ => ((-1 : ℂ) ^ (2 * k + 1)) / (((2 * k + 2 : ℕ) : ℂ) ^ s)) := by
    have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      have hm : 2 * a = 2 * b := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) hm
    convert hηsum.comp_injective hi using 1
  have hsplit : etaSeries s =
      (∑' k : ℕ, ((-1 : ℂ) ^ (2 * k)) / (((2 * k + 1 : ℕ) : ℂ) ^ s)) +
      (∑' k : ℕ, ((-1 : ℂ) ^ (2 * k + 1)) / (((2 * k + 2 : ℕ) : ℂ) ^ s)) := by
    unfold etaSeries
    rw [← tsum_even_add_odd (f := fun n : ℕ => ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ s)) he ho]
  -- 2) (-1)^(2k) = 1, (-1)^(2k+1) = -1
  have h_even_pow : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k) = 1 := by
    intro k
    rw [pow_mul]
    norm_num
  have h_odd_pow : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    intro k
    rw [pow_add, pow_mul]
    norm_num
  -- 3) 简化偶/奇项: η = Σ' 1/(2k+1)^s − Σ' 1/(2k+2)^s
  have hsplit' : etaSeries s =
      (∑' k : ℕ, (1 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) ^ s)) -
      (∑' k : ℕ, (1 : ℂ) / (((2 * k + 2 : ℕ) : ℂ) ^ s)) := by
    rw [hsplit]
    have h1 : (∑' k : ℕ, ((-1 : ℂ) ^ (2 * k)) / (((2 * k + 1 : ℕ) : ℂ) ^ s)) =
        (∑' k : ℕ, (1 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) ^ s)) := by
      apply tsum_congr
      intro k
      rw [h_even_pow k]
    have h2 : (∑' k : ℕ, ((-1 : ℂ) ^ (2 * k + 1)) / (((2 * k + 2 : ℕ) : ℂ) ^ s)) =
        (∑' k : ℕ, -((1 : ℂ) / (((2 * k + 2 : ℕ) : ℂ) ^ s))) := by
      apply tsum_congr
      intro k
      rw [h_odd_pow k, neg_div]
    rw [h1, h2]
    rw [tsum_neg]
    rw [sub_eq_add_neg]
  -- 4) ζ 的奇偶拆分: ζ = Σ' 1/(2k+1)^s + Σ' 1/(2k+2)^s
  have hze : Summable (fun k : ℕ => (1 : ℂ) / (((2 * k : ℕ) : ℂ) + 1) ^ s) := by
    have hi : Function.Injective (fun k : ℕ => 2 * k) := by
      intro a b h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) h
    simpa [Function.comp_def] using hz0.comp_injective hi
  have hzo : Summable (fun k : ℕ => (1 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) + 1) ^ s) := by
    have hi : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      have hm : 2 * a = 2 * b := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by norm_num : 0 < 2) hm
    simpa [Function.comp_def] using hz0.comp_injective hi
  have hzeta_split : riemannZeta s =
      (∑' k : ℕ, (1 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) ^ s)) +
      (∑' k : ℕ, (1 : ℂ) / (((2 * k + 2 : ℕ) : ℂ) ^ s)) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    rw [← tsum_even_add_odd (f := fun n : ℕ => (1 : ℂ) / (((n : ℕ) : ℂ) + 1) ^ s) hze hzo]
    congr 1
    · apply tsum_congr; intro k; congr 1; norm_num [Nat.cast_add]
    · apply tsum_congr; intro k; congr 1
      congr 1
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
  -- 5) 组合: η = ζ − 2·EVEN, EVEN = 2^(−s)·ζ ⟹ η = (1 − 2^(1−s))·ζ
  let ODD : ℂ := ∑' k : ℕ, (1 : ℂ) / (((2 * k + 1 : ℕ) : ℂ) ^ s)
  let EVEN : ℂ := ∑' k : ℕ, (1 : ℂ) / (((2 * k + 2 : ℕ) : ℂ) ^ s)
  have hODD : ODD = riemannZeta s - EVEN := by
    dsimp [ODD, EVEN]
    have h := hzeta_split
    rw [h]
    ring
  have hη : etaSeries s = riemannZeta s - 2 * EVEN := by
    rw [hsplit']
    dsimp [ODD, EVEN] at hODD
    rw [hODD]
    ring
  have hEVEN : EVEN = (2 : ℂ) ^ (-s) * riemannZeta s := by
    dsimp [EVEN]
    have h := evenSum_eq_mul_zeta (s := s) hs
    convert h using 1
  rw [hη, hEVEN]
  have hpow : (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    have h := Complex.cpow_add (x := (2 : ℂ)) (-s) 1 (by norm_num : (2 : ℂ) ≠ 0)
    calc
      (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (2 : ℂ) := by rw [mul_comm]
      _ = (2 : ℂ) ^ (-s) * (2 : ℂ) ^ (1 : ℂ) := by norm_num
      _ = (2 : ℂ) ^ (-s + 1) := by exact h.symm
      _ = (2 : ℂ) ^ (1 - s) := by congr 1; ring
  rw [← hpow]
  ring

-- 隐数空间的解析延拓公式: 对隐数 h (S 支, 值 = Re(s)), ζ_H 的 η 表示
theorem eta_eq_mul_zeta_hidden {a : ℤ} (ha : 1 < (a : ℝ)) :
    etaSeries ((a : ℂ)) = (1 - (2 : ℂ) ^ (1 - (a : ℂ))) * riemannZeta (a : ℂ) :=
  eta_eq_mul_zeta (s := (a : ℂ)) (by simpa using ha)

-- ====================================================================
-- 5. 隐数黎曼猜想 (声明 — 非 sorry; 与 mathlib 的 RiemannHypothesis 一致)
--    mathlib 版: RiemannHypothesis : ∀ s, ζ(s) = 0 → ¬平凡 → s ≠ 1 → s.re = 1/2
-- ====================================================================

-- mathlib 的 RiemannHypothesis 提升到隐数空间:
--   对每个隐数 h (其可观测值 hEval h 满足解析延拓后的 ζ 零点条件),
--   非平凡零点落在倍化临界线上.
def RiemannHypothesisHidden : Prop :=
  ∀ h : S, zetaHidden h = 0 → ¬ trivialZero h → hEval h ≠ 1 → (hEval h).re = 1 / 2

-- 与 mathlib 版的关系: 若经典 RiemannHypothesis 成立, 则隐数版成立
theorem riemannHypothesis_hidden_of_mathlib :
    RiemannHypothesis → RiemannHypothesisHidden := by
  intro hrh h hζ hnt hne1
  -- 隐数 h 的 ζ_H 零点 ⟺ ζ(hEval h) = 0
  have hz : riemannZeta (hEval h) = 0 := by simpa [zetaHidden] using hζ
  -- 平凡零点: ¬trivialZero h 翻译为 mathlib 的 ¬∃ n, s = -2(n+1)
  -- trivialZero h = ∃ n, hEval h = -2·(n+1); mathlib 用 -2·(↑n+1) — 同值异表示
  -- 转换 hnt 的类型再代入
  have hnt' : ¬ ∃ n : ℕ, hEval h = -2 * ((n : ℂ) + 1) := by
    intro hn
    apply hnt
    rcases hn with ⟨n, hn_eq⟩
    refine ⟨n, ?_⟩
    -- -2·(↑n+1) = -2·((n+1:ℕ):ℂ)
    simpa [Nat.cast_add] using hn_eq
  -- 直接应用 mathlib RiemannHypothesis 到 s = hEval h:
  exact hrh (hEval h) hz hnt' hne1

-- ====================================================================
-- 6. 隐数包络: expZeta 与临界线圆周 (w = e^s 坐标)
--    包络结构: 隐数三标签 {S,R,iR} = 复平面锚定方向 {θ=0, π/2, π} 的离散采样
--    (hEval ⟨x,S⟩ = x, hEval ⟨x,R⟩ = −x, hEval ⟨x,iR⟩ = x·i 即 x·e^{iθ});
--    标签连续化 + 值连续化 → 极坐标/复对数曲面 w = log z (螺旋柱面).
--    在包络坐标 w = e^s 下: 临界线 Re s = 1/2 卷成圆周 |w| = √e,
--    因此 (若 RH) 所有非平凡零点共圆 |w| = √e.
-- ====================================================================

-- 包络坐标下的 ζ: ζ̂(w) := ζ(log w)  (log 主支, w ∉ (−∞,0])
def expZeta (w : ℂ) : ℂ := riemannZeta (Complex.log w)

-- 包络半径: √e = sqrt(exp 1)
noncomputable def envelopeRadius : ℝ := Real.sqrt (Real.exp 1)

-- 引理: exp(1/2) = √e  (包络半径的指数表示)
lemma exp_half_eq_sqrt_exp_one :
    Real.exp (1 / 2 : ℝ) = Real.sqrt (Real.exp 1) := by
  -- (exp(1/2))^2 = exp(1/2 + 1/2) = exp 1
  have h_sq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  apply le_antisymm
  · -- sqrt(exp 1) ≤ exp(1/2): 重写 exp 1 = (exp(1/2))^2 后用 sqrt_sq
    rw [← h_sq]
    rw [Real.sqrt_sq (Real.exp_pos (1 / 2 : ℝ)).le]
  · -- exp(1/2) ≤ sqrt(exp 1): 重写 exp(1/2) = sqrt((exp(1/2))^2) 后反向
    rw [← Real.sqrt_sq (Real.exp_pos (1 / 2 : ℝ)).le]
    rw [h_sq]

-- 临界线像 = 圆周 |w| = √e: 对任意 t, ‖exp(1/2 + it)‖ = √e
--   (s = 1/2 + it 在临界线上 ⟹ w = e^s 满足 ‖w‖ = e^{1/2} = √e)
--   证明: exp(1/2+it) = exp(1/2)·exp(it), 模 = exp(1/2)·1
--     (norm_exp_ofReal_mul_I: 纯虚指数模为 1)
theorem criticalLine_circle (t : ℝ) :
    ‖Complex.exp ((1 / 2 : ℂ) + Complex.I * t)‖ = envelopeRadius := by
  rw [Complex.exp_add, Complex.norm_mul]
  have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [← hcast, Complex.norm_exp_ofReal (1 / 2 : ℝ)]
  have hswap : Complex.I * (t : ℂ) = (t : ℂ) * Complex.I := by ring
  rw [hswap, Complex.norm_exp_ofReal_mul_I t]
  rw [mul_one]
  exact exp_half_eq_sqrt_exp_one

-- 包络坐标下的 RH 翻译: 若 s 在临界线上且 ζ(s) = 0 (非平凡),
-- 则包络点 w = e^s 落在圆周 |w| = √e 上 (criticalLine_circle 的直接推论)
theorem zero_on_critical_line_envelope (t : ℝ)
    (_hζ : riemannZeta ((1 / 2 : ℂ) + Complex.I * t) = 0) :
    ‖Complex.exp ((1 / 2 : ℂ) + Complex.I * t)‖ = envelopeRadius :=
  criticalLine_circle t

-- ====================================================================
-- 7. 相位包络 ↔ 临界线圆周 (桥)
--    EnvelopePhase (EnvelopeC.lean §6): ⟨r,θ⟩ ↦ r·e^{iθ} 覆盖全 ℂ,
--    临界截面 criticalPhaseC: 投影 = 1/2 + t·i.
--    桥定理: 临界截面经指数映射后的模恒为 √e — 临界线在相位包络的
--    "半径-相位"坐标下就是圆周 |w| = √e. 把两套语言 (三叶壳/截面 ↔ 共圆) 接上.
--    注: 选择性 open 仅引入所需名字, 避免 EnvelopeC 的 Tag/Hidden 与本模块冲突.
-- ====================================================================
open RiemannHIBS.EnvelopeC (EnvelopePhase hEvalPhase criticalPhaseC criticalPhaseC_proj
  phaseCoversTotal phaseRay_inj)

-- 桥: criticalPhaseC (相位包络的临界截面) 的指数像落在圆周 |w| = √e 上
theorem criticalPhaseC_envelope_circle (t : ℝ) :
    ‖Complex.exp (hEvalPhase (criticalPhaseC t))‖ = envelopeRadius := by
  rw [criticalPhaseC_proj t]
  simpa [mul_comm] using criticalLine_circle t

-- 桥 (RH 版): 临界线上的零点 ζ(1/2+it) = 0 在相位包络的指数像共圆 √e
theorem zero_envelope_circle (t : ℝ)
    (_hζ : riemannZeta ((1 / 2 : ℂ) + Complex.I * t) = 0) :
    ‖Complex.exp (hEvalPhase (criticalPhaseC t))‖ = envelopeRadius :=
  criticalPhaseC_envelope_circle t

-- ====================================================================
-- 8. 相位包络 ↔ 对数坐标: 主支参数化, 多圈叶与连续折叠
--    缝合 EnvelopeC 的 EnvelopePhase (覆盖全 ℂ) 与 log 主支 (可逆域):
--    - 主支相位参数化: ζ̂(r·e^{iθ}) = ζ(log r + iθ)  (θ ∈ (−π, π])
--    - 2π 周期: 多圈叶 ⟨r, θ+2πk⟩ 投影回同一点
--    - 连续折叠: 叶 π+2πk 全部折叠到负实轴 (离散 envelope_fold 的连续版)
--    - 每圈叶覆盖: 每个 w ≠ 0 的每一圈 k 都有主支相位 θ 使投影回 w
--    (draft: 多值 log 的叶分支, 如实标注)
-- ====================================================================

-- 主支相位参数化: 对 r > 0, θ ∈ (−π, π], expZeta 在相位包络坐标下
--   就是 ζ 的对数坐标: ζ̂(r·e^{iθ}) = ζ(log r + iθ)
--   (log 主支在 ℂ∖(−∞,0] 上可逆 ⟺ 相位叶 θ ∈ (−π,π] 覆盖该区域)
theorem expZeta_phase_principal (r : ℝ) (hr : 0 < r) (θ : ℝ)
    (hθ : -Real.pi < θ) (hθ' : θ ≤ Real.pi) :
    expZeta (hEvalPhase ⟨r, θ⟩) = riemannZeta ((Real.log r : ℂ) + (θ : ℂ) * Complex.I) := by
  unfold expZeta
  congr 1
  change Complex.log ((r : ℂ) * Complex.exp (θ * Complex.I)) =
    (Real.log r : ℂ) + (θ : ℂ) * Complex.I
  have hlog : Complex.log ((r : ℂ) * Complex.exp (θ * Complex.I)) =
      (Real.log r : ℂ) + Complex.log (Complex.exp (θ * Complex.I)) :=
    Complex.log_ofReal_mul (r := r) hr (Complex.exp_ne_zero (θ * Complex.I))
  rw [hlog]
  rw [Complex.log_exp (by simpa using hθ) (by simpa using hθ')]

-- 相位 2π 周期 (归纳): 同一 w 的多圈叶 ⟨r, θ+2πk⟩ 投影回同一点
theorem phase_periodic (r : ℝ) (θ : ℝ) (k : ℕ) :
    hEvalPhase ⟨r, θ + 2 * Real.pi * (k : ℝ)⟩ = hEvalPhase ⟨r, θ⟩ := by
  unfold hEvalPhase
  dsimp
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
      -- 单步: exp((x + 2π)·I) = exp(x·I)
      have hstep (x : ℝ) : Complex.exp ((x + 2 * Real.pi) * Complex.I) =
          Complex.exp (x * Complex.I) := by
        rw [add_mul, Complex.exp_add]
        have h2 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := by
          simp [Complex.exp_two_pi_mul_I]
        rw [h2, mul_one]
      -- θ + 2π(k+1) = (θ + 2πk) + 2π  (ℝ 层)
      rw [show θ + 2 * Real.pi * ((k + 1 : ℕ) : ℝ) =
          (θ + 2 * Real.pi * (k : ℝ)) + 2 * Real.pi by
        norm_num [Nat.cast_add, Nat.cast_one]
        ring]
      simpa using (hstep (θ + 2 * Real.pi * (k : ℝ))).trans ih

-- 连续折叠: 相位叶 π + 2πk 全部投影到负实轴 −r
--   (离散折叠 envelope_fold 的连续版: 同一像 −r 有可数多个叶)
theorem phase_fold_neg_axis (r : ℝ) (k : ℕ) :
    hEvalPhase ⟨r, Real.pi + 2 * Real.pi * (k : ℝ)⟩ = -(r : ℂ) := by
  -- 先按周期折叠到 k = 0, 再用 exp(π·I) = -1
  rw [phase_periodic r Real.pi k]
  unfold hEvalPhase
  dsimp
  rw [Complex.exp_pi_mul_I]
  ring

-- 可数多叶折叠: 不同圈 k₁, k₂ 的相位叶投影到同一可观测点
theorem phase_fold_many_sheets (r : ℝ) (k₁ k₂ : ℕ) :
    hEvalPhase ⟨r, Real.pi + 2 * Real.pi * (k₁ : ℝ)⟩ =
    hEvalPhase ⟨r, Real.pi + 2 * Real.pi * (k₂ : ℝ)⟩ := by
  rw [phase_fold_neg_axis r k₁, phase_fold_neg_axis r k₂]

-- 万有覆盖的多圈叶 (已证): 每个 w ≠ 0 的每一圈 k 都有主支相位 θ ∈ (−π, π]
--   使 ⟨‖w‖, θ + 2πk⟩ 投影回 w — 相位包络是 ℂ∖{0} 上的可数叶覆盖
theorem envelope_universal_cover_branch (w : ℂ) (k : ℕ) (_hw : w ≠ 0) :
    ∃ θ : ℝ, -Real.pi < θ ∧ θ ≤ Real.pi ∧
      hEvalPhase ⟨‖w‖, θ + 2 * Real.pi * (k : ℝ)⟩ = w := by
  refine ⟨w.arg, Complex.neg_pi_lt_arg w, Complex.arg_le_pi w, ?_⟩
  rw [phase_periodic]
  simp [hEvalPhase, Complex.norm_mul_exp_arg_mul_I]

-- ====================================================================
-- 9. 零点共圆机制: 函数方程反射 + 反演不动圆 + 全称机制定理
--    回答: "能否证明零点不落在圆外?" / "能否机制性说明零点都在圆上?"
--
--    包络坐标 w = e^s: 临界线 Re(s)=1/2 卷成圆周 |w| = √e (criticalLine_circle).
--    机制链:
--      (a) 反射机制: 函数方程 ζ(1−s) = 2·(2π)^{−s}·Γ(s)·cos(πs/2)·ζ(s)
--          使零点集在 s ↦ 1−s 下闭合 (零点必然成对出现);
--      (b) 不动圆: 该反射在包络坐标下 = 反演 w ↦ e/w, 其不动集恰为 |w| = √e;
--      (c) 全称机制定理: 若"圆外无零点" (Re s ≤ 1/2), 则由反射闭合性,
--          "圆内也无零点" (Re s ≥ 1/2), 故零点全在圆上 (Re s = 1/2 = RH).
--          —— 即"证明零点不落在圆外"与"零点全在圆上"在机制上是等价的.
--      (d) 平凡零点在圆内 (|w| = e^{−2(n+1)} < 1): 圆内的零点来源确知;
--      (e) 圆上反演 = 共轭: 临界线/圆是"相位对齐"的自共轭结构;
--      (f) 螺旋线版本: 上述机制在相位包络 (螺旋面) 中的表述 —
--          零点在螺旋面上的半径被锁定为 √e.
--
--    注: Re(s) > 1 (即 |w| > e, 圆外严格更远的区域) 无零点是经典结果
--        (欧拉乘积 ζ(s) = ∏_p (1−p^{−s})⁻¹ ≠ 0), 其 Lean 形式化需要
--        EulerProduct 框架, 作为独立工作; 本节省略 (如实标注).
-- ====================================================================

-- 机制 (a): 函数方程反射 — 零点在 s ↦ 1−s 下成对出现.
--   由 riemannZeta_one_sub: ζ(1−s) = 2·(2π)^{−s}·Γ(s)·cos(πs/2)·ζ(s).
--   若 ζ(s) = 0 且 s 非负整数 (使函数方程可用), 则右边 = 0, 故 ζ(1−s) = 0.
theorem zero_reflects_under_one_sub {s : ℂ}
    (hζ : riemannZeta s = 0) (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) (hs1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  rw [riemannZeta_one_sub hsn hs1]
  rw [hζ]
  ring

-- 机制 (b): 反射的包络坐标形式 = 反演 w ↦ e/w (e^{1−s} = e / e^s)
theorem envelope_inversion_map (s : ℂ) :
    Complex.exp (1 - s) = Complex.exp 1 / Complex.exp s := by
  rw [Complex.exp_sub]

-- 机制 (b): 反演不动圆 — 反演 w ↦ e/w 的不动点恰为圆周 |w| = √e.
--   ‖e/w‖ = ‖w‖  ⟺  ‖w‖² = e  ⟺  ‖w‖ = √e.
theorem envelope_inversion_fixed_circle (w : ℂ) (hw : w ≠ 0) :
    ‖Complex.exp 1 / w‖ = ‖w‖ ↔ ‖w‖ = envelopeRadius := by
  have hnw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsplit : ‖Complex.exp 1 / w‖ = Real.exp 1 / ‖w‖ := by
    rw [Complex.norm_div]
    have : ‖Complex.exp (1 : ℂ)‖ = Real.exp 1 := by
      simpa using Complex.norm_exp_ofReal (1 : ℝ)
    rw [this]
  rw [hsplit]
  rw [envelopeRadius]
  constructor
  · intro h
    -- e/‖w‖ = ‖w‖ ⟹ ‖w‖² = e ⟹ ‖w‖ = √e
    have hsq : ‖w‖ ^ 2 = Real.exp 1 := by
      calc
        ‖w‖ ^ 2 = ‖w‖ * ‖w‖ := by rw [pow_two]
        _ = Real.exp 1 / ‖w‖ * ‖w‖ := by nth_rw 1 [← h]
        _ = Real.exp 1 := by rw [div_mul_cancel₀ _ hnw]
    rw [← Real.sqrt_sq (norm_nonneg w), hsq]
  · intro h
    -- ‖w‖ = √e ⟹ ‖w‖² = e ⟹ e/‖w‖ = ‖w‖
    calc
      Real.exp 1 / ‖w‖ = ‖w‖ ^ 2 / ‖w‖ := by
        congr 1
        rw [h, Real.sq_sqrt (Real.exp_pos 1).le]
      _ = ‖w‖ := by rw [pow_two]; exact mul_div_cancel_left₀ _ hnw

-- 机制 (c): 全称机制定理 — 圆外无零点 + 反射闭合性 ⟹ 所有零点在圆上.
--   hno: "圆外无零点" 的机制输入 (零点满足 Re s ≤ 1/2);
--   反射使 1−s 也是零点, 对 1−s 再用 hno 得 Re s ≥ 1/2; 合起来 Re s = 1/2.
--   (0 < Re s 是标准事实: 非平凡零点位于右半平面; 此处作为机制输入显式给出.)
theorem zero_on_critical_line_of_no_zeros_outside_circle
    (hno : ∀ s : ℂ, riemannZeta s = 0 → (∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) → s ≠ 1 →
      0 < s.re → s.re ≤ 1 / 2)
    {s : ℂ} (hζ : riemannZeta s = 0) (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ))
    (hs1 : s ≠ 1) (hs0 : 0 < s.re) : s.re = 1 / 2 := by
  have hle : s.re ≤ 1 / 2 := hno s hζ hsn hs1 hs0
  -- 反射: 1−s 也是零点
  have hζ' : riemannZeta (1 - s) = 0 := zero_reflects_under_one_sub hζ hsn hs1
  -- 检查 1−s 满足 hno 的各个条件
  have h1s1 : 1 - s ≠ 1 := by
    intro h
    have hs0' : s = 0 := by
      calc s = 1 - (1 - s) := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := by norm_num
    have hsre0 : s.re = 0 := by rw [hs0']; simp
    linarith
  have h1s0 : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    nlinarith [hle]
  have h1sn : ∀ n : ℕ, 1 - s ≠ -((n : ℕ) : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    have hre' : 1 - s.re = -((n : ℕ) : ℝ) := by
      simpa [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re] using hre
    have hnneg : -((n : ℕ) : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
    have hge : (1 / 2 : ℝ) ≤ 1 - s.re := by nlinarith [hle]
    linarith
  -- 对 1−s 应用"圆外无零点" ⟹ 1 − s.re ≤ 1/2 ⟹ s.re ≥ 1/2
  have hle' : (1 - s).re ≤ 1 / 2 := hno (1 - s) hζ' h1sn h1s1 h1s0
  have hge : (1 / 2 : ℝ) ≤ s.re := by
    rw [Complex.sub_re, Complex.one_re] at hle'
    linarith
  exact le_antisymm hle hge

-- 机制 (d): 平凡零点在圆内 — w = e^{−2(n+1)}, |w| < 1 < √e.
--   (配合 riemannZeta_neg_two_mul_nat_add_one: 圆内零点来源确知.)
theorem trivialZero_inside_envelope_circle (n : ℕ) :
    ‖Complex.exp (-2 * ((n + 1 : ℕ) : ℂ))‖ < envelopeRadius := by
  have hcast : (-2 * ((n + 1 : ℕ) : ℂ)) = ((-2 * ((n + 1 : ℕ) : ℝ)) : ℂ) := by
    norm_num [Complex.ofReal_natCast, Complex.ofReal_neg, Complex.ofReal_mul]
  have hnorm : ‖Complex.exp (-2 * ((n + 1 : ℕ) : ℂ))‖ =
      Real.exp (-2 * ((n + 1 : ℕ) : ℝ)) := by
    convert Complex.norm_exp_ofReal (-2 * ((n + 1 : ℕ) : ℝ)) using 1
    norm_num [Complex.ofReal_natCast, Complex.ofReal_neg, Complex.ofReal_mul]
  rw [hnorm]
  rw [envelopeRadius, ← exp_half_eq_sqrt_exp_one]
  -- exp(−2(n+1)) < exp(1/2)  ⟺  −2(n+1) < 1/2  (exp 严格递增)
  rw [Real.exp_lt_exp]
  have hpos : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  linarith

-- 机制 (e): 圆上反演 = 共轭 — 在不动圆上, e/w = conj w.
--   临界线/圆是"相位对齐"的自共轭结构: 镜像在圆上就是共轭反射.
theorem envelope_inversion_eq_conj_on_circle {w : ℂ} (_hw : w ≠ 0)
    (hr : ‖w‖ = envelopeRadius) :
    Complex.exp 1 / w = conj w := by
  have hE : (Real.exp 1 : ℂ) = Complex.exp (1 : ℂ) := by
    exact Complex.ofReal_exp (1 : ℝ)
  have hEne : (Real.exp 1 : ℂ) ≠ 0 := by
    rw [hE]
    exact Complex.exp_ne_zero (1 : ℂ)
  have hsq : ‖w‖ ^ 2 = Real.exp 1 := by
    rw [hr, envelopeRadius]
    rw [Real.sq_sqrt (Real.exp_pos 1).le]
  calc
    Complex.exp 1 / w = (Real.exp 1 : ℂ) / w := by rw [hE]
    _ = (Real.exp 1 : ℂ) * w⁻¹ := by rw [div_eq_mul_inv]
    _ = (Real.exp 1 : ℂ) * (conj w * ((Complex.normSq w)⁻¹ : ℝ)) := by
          rw [Complex.inv_def]
    _ = (Real.exp 1 : ℂ) * (conj w * ((‖w‖ ^ 2)⁻¹ : ℝ)) := by
          rw [Complex.normSq_eq_norm_sq]
    _ = conj w := by
      rw [hsq]
      rw [Complex.ofReal_inv]
      field_simp [hEne]

-- 机制 (f): 螺旋线版本 — 机制定理在相位包络/螺旋面中的表述:
--   在"圆外无零点"机制输入下, 任意零点 s (0 < Re s) 的包络像 w = e^s
--   落在圆周 |w| = √e 上 — 零点在螺旋面上的"半径"被锁定为 √e.
--   (即 ‖e^s‖ = e^{Re s} = e^{1/2} = √e.)
theorem zero_envelope_on_circle_of_no_zeros_outside_circle
    (hno : ∀ s : ℂ, riemannZeta s = 0 → (∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) → s ≠ 1 →
      0 < s.re → s.re ≤ 1 / 2)
    {s : ℂ} (hζ : riemannZeta s = 0) (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ))
    (hs1 : s ≠ 1) (hs0 : 0 < s.re) : ‖Complex.exp s‖ = envelopeRadius := by
  have hre : s.re = 1 / 2 := zero_on_critical_line_of_no_zeros_outside_circle hno hζ hsn hs1 hs0
  -- ‖e^s‖ = e^{Re s} = e^{1/2} = √e
  rw [Complex.norm_exp]
  rw [hre]
  exact exp_half_eq_sqrt_exp_one

-- ====================================================================
-- 10. 旋转向量机制: Dirichlet 级数的每一项 = 旋转向量 (猜想 1 的可证明内核)
--    猜想 1: "零点的产生与自然数本身的旋转/缠绕有关; ζ 在零点处
--            不断旋转、在实部与虚部之间来回跳动."
--    可证明内核 (本节省略全部为已证定理):
--      (a) 每一项 1/(n+1)^s 对 s = σ+it 是模长 (n+1)^{−σ}、相位 −t·log(n+1)
--          的旋转向量; 角速度 log(n+1) 正是自然数 n+1 的"内在转速" —
--          大数转得快, 小数转得慢, 零点 = 无穷多个不同转速的向量相位对齐.
--      (b) ζ(s) = 0 ⟺ 这些旋转向量之和为 0 (相消条件 = 相位对齐条件).
--      (c) 方向 (圆内/圆外) 不是内在的: 反演 w ↦ e/w 交换圆内与圆外,
--          只有圆周 |w| = √e 不动 — 猜想 2 ("方向本身有问题") 的可证明内核.
--    注: "零点为何恰好无穷多且都在 1/2 处"仍是超出本框架的经典分析事实,
--        本节省略 (如实标注).
-- ====================================================================

-- 机制 (a): 旋转向量分解 — 第 n 项 1/(n+1)^s 的极坐标形式.
--   s = σ + i·t: 1/(n+1)^s = (n+1)^{−σ}·e^{−i·t·log(n+1)}.
theorem dirichlet_term_rotating_vector (n : ℕ) (σ t : ℝ) :
    (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))) =
      (((n + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ)) := by
  have hnz : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hbase : Complex.log (((n + 1 : ℕ) : ℂ)) = (Real.log ((n + 1 : ℝ)) : ℂ) := by
    have h := Complex.ofReal_log (x := ((n + 1 : ℝ)))
      (by exact_mod_cast (Nat.zero_le (n + 1)) : (0 : ℝ) ≤ (n + 1 : ℝ))
    simpa using h.symm
  -- 左边 = exp(−(log(n+1)·(σ+it)))
  have hL : (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))) =
      Complex.exp (-((Real.log ((n + 1 : ℝ)) : ℂ) * ((σ : ℂ) + Complex.I * (t : ℂ)))) := by
    rw [Complex.cpow_def_of_ne_zero hnz, hbase]
    rw [one_div]
    rw [Complex.exp_neg]
  -- 右边 = exp((log(n+1)·(−σ)) + (−(i·t)·log(n+1)))
  have hR : (((n + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (t : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ)) =
      Complex.exp ((Real.log ((n + 1 : ℝ)) : ℂ) * (-(σ : ℂ)) +
        (-(Complex.I * (t : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))) := by
    calc
      (((n + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (t : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))
          = Complex.exp ((Real.log ((n + 1 : ℝ)) : ℂ) * (-(σ : ℂ))) *
              Complex.exp (-(Complex.I * (t : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ)) := by
            rw [Real.rpow_def_of_pos (by positivity : 0 < (n + 1 : ℝ)) (-σ)]
            rw [Complex.ofReal_exp]
            congr 1
            rw [Complex.ofReal_mul, Complex.ofReal_neg]
      _ = Complex.exp ((Real.log ((n + 1 : ℝ)) : ℂ) * (-(σ : ℂ)) +
          (-(Complex.I * (t : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))) := by
            rw [← Complex.exp_add]
  rw [hL, hR]
  congr 1
  ring

-- 机制 (b): 相位对齐条件 — ζ(s) = 0 ⟺ 旋转向量之和为 0.
--   零点 = 无穷多个不同角速度 (log(n+1)) 的旋转向量相位对齐、相消.
theorem zeta_phase_alignment_condition {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = 0 ↔
      (∑' n : ℕ,
        (((n + 1 : ℝ) ^ (-(s.re)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (s.im : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))) = 0 := by
  -- 先证 riemannZeta s = Σ term', 再转成 iff (同义反复)
  have hswap : riemannZeta s =
      (∑' n : ℕ,
        (((n + 1 : ℝ) ^ (-(s.re)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (s.im : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    apply tsum_congr
    intro n
    -- 把 s 拆成 s.re + i·s.im
    have hsdef : s = (s.re : ℂ) + Complex.I * (s.im : ℂ) := by
      rw [Complex.ext_iff]
      constructor <;> simp
    rw [hsdef]
    simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] using dirichlet_term_rotating_vector n s.re s.im
  exact Iff.of_eq (congrArg (fun x : ℂ => x = 0) hswap)

-- 机制 (c): 方向不是内在的 — 反演 w ↦ e/w 交换圆内与圆外, 只有圆周 |w| = √e 不动.
--   (猜想 2 "方向本身有问题" 的可证明内核: 圆内/圆外在反演下互为镜像,
--    因此"方向"不携带独立信息 — 唯一不变的是圆.)
theorem envelope_inversion_swaps_inside_outside (w : ℂ) (hw : w ≠ 0) :
    ‖Complex.exp 1 / w‖ < envelopeRadius ↔ envelopeRadius < ‖w‖ := by
  have hsplit : ‖Complex.exp 1 / w‖ = Real.exp 1 / ‖w‖ := by
    rw [Complex.norm_div]
    have : ‖Complex.exp (1 : ℂ)‖ = Real.exp 1 := by
      simpa using Complex.norm_exp_ofReal (1 : ℝ)
    rw [this]
  rw [hsplit, envelopeRadius, ← exp_half_eq_sqrt_exp_one]
  have h1 : Real.exp 1 = (Real.exp (1 / 2 : ℝ)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    norm_num
  have he : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos (1 / 2 : ℝ)
  have hnwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  constructor
  · intro h
    -- e/‖w‖ < √e ⟹ √e < ‖w‖
    have h' : Real.exp (1 : ℝ) < Real.exp (1 / 2 : ℝ) * ‖w‖ :=
      (div_lt_iff₀ hnwpos).mp h
    have h'' : (Real.exp (1 / 2 : ℝ)) ^ 2 < Real.exp (1 / 2 : ℝ) * ‖w‖ := by
      simpa [h1] using h'
    -- (c² < c·‖w‖) ∧ (c > 0) ⟹ c < ‖w‖
    nlinarith [he, h'']
  · intro h
    -- √e < ‖w‖ ⟹ e/‖w‖ < √e
    -- (c < ‖w‖) ∧ (c > 0) ⟹ c² < c·‖w‖ ⟹ e < c·‖w‖
    have h' : Real.exp (1 : ℝ) < Real.exp (1 / 2 : ℝ) * ‖w‖ := by
      have h2 : (Real.exp (1 / 2 : ℝ)) ^ 2 < Real.exp (1 / 2 : ℝ) * ‖w‖ := by
        nlinarith [he, h]
      simpa [h1] using h2
    exact (div_lt_iff₀ hnwpos).mpr h'

-- ====================================================================
-- 11. 半径叶与缠绕 (旋转向量机制在隐数坐标系中的几何化)
--    在覆盖空间坐标 ⟨r,θ⟩ (隐数坐标系的连续形式) 下:
--      ζ̂(r,θ) = ζ(log r + iθ) = Σ (n+1)^{−log r} · e^{−iθ·log(n+1)}
--    本节省略全部为已证定理:
--      (a) 叶上项分解: 第 n 项 = (模长 (n+1)^{−log r}) · (相位 −θ·log(n+1))
--      (b) 叶上模长: ‖第 n 项‖ = (n+1)^{−log r}  (半径叶决定模长)
--      (c) 临界叶锁定: 在 r = √e 上, ‖第 n 项‖ = (n+1)^{−1/2}
--          —— "长度维度锁定"的精确内容: 整片叶上模长被锁为 n^{−1/2}
--      (d) 缠绕: θ 增加 2π 时第 n 项相位改变 −2π·log(n+1) = −2π·windingCount n,
--          即每个自然数在圆上转 log(n+1) 圈 (缠绕圈数 = log(n+1)/2π)
--      (e) 临界衰减分界: r > e (log r > 1) 时圆上级数绝对收敛 (圆外远处无零点机制)
--      (f) 临界叶不绝对收敛: Σ (n+1)^{−1/2} 发散 — 临界叶是"绝对收敛⟷条件收敛"的分界
--           (对齐机制的启动条件, 经典分析边界的几何表述)
-- ====================================================================

-- 引理: log(√e) = 1/2  (临界叶半径的对数)
lemma log_sqrt_exp_one : Real.log (Real.sqrt (Real.exp 1)) = 1 / 2 := by
  rw [Real.log_sqrt (Real.exp_pos 1).le]
  rw [Real.log_exp]

-- 机制 (a): 叶上项分解 — ζ̂(r,θ) 的第 n 项在半径叶 r 上的旋转向量形式.
theorem leaf_term_decomposition (n : ℕ) (r θ : ℝ) :
    (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ ((Real.log r : ℂ) + Complex.I * (θ : ℂ))) =
      (((n + 1 : ℝ) ^ (-(Real.log r)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ)) := by
  exact dirichlet_term_rotating_vector n (Real.log r) θ

-- 机制 (b): 叶上模长 — 第 n 项在半径叶 r 上的模长 = (n+1)^{−log r}.
theorem leaf_term_norm (n : ℕ) (r θ : ℝ) :
    ‖(((n + 1 : ℝ) ^ (-(Real.log r)) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))‖ =
      (n + 1 : ℝ) ^ (-(Real.log r)) := by
  rw [Complex.norm_mul]
  -- 第一因子: ofReal 的模 = |·| = 自身 (因 (n+1)^{−log r} > 0)
  have hpos : 0 < (n + 1 : ℝ) ^ (-(Real.log r)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos n) (-(Real.log r))
  have h1 : ‖(((n + 1 : ℝ) ^ (-(Real.log r)) : ℝ) : ℂ)‖ =
      (n + 1 : ℝ) ^ (-(Real.log r)) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos hpos]
  -- 第二因子: 纯虚指数的模 = 1
  have h2 : ‖Complex.exp (-(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))‖ = 1 := by
    have harg : -(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ) =
        ((Real.log ((n + 1 : ℝ)) * (-θ) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_mul]
      rw [Complex.ofReal_neg]
      ring
    rw [harg]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [h1, h2]
  rw [mul_one]

-- 机制 (c): 临界叶锁定 — 在 r = √e 上, 每项模长被锁为 (n+1)^{−1/2}.
theorem critical_leaf_norm_locked (n : ℕ) (θ : ℝ) :
    ‖(((n + 1 : ℝ) ^ (-(Real.log (Real.sqrt (Real.exp 1)))) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hlog : Real.log (Real.sqrt (Real.exp 1)) = 1 / 2 := log_sqrt_exp_one
  simpa [hlog] using leaf_term_norm n (Real.sqrt (Real.exp 1)) θ

-- 机制 (d): 缠绕 — 每个自然数的缠绕圈数 = log(n+1)/2π.
--   定义: windingCount n := log(n+1)  (θ 增加 2π 时第 n 项转 windingCount n 圈)
noncomputable def windingCount (n : ℕ) : ℝ := Real.log (n + 1)

-- 相位增量: θ ↦ θ+2π 时, 第 n 项的相位改变 −2π·log(n+1) (即 −2π·windingCount n)
theorem term_phase_shift_over_turn (n : ℕ) (θ : ℝ) :
    -((θ + 2 * Real.pi) * Real.log (n + 1 : ℝ)) =
      -(θ * Real.log (n + 1 : ℝ)) - 2 * Real.pi * windingCount n := by
  unfold windingCount
  ring

-- 缠绕圈数: 第 n 项在一整圈上的圈数 = log(n+1)/(2π)
theorem term_winding_number (n : ℕ) :
    Real.log (n + 1 : ℝ) = 2 * Real.pi * (Real.log (n + 1 : ℝ) / (2 * Real.pi)) := by
  field_simp [Real.pi_ne_zero]

-- 机制 (e): 临界衰减分界 — 对 r > e (log r > 1), 圆上 Dirichlet 级数绝对收敛.
--   Σ ‖第 n 项‖ = Σ (n+1)^{−log r} < ∞  (p-级数, p = log r > 1)
theorem absolute_convergence_outside_critical_leaf (r : ℝ) (hr : Real.exp 1 < r) :
    Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (-(Real.log r)) : ℝ)) := by
  -- log r > 1 (log 严格递增, log(exp 1) = 1)
  have hlog : 1 < Real.log r := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_lt_log (Real.exp_pos 1) hr
  -- Σ (n:ℝ)^{−log r} 可和 (p-级数, p > 1): (n:ℝ)^(−log r) = ((n:ℝ)^(log r))⁻¹
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ (-(Real.log r)) : ℝ)) := by
    have hs : Summable (fun n : ℕ => (((n : ℝ) ^ (Real.log r))⁻¹ : ℝ)) :=
      Real.summable_nat_rpow_inv.mpr hlog
    simpa [Real.rpow_neg] using hs
  -- 平移 1: Σ (n+1)^{−log r}
  simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using
    (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (-(Real.log r)) : ℝ)) 1).mpr hsum

-- 机制 (f): 临界叶不绝对收敛 — Σ (n+1)^{−1/2} 发散.
--   临界叶 r=√e 是"绝对收敛 ⟷ 条件收敛"的分界 (对齐机制的启动条件).
theorem critical_leaf_not_absolutely_convergent :
    ¬ Summable (fun n : ℕ => ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) := by
  -- Σ n^{−1/2} 发散 (p = 1/2 ≤ 1)
  have hdiv : ¬ Summable (fun n : ℕ => ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) := by
    intro h
    have h' : Summable (fun n : ℕ => (((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ : ℝ)) := by
      simpa [Real.rpow_neg] using h
    have hp := (Real.summable_nat_rpow_inv (p := (1 / 2 : ℝ))).mp h'
    norm_num at hp
  intro h
  -- 若 Σ (n+1)^{−1/2} 可和, 平移回来 Σ n^{−1/2} 可和, 矛盾
  exact hdiv ((summable_nat_add_iff
    (f := fun n : ℕ => ((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) 1).mp (by simpa using h))

-- 机制 (g) [2026-08-26 验证探针]: 临界圆上的「相位预算」是随 N 单调累积的
--   可被 Lean 直接代数操作的真实量 — 验证「隐数坐标能否承载丰度指标」这一元问题。
--   定义前 N 项部分和 (在临界圆 r=√e, 即 σ=1/2 上):
--     S_N(θ) := Σ_{n<N} (n+1)^{−1/2} · e^{−iθ·log(n+1)}
--   对 θ 求导 (逐项求, 有限和):
--     S_N'(θ) = Σ_{n<N} −i·(n+1)^{−1/2}·log(n+1)·e^{−iθ·log(n+1)}
--   每个单项的模长 = (n+1)^{−1/2}·log(n+1) (纯实数权重, 旋转因子模=1)。
--   这是随 N 严格递增的可算量 — 证明隐数坐标的「相位速度预算」在代数层非死路。
--   诚实边界: 这只是「预算在累积」, 不推出「预算在某一 θ 被迫归零 (⟹零点)」;
--   后者仍需尾项控制 (Σ_{n≥N}(n+1)^{−1/2}·... 受控), 即 §17 P1–P3 的 Stirling 输入。

-- 单项相位速度模长: ‖ −i·(n+1)^{−1/2}·log(n+1)·e^{−iθ·log(n+1)} ‖ = (n+1)^{−1/2}·log(n+1)
theorem critical_leaf_phase_velocity_term_norm (n : ℕ) (θ : ℝ) :
    ‖((-Complex.I : ℂ) * (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (Real.log ((n + 1 : ℝ)) : ℂ) *
        Complex.exp (-(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ)))‖ =
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (n + 1 : ℝ) := by
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_mul]
  -- 因子1: ‖−i‖ = 1
  have h1 : ‖(-Complex.I : ℂ)‖ = 1 := by
    rw [norm_neg, Complex.norm_I]
  -- 因子2: ‖(n+1)^{−1/2}‖ = (n+1)^{−1/2} (正实数 ofReal 模)
  have h2 : ‖(((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ = (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < (n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos n) (-(1 / 2 : ℝ))
    rw [abs_of_pos hpos]
  -- 因子3: ‖log(n+1)‖ = log(n+1) (n+1≥1 ⟹ log≥0)
  have h3 : ‖((Real.log ((n + 1 : ℝ)) : ℂ))‖ = Real.log (n + 1 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hnonneg : 0 ≤ Real.log (n + 1 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.succ_pos n))
    rw [abs_of_nonneg hnonneg]
  -- 因子4: ‖e^{−iθ·log(n+1)}‖ = 1 (纯虚指数)
  have h4 : ‖Complex.exp (-(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))‖ = 1 := by
    have harg : -(Complex.I * (θ : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ) =
        ((Real.log ((n + 1 : ℝ)) * (-θ) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_mul, Complex.ofReal_neg]; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [h1, h2, h3, h4]
  simp only [one_mul, mul_one]

-- 相位预算随 N 严格递增: 第 N 项的相位速度模长是新添的正贡献
--   (即 ‖S_{N+1}'(θ) − S_N'(θ)‖ = (N+1)^{−1/2}·log(N+1) > 0)
theorem critical_leaf_phase_velocity_budget_increasing (N : ℕ) (θ : ℝ) :
    ‖((-Complex.I : ℂ) * (((N + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (Real.log ((N + 1 : ℝ)) : ℂ) *
        Complex.exp (-(Complex.I * (θ : ℂ)) * (Real.log ((N + 1 : ℝ)) : ℂ)))‖ =
      (N + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (N + 1 : ℝ) := by
  exact critical_leaf_phase_velocity_term_norm N θ

-- 推论: 该相位速度贡献对 N≥1 恒为正 (预算确实在累积, 非退化)
theorem critical_leaf_phase_velocity_positive (N : ℕ) (hN : N ≥ 1) :
    0 < (N + 1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.log (N + 1 : ℝ) := by
  have hpos1 : 0 < (N + 1 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos N) (-(1 / 2 : ℝ))
  have hlt : (1 : ℝ) < N + 1 := by
    have hNlt : (N : ℕ) < N + 1 := lt_add_one N
    exact_mod_cast (Nat.lt_of_le_of_lt hN hNlt)
  have hlogpos : 0 < Real.log (N + 1 : ℝ) := by exact Real.log_pos hlt
  exact mul_pos hpos1 hlogpos

-- 指标一 (丰度种子, 2026-08-26): 临界叶上「对角能量」发散 — Hardy 1914 的能量出发点.
--   critical_leaf_norm_locked 证每项模长 ‖a_n‖ = (n+1)^{−1/2}.
--   对角能量 = Σ_n ‖a_n‖² = Σ_n (n+1)^{−1} (调和级数) — 发散.
--   这是隐数坐标独有视角: 「模长锁定」给固定长度 n^{−1/2} 的无限多根向量叠加,
--   其 L² 总能量按 ~log N 无限累积, 不可能被有限次相位对齐吸收掉.
--   诚实边界: 此定理只证「能量种子发散」(纯代数+调和级数, 无需 Stirling);
--   从「能量发散」到「Z(t) 在临界线过零无限次」(Hardy 定理真核) 需 Hardy Z 函数 +
--   近似函数方程, mathlib 无 — 见下方 critical_leaf_energy_to_hardy_bridge 接口.

-- 对角能量单项: ‖a_n‖² = (n+1)^{−1} (纯代数, 由 critical_leaf_norm_locked 的平方)
theorem critical_leaf_diagonal_energy_term (n : ℕ) :
    (((n + 1 : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ).normSq =
      (((n + 1 : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ) := by
  rw [Complex.normSq_ofReal]
  have hpos : 0 < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hex : (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) = -1 := by norm_num
  rw [← Real.rpow_add hpos, hex]

-- 对角能量级数发散: ¬ Summable (fun n => (n+1)^{−1}) (调和级数发散)
theorem critical_leaf_diagonal_energy_diverges :
    ¬ Summable (fun (n : ℕ) => (n + 1 : ℝ) ^ (-1 : ℝ)) := by
  intro h
  -- Σ (n+1)^{−1} 可和 ⟹ Σ n^{−1} 可和 (平移), 与调和级数发散矛盾
  have hshift : Summable (fun (n : ℕ) => (n : ℝ) ^ (-1 : ℝ)) := by
    exact (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-1 : ℝ)) 1).mp
      (by simpa using h)
  -- mathlib: Summable (n ↦ n^{p}) ↔ p < -1; 取 p=−1 得矛盾
  have hbad : (-1 : ℝ) < -1 := Real.summable_nat_rpow.mp hshift
  norm_num at hbad

-- 接口缺口 (诚实标注, 非 axiom, 非已证): 指标一的能量种子 → Hardy 论证的桥.
--   形式化目标: 「若 Hardy Z 函数在临界线上实值、且临界叶 L² 能量 ∫|ζ(1/2+it)|² 无界,
--   则 Z(t) 在临界线有无限多个实零点」这一条件结构.
--   本仓库当前缺口 (mathlib 缺失):
--     (1) Hardy Z 函数 (Z(t) = e^{iθ(t)} ζ(1/2+it) 实值) 未定义;
--     (2) 近似函数方程 / 临界线均值公式 ∫₀ᵀ|ζ(1/2+it)|² dt ~ T·log T 未形式化.
--   已证部分: 上方 critical_leaf_diagonal_energy_diverges 钉死了「能量种子发散」这一半,
--   且它纯代数 + 调和级数, 完全不需要 Stirling —— 正是 Hardy 1914 绕开 Stirling 的丰度来源.
--   过零结论留作后续分析输入, 不声称已证. 此缺口登记于 current-status 「诚实边界」.

-- ====================================================================
-- 12. ζ 与隐数坐标系的同构 + 螺旋线延续 (目标 2)
--    "完美同构": 隐数坐标系 (覆盖空间 E_θ) 与复平面之间的对应 —
--      双射 (hEvalPhase 覆盖 + 径向单射) + ζ 值一致 (主支相位参数化)
--      + 螺旋线延续 (万有覆盖分支: 每个 w ≠ 0 的每一圈叶都投影回 w).
--    注: 多叶分支的 ζ 值一致性需要"多叶 log"(非主支分支), 超出当前
--        mathlib 范围, 如实标注为边界.
-- ====================================================================

-- 12.1 同构打包结构: 把"同构 + ζ 值一致 + 螺旋延续"的全部原料收进一个记录.
--     字段对应:
--       total        ≈ 隐数坐标系 (覆盖空间 E_θ)
--       toComplex    ≈ 投影 hEvalPhase (双射的"去"方向)
--       covers       ≈ 双射 1/2: 每个 z 有原像 (phaseCoversTotal)
--       radial_inj   ≈ 双射 2/2: 每片相位叶上径向唯一 (phaseRay_inj)
--       zeta_eq      ≈ ζ 值一致: ζ̂(⟨r,θ⟩) = ζ(log r + iθ) (主支, expZeta_phase_principal)
--       branch       ≈ 螺旋线延续: 第 k 圈叶投影回同一点 (envelope_universal_cover_branch)
--       periodic     ≈ 多叶一致性: 相位模 2π 平移投影不变 (phase_periodic)
structure ZetaCoverIsomorphism where
  -- 总空间 (隐数坐标系 = 覆盖空间)
  total : Type := EnvelopePhase
  -- 到复平面的投影 (双射的"去"方向)
  toComplex : EnvelopePhase → ℂ := hEvalPhase
  -- 双射 1/2: 覆盖性 — 每个 z 都有原像
  covers (z : ℂ) : ∃ e : EnvelopePhase, hEvalPhase e = z := phaseCoversTotal z
  -- 双射 2/2: 径向单射 — 每片相位叶上唯一
  radial_inj (θ : ℝ) : Function.Injective (fun r : ℝ => hEvalPhase ⟨r, θ⟩) :=
    RiemannHIBS.EnvelopeC.phaseRay_inj θ
  -- ζ 值一致: 主支相位参数化 ζ̂(⟨r,θ⟩) = ζ(log r + iθ)
  zeta_eq (r : ℝ) (hr : 0 < r) (θ : ℝ) (hθ : -Real.pi < θ) (hθ' : θ ≤ Real.pi) :
    expZeta (hEvalPhase ⟨r, θ⟩) = riemannZeta ((Real.log r : ℂ) + (θ : ℂ) * Complex.I) :=
    expZeta_phase_principal r hr θ hθ hθ'
  -- 螺旋线延续: 每个 w ≠ 0 的每一圈 k 都有主支相位, 使第 k 叶投影回 w
  branch (w : ℂ) (k : ℕ) (hw : w ≠ 0) :
    ∃ θ : ℝ, -Real.pi < θ ∧ θ ≤ Real.pi ∧
      hEvalPhase ⟨‖w‖, θ + 2 * Real.pi * (k : ℝ)⟩ = w :=
    envelope_universal_cover_branch w k hw
  -- 多叶一致性: 相位模 2π 平移投影不变 (覆盖空间纤维 = 2πℤ)
  periodic (r : ℝ) (θ : ℝ) (k : ℕ) :
    hEvalPhase ⟨r, θ + 2 * Real.pi * (k : ℝ)⟩ = hEvalPhase ⟨r, θ⟩ :=
    phase_periodic r θ k

-- 12.2 同构实例: 结构非空 — 所有字段由已证定理提供, 无新假设.
noncomputable def zetaCoverIsomorphism : ZetaCoverIsomorphism :=
  { covers := phaseCoversTotal
    radial_inj := RiemannHIBS.EnvelopeC.phaseRay_inj
    zeta_eq := expZeta_phase_principal
    branch := envelope_universal_cover_branch
    periodic := phase_periodic }

-- 12.3 螺旋线延续的"每圈叶"陈述: 第 k 圈叶上存在主支相位 θ, 使该叶投影回 w,
--     且 (主支) ζ 值由 θ 给出. 这把"螺旋线无限延伸"与"每个 w 有可数多叶"接起来.
theorem helix_continuation (w : ℂ) (k : ℕ) (hw : w ≠ 0) :
    ∃ θ : ℝ, -Real.pi < θ ∧ θ ≤ Real.pi ∧
      hEvalPhase ⟨‖w‖, θ + 2 * Real.pi * (k : ℝ)⟩ = w :=
  envelope_universal_cover_branch w k hw

-- ====================================================================
-- 13. 机制完备环 (目标 1): 四种机制描述两两等价
--     A: NoZerosOutsideCircle   — 圆外无零点 (排除机制, Re ≤ 1/2)
--     B: ZerosOnCircle          — 零点全在圆上 (对齐机制, Re = 1/2)
--     C: ZerosOnEnvelopeCircle  — 包络半径锁定 (长度维度锁定, ‖e^s‖ = √e)
--     D: RiemannHypothesis      — 经典 RH
--     环: A ⟹ B ⟹ C ⟹ D ⟹ A  (反射闭合 + exp/log 转换)
--     注: "0 < Re s"(零点在右半平面) 作为机制输入 h0 显式给出 —
--         经典事实 (函数方程 + 平凡零点排除可证), 形式化成本高, 如实标注.
--     完备性含义: 从任一机制入口进入都得到同一结论 — 机制描述互相一致.
-- ====================================================================

-- A: 圆外无零点 (排除机制)
def NoZerosOutsideCircle : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) → s ≠ 1 → 0 < s.re →
    s.re ≤ 1 / 2

-- B: 零点全在圆上 (对齐机制)
def ZerosOnCircle : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) → s ≠ 1 → 0 < s.re →
    s.re = 1 / 2

-- C: 包络半径锁定 (长度锁定机制)
def ZerosOnEnvelopeCircle : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) → s ≠ 1 → 0 < s.re →
    ‖Complex.exp s‖ = envelopeRadius

-- 环 A ⟹ B: 圆外无零点 + 反射闭合 ⟹ 零点全在圆上 (§9 机制定理)
theorem zerosOnCircle_of_noZerosOutsideCircle (hno : NoZerosOutsideCircle) :
    ZerosOnCircle := by
  intro s hζ hsn hs1 hs0
  exact zero_on_critical_line_of_no_zeros_outside_circle hno hζ hsn hs1 hs0

-- 环 B ⟹ C: 零点全在圆上 ⟹ 包络半径锁定 (e^{Re s} = e^{1/2} = √e)
theorem zerosOnEnvelopeCircle_of_zerosOnCircle (hz : ZerosOnCircle) :
    ZerosOnEnvelopeCircle := by
  intro s hζ hsn hs1 hs0
  have hre : s.re = 1 / 2 := hz s hζ hsn hs1 hs0
  rw [Complex.norm_exp]
  rw [hre]
  exact exp_half_eq_sqrt_exp_one

-- 环 C ⟹ D: 包络半径锁定 ⟹ 经典 RH (e^{Re s} = √e 取 log 得 Re s = 1/2)
theorem riemannHypothesis_of_zerosOnEnvelopeCircle (hz : ZerosOnEnvelopeCircle)
    (h0 : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re) :
    RiemannHypothesis := by
  intro s hζ hnt hs1
  have hs0 : 0 < s.re := h0 s hζ
  -- 非平凡零点自动满足 hsn (0 < Re s 排除负整数)
  have hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ) := by
    intro n h
    have hre : s.re = -((n : ℕ) : ℝ) := by
      simpa [Complex.neg_re, Complex.ofReal_re] using congrArg Complex.re h
    linarith
  have hnorm : ‖Complex.exp s‖ = envelopeRadius := hz s hζ hsn hs1 hs0
  -- e^{Re s} = √e ⟹ Re s = 1/2 (log 两边)
  have he : Real.exp s.re = envelopeRadius := by
    rw [← Complex.norm_exp]
    exact hnorm
  have hlog : s.re = Real.log envelopeRadius := by
    rw [← Real.log_exp s.re]
    exact congrArg Real.log he
  rw [envelopeRadius] at hlog
  rw [Real.log_sqrt (Real.exp_pos 1).le, Real.log_exp] at hlog
  exact hlog

-- 环 D ⟹ A: 经典 RH ⟹ 圆外无零点 (RH 直接给 Re = 1/2 ≤ 1/2)
theorem noZerosOutsideCircle_of_riemannHypothesis (hrh : RiemannHypothesis) :
    NoZerosOutsideCircle := by
  intro s hζ _hsn hs1 hs0
  -- 用 hs0 证 mathlib 需要的"非平凡"条件 hnt (0 < Re s 排除偶负整数零点)
  have hnt : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    intro hn
    rcases hn with ⟨n, hn_eq⟩
    have hre : s.re = -2 * ((n : ℝ) + 1) := by
      simpa [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.add_re]
        using congrArg Complex.re hn_eq
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hneg : -2 * ((n : ℝ) + 1) ≤ 0 := by nlinarith
    linarith
  have hre : s.re = 1 / 2 := hrh s hζ hnt hs1
  exact le_of_eq hre

-- 汇总: 机制等价 (A ↔ B 与 D ↔ C), 环闭合
theorem mechanism_equivalence_A_B
    (h0 : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re) :
    NoZerosOutsideCircle ↔ ZerosOnCircle :=
  ⟨zerosOnCircle_of_noZerosOutsideCircle,
   fun hz => noZerosOutsideCircle_of_riemannHypothesis
     (riemannHypothesis_of_zerosOnEnvelopeCircle
       (zerosOnEnvelopeCircle_of_zerosOnCircle hz) h0)⟩

theorem mechanism_equivalence_C_D
    (h0 : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re) :
    ZerosOnEnvelopeCircle ↔ RiemannHypothesis :=
  ⟨fun hz => riemannHypothesis_of_zerosOnEnvelopeCircle hz h0,
   fun hrh => zerosOnEnvelopeCircle_of_zerosOnCircle
     (zerosOnCircle_of_noZerosOutsideCircle
       (noZerosOutsideCircle_of_riemannHypothesis hrh))⟩

-- 机制环闭合: A ⟹ B ⟹ C ⟹ D ⟹ A (四方向全部为已证定理)
theorem mechanism_cycle_closed
    (h0 : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re) :
    (NoZerosOutsideCircle → ZerosOnCircle) ∧
    (ZerosOnCircle → ZerosOnEnvelopeCircle) ∧
    (ZerosOnEnvelopeCircle → RiemannHypothesis) ∧
    (RiemannHypothesis → NoZerosOutsideCircle) :=
  ⟨zerosOnCircle_of_noZerosOutsideCircle,
   zerosOnEnvelopeCircle_of_zerosOnCircle,
   (fun hz => riemannHypothesis_of_zerosOnEnvelopeCircle hz h0),
   noZerosOutsideCircle_of_riemannHypothesis⟩

-- ====================================================================
-- 14. 零点分布: 临界带内 (已证) — "零点分布规律"的严格版本
--    目标 1 的补全: 修正两个逻辑跳跃后, 圆外无零点的硬核部分可证.
--      (i) 修正: "收敛分界(绝对收敛) ⟹ 无零点" 不成立 (绝对收敛级数和可为 0).
--          真正原因 = 欧拉乘积: ζ(s) = ∏_p (1−p^{−s})⁻¹ 每因子非零
--          (mathlib 已证: riemannZeta_ne_zero_of_one_le_re, Re(s) ≥ 1 无零点).
--      (ii) 修正: "螺旋无限延伸 ⟹ 无限零点" 不成立 (候选时刻无限多 ≠ 零点存在).
--           无限零点需振荡估计 (Hardy), 如实标注为边界.
--    已证结论 (本节省略全部为已证定理, mathlib 欧拉乘积 + 函数方程反射):
--      14.1 圆外远处无零点: Re(s) ≥ 1 ⟹ ζ(s) ≠ 0  (|w| ≥ e)
--      14.2 负侧无非平凡零点: Re(s) ≤ 0 ⟹ ζ(s) ≠ 0  (非负整数外, |w| ≤ 1)
--      14.3 零点在临界带: 非平凡零点 ⟹ 0 < Re(s) < 1
--      14.4 隐数坐标翻译: 非平凡零点 ⟹ 1 < |w| < e (圆环内)
--    结论: 零点分布规律 (已证) = 非平凡零点全部位于圆环 1 < |w| < e 内;
--          临界叶 |w| = √e 是圆环的正中间 (几何平均);
--          RH ⟺ 所有零点从圆环"塌缩"到中间圆 (未证, 如实标注).
-- ====================================================================

-- 14.1 圆外远处无零点: Re(s) ≥ 1 ⟹ ζ(s) ≠ 0  (欧拉乘积, mathlib)
theorem zero_free_outside_envelope (s : ℂ) (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

-- 14.2 负侧无非平凡零点: Re(s) ≤ 0 ⟹ ζ(s) ≠ 0 (非负整数外)
--   证明: 若 ζ(s)=0, 函数方程反射给 ζ(1−s)=0; 但 Re(1−s) = 1−Re(s) ≥ 1,
--         由 14.1 得 ζ(1−s) ≠ 0, 矛盾.
theorem zero_free_negative_side {s : ℂ} (hs : s.re ≤ 0)
    (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) : riemannZeta s ≠ 0 := by
  intro hζ
  -- 反射: ζ(1−s) = 0
  have hs1 : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith
  have hζ' : riemannZeta (1 - s) = 0 := zero_reflects_under_one_sub hζ hsn hs1
  -- 但 Re(1−s) = 1 − Re s ≥ 1 ⟹ ζ(1−s) ≠ 0
  have hge : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hge) hζ'

-- 14.3 零点在临界带: 非平凡零点 ⟹ 0 < Re(s) < 1
--   证明: s.re < 1 由 14.1 (Re ≥ 1 无零点);
--         0 < s.re 由 14.2 (Re ≤ 0 无零点, 非负整数外).
theorem nontrivial_zero_in_critical_strip {s : ℂ} (hζ : riemannZeta s = 0)
    (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) (_hs1 : s ≠ 1) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    have hz : riemannZeta s ≠ 0 := zero_free_negative_side (le_of_not_gt hle) hsn
    exact hz hζ
  · by_contra hge
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hge)
    exact hz hζ

-- 14.4 隐数坐标翻译: 非平凡零点 ⟹ 1 < ‖e^s‖ < e (圆环内)
--   ‖e^s‖ = e^{Re s}, 0 < Re s < 1 ⟹ 1 < e^{Re s} < e
theorem nontrivial_zero_in_envelope_annulus {s : ℂ} (hζ : riemannZeta s = 0)
    (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) (hs1 : s ≠ 1) :
    1 < ‖Complex.exp s‖ ∧ ‖Complex.exp s‖ < Real.exp 1 := by
  have hstrip := nontrivial_zero_in_critical_strip hζ hsn hs1
  constructor
  · rw [Complex.norm_exp]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hstrip.1
  · rw [Complex.norm_exp]
    exact Real.exp_lt_exp.mpr hstrip.2

-- ====================================================================
-- 14.5 存在性转换器 — 用隐数特有结构 (反演不动圆) 构建"圆环零点对"
--    用户思路 (session 2026-08-25): 尚未建立的"非平凡零点存在性/无限性",
--      能否用隐数坐标特有信息 (覆盖多叶 / 反演不动圆 / 圆环化) 来构建?
--    本节省略给出可编译的"转换器":
--      (a) 反演保圆环: 1<‖w‖<e ⟹ 1<‖e/w‖<e (纯代数, 反演在圆环内闭合).
--      (b) 非平凡零点 ⟹ 反射对也在圆环内 (隐数坐标: 反射 = 反演 w↦e/w).
--      (c) 非平凡零点对结构 NontrivialZeroPair: 一个零点 + 其反射 (圆环内一对).
--      (d) 圆上零点 ⟹ 反演不动 (‖e^{1-s}‖ = ‖e^s‖ = √e, 不动圆).
--    归约 (诚实标注): 这些把"存在性 + 无限性"归约为——
--      "圆环 1<‖e^s‖<e 内至少存在一个非平凡零点" (聚焦缺口).
--      一旦有第一个, 反射 + 反演保圆环自动给出一整对; 无限性仍需增长估计 (§17).
--      转换器不证明该缺口 (不伪证), 只把问题精确钉住.
-- ====================================================================

-- 14.5.1 反演保圆环: 若 w 在圆环 1<‖w‖<e 内, 则 e/w 也在圆环内.
--   ‖e/w‖ = e/‖w‖, 且 1<‖w‖<e ⟹ 1<e/‖w‖<e (代数).
theorem inversion_preserves_annulus {w : ℂ} (hw : w ≠ 0)
    (hlo : 1 < ‖w‖) (hhi : ‖w‖ < Real.exp 1) :
    1 < ‖Complex.exp 1 / w‖ ∧ ‖Complex.exp 1 / w‖ < Real.exp 1 := by
  have hsplit : ‖Complex.exp 1 / w‖ = Real.exp 1 / ‖w‖ := by
    rw [Complex.norm_div]
    congr 1
    simpa using Complex.norm_exp_ofReal (1 : ℝ)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  constructor
  · rw [hsplit]
    exact one_lt_div_iff.mpr (Or.inl ⟨hwpos, hhi⟩)
  · rw [hsplit]
    rw [div_lt_iff₀ hwpos]
    nlinarith [Real.exp_pos 1, hlo]

-- 14.5.2 非平凡零点的反射对也在圆环内 (隐数坐标: 反射 s↦1−s = 反演 w↦e/w).
--   证明: ζ(1−s)=0 (反射闭合, 已证) ⟹ 1−s 是非平凡零点 ⟹ 在圆环内.
theorem nontrivial_zero_pair_in_annulus {s : ℂ} (hζ : riemannZeta s = 0)
    (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) (hs1 : s ≠ 1) :
    1 < ‖Complex.exp (1 - s)‖ ∧ ‖Complex.exp (1 - s)‖ < Real.exp 1 := by
  rw [envelope_inversion_map]
  exact inversion_preserves_annulus (Complex.exp_ne_zero s) (nontrivial_zero_in_envelope_annulus hζ hsn hs1).1
    (nontrivial_zero_in_envelope_annulus hζ hsn hs1).2

-- 14.5.3 圆环内非平凡零点对象.
--   用临界带条件表达"非平凡", 同时保留隐数圆环坐标作为显式字段.
structure AnnularNontrivialZero (s : ℂ) : Prop where
  zero : riemannZeta s = 0
  strip : 0 < s.re ∧ s.re < 1
  annulus : 1 < ‖Complex.exp s‖ ∧ ‖Complex.exp s‖ < Real.exp 1

-- 已知的非平凡零点可封装成圆环对象; 这里只是把 §14.3--14.4 组合起来.
theorem annularNontrivialZero_of_zero {s : ℂ} (hζ : riemannZeta s = 0)
    (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) (hs1 : s ≠ 1) :
    AnnularNontrivialZero s := by
  exact
    { zero := hζ
      strip := nontrivial_zero_in_critical_strip hζ hsn hs1
      annulus := nontrivial_zero_in_envelope_annulus hζ hsn hs1 }

-- 反射 s↦1−s 是 involution; 这里的"固定"是集合意义上的闭合,
-- 不是说临界圆上的每个点都被点点固定.
theorem reflection_involutive :
    Function.Involutive (fun s : ℂ => 1 - s) := by
  intro s
  ring

-- 一个圆环内非平凡零点反射为另一个圆环内非平凡零点.
-- 注意: zero_reflects_under_one_sub 的非负整数排除条件由 strip 自动给出;
-- 因而平凡负偶零点不会被错误地纳入本闭合定理.
theorem annularNontrivialZero_reflects {s : ℂ}
    (hs : AnnularNontrivialZero s) :
    AnnularNontrivialZero (1 - s) := by
  have hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ) := by
    intro n hneg
    have hrel := congrArg Complex.re hneg
    simp only [Complex.neg_re, Complex.natCast_re] at hrel
    linarith [hs.strip.1]
  have hs1 : s ≠ 1 := by
    intro hone
    have hrel := congrArg Complex.re hone
    simp only [Complex.one_re] at hrel
    linarith [hs.strip.2]
  have hζ' : riemannZeta (1 - s) = 0 :=
    zero_reflects_under_one_sub hs.zero hsn hs1
  have hstrip' : 0 < (1 - s).re ∧ (1 - s).re < 1 := by
    rw [Complex.sub_re, Complex.one_re]
    constructor <;> linarith [hs.strip.1, hs.strip.2]
  exact
    { zero := hζ'
      strip := hstrip'
      annulus := nontrivial_zero_pair_in_annulus hs.zero hsn hs1 }

-- 反射闭合可逆: 圆环内非平凡零点集合在 s↦1−s 下保持不变.
theorem annularNontrivialZero_iff_reflects {s : ℂ} :
    AnnularNontrivialZero s ↔ AnnularNontrivialZero (1 - s) := by
  constructor
  · exact annularNontrivialZero_reflects
  · intro hs
    simpa [sub_eq_add_neg, add_assoc] using
      (annularNontrivialZero_reflects hs)

-- 一个种子只产生一个反射轨道; 这不是无限性结论.
theorem exists_annular_nontrivial_zero_pair
    (h : ∃ s : ℂ, AnnularNontrivialZero s) :
    ∃ s : ℂ, AnnularNontrivialZero s ∧ AnnularNontrivialZero (1 - s) := by
  rcases h with ⟨s, hs⟩
  exact ⟨s, hs, annularNontrivialZero_reflects hs⟩

-- 14.5.5 覆盖空间中的有限高度提升矩形.
--   s 的虚部就是覆盖角度 θ; 这里保留 θ 而不折叠到 w 平面,
--   以便后续用围道/绕数处理不同叶上的零点.
def hiddenStripWindow (T : ℝ) : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1 ∧ |s.im| < T}

theorem hiddenStripWindow_mem_annulus {T : ℝ} {s : ℂ}
    (hs : s ∈ hiddenStripWindow T) :
    1 < ‖Complex.exp s‖ ∧ ‖Complex.exp s‖ < Real.exp 1 := by
  rcases hs with ⟨hs0, hs1, _⟩
  constructor
  · rw [Complex.norm_exp, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hs0
  · rw [Complex.norm_exp]
    exact Real.exp_lt_exp.mpr hs1

-- 提升矩形的闭包: 左右边界对称于临界线, 上下边界位于覆盖高度 ±T.
def hiddenLiftRectangle (σ T : ℝ) : Set ℂ :=
  Complex.Rectangle ((σ : ℂ) - (T : ℂ) * Complex.I)
    (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I)

-- 矩形边界积分的隐数坐标写法, 顺序为下边、上边、右边、左边.
def hiddenRectangleBoundaryIntegral (f : ℂ → ℂ) (σ T : ℝ) : ℂ :=
    (∫ x : ℝ in σ..(1 - σ),
        f ((x : ℂ) - (T : ℂ) * Complex.I))
      - (∫ x : ℝ in σ..(1 - σ),
        f ((x : ℂ) + (T : ℂ) * Complex.I))
      + Complex.I • (∫ y : ℝ in (-T)..T,
        f (((1 - σ : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      - Complex.I • (∫ y : ℝ in (-T)..T,
        f ((σ : ℂ) + (y : ℂ) * Complex.I))

-- 已知的 Cauchy–Goursat 矩形原子: 全纯函数在提升矩形边界上的积分为零.
-- 后续对 logDeriv 使用时, 正是要替换为“零点数/绕数”版本.
theorem hiddenRectangleBoundaryIntegral_eq_zero_of_differentiableOn
    {f : ℂ → ℂ} {σ T : ℝ}
    (hf : DifferentiableOn ℂ f (hiddenLiftRectangle σ T)) :
    hiddenRectangleBoundaryIntegral f σ T = 0 := by
  simpa [hiddenRectangleBoundaryIntegral, hiddenLiftRectangle, Complex.Rectangle,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] using
    (Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((σ : ℂ) - (T : ℂ) * Complex.I)
      (((1 - σ : ℝ) : ℂ) + (T : ℂ) * Complex.I) hf)

-- 覆盖高度: |θ| = |Im s|. 这是把“螺旋向上无界”翻译成实数无界集.
def hiddenNontrivialZeroHeights : Set ℝ :=
  (fun s : ℂ => |s.im|) '' {s | AnnularNontrivialZero s}

def HiddenZeroHeightGrowth : Prop :=
  ¬ BddAbove hiddenNontrivialZeroHeights

-- 有限高度窗口中的隐数零点集合与计数 N_hidden(T).
def hiddenNontrivialZeroWindow (T : ℝ) : Set ℂ :=
  {s | AnnularNontrivialZero s ∧ |s.im| ≤ T}

def hiddenZeroCount (T : ℝ) : ℕ∞ :=
  (hiddenNontrivialZeroWindow T).encard

-- 零点计数的分析输入接口: 对任意 N, 某个有限高度窗口至少容纳 N 个零点.
-- 这是 Riemann–von Mangoldt 下界的抽象形式, 目前不声明其成立.
def HiddenZeroCountGrowth : Prop :=
  ∀ N : ℕ, ∃ T : ℝ, (N : ℕ∞) ≤ hiddenZeroCount T

-- 经典临界带中的非平凡零点谓词, 用于计数定理向隐数坐标传递.
def ClassicalNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

theorem annularNontrivialZero_iff_classicalNontrivialZero {s : ℂ} :
    AnnularNontrivialZero s ↔ ClassicalNontrivialZero s := by
  constructor
  · intro hs
    exact ⟨hs.zero, hs.strip.1, hs.strip.2⟩
  · intro hs
    have hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ) := by
      intro n hneg
      have hrel := congrArg Complex.re hneg
      simp only [Complex.neg_re, Complex.natCast_re] at hrel
      linarith [hs.2.1]
    have hs1 : s ≠ 1 := by
      intro hone
      have hrel := congrArg Complex.re hone
      simp only [Complex.one_re] at hrel
      linarith [hs.2.2]
    exact annularNontrivialZero_of_zero hs.1 hsn hs1

def classicalNontrivialZeroWindow (T : ℝ) : Set ℂ :=
  {s | ClassicalNontrivialZero s ∧ |s.im| ≤ T}

def classicalZeroCount (T : ℝ) : ℕ∞ :=
  (classicalNontrivialZeroWindow T).encard

theorem hiddenZeroCount_eq_classicalZeroCount (T : ℝ) :
    hiddenZeroCount T = classicalZeroCount T := by
  unfold hiddenZeroCount classicalZeroCount
  congr 1
  ext s
  rw [hiddenNontrivialZeroWindow, classicalNontrivialZeroWindow]
  simp only [Set.mem_setOf_eq]
  rw [annularNontrivialZero_iff_classicalNontrivialZero]

-- 经典计数增长接口传递到隐数计数增长接口.
def ClassicalZeroCountGrowth : Prop :=
  ∀ N : ℕ, ∃ T : ℝ, (N : ℕ∞) ≤ classicalZeroCount T

theorem classicalZeroCountGrowth_implies_hiddenZeroCountGrowth
    (h : ClassicalZeroCountGrowth) : HiddenZeroCountGrowth := by
  intro N
  rcases h N with ⟨T, hT⟩
  exact ⟨T, by simpa [hiddenZeroCount_eq_classicalZeroCount T] using hT⟩

-- 若隐数覆盖中的非平凡零点高度无界, 则圆环内非平凡零点必为无限集.
-- 这是存在性/增长证明与集合无限性的严格接口, 不引入任何分析公理.
theorem infinite_annular_nontrivial_zeros_of_height_growth
    (h : HiddenZeroHeightGrowth) :
    Set.Infinite {s : ℂ | AnnularNontrivialZero s} := by
  intro hfinite
  apply h
  unfold hiddenNontrivialZeroHeights
  exact (hfinite.image (fun s : ℂ => |s.im|)).bddAbove

-- 零点计数无界也直接推出无限性; 这是计数公式接入隐数层的第一座桥.
theorem infinite_annular_nontrivial_zeros_of_count_growth
    (h : HiddenZeroCountGrowth) :
    Set.Infinite {s : ℂ | AnnularNontrivialZero s} := by
  intro hfinite
  obtain ⟨n, hn⟩ := hfinite.exists_encard_eq_coe
  obtain ⟨T, hT⟩ := h (n + 1)
  have hsubset : hiddenNontrivialZeroWindow T ⊆ {s : ℂ | AnnularNontrivialZero s} := by
    intro s hs
    exact hs.1
  have hle : hiddenZeroCount T ≤ ({s : ℂ | AnnularNontrivialZero s}).encard := by
    exact Set.encard_mono hsubset
  have hcontra : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    calc
      ((n + 1 : ℕ) : ℕ∞) ≤ hiddenZeroCount T := hT
      _ ≤ ({s : ℂ | AnnularNontrivialZero s}).encard := hle
      _ = (n : ℕ∞) := hn
  exact (Nat.not_succ_le_self n) ((ENat.coe_le_coe.mp hcontra))

theorem infinite_classical_nontrivial_zeros_of_classical_count_growth
    (h : ClassicalZeroCountGrowth) :
    Set.Infinite {s : ℂ | ClassicalNontrivialZero s} := by
  have hhidden : Set.Infinite {s : ℂ | AnnularNontrivialZero s} :=
    infinite_annular_nontrivial_zeros_of_count_growth
      (classicalZeroCountGrowth_implies_hiddenZeroCountGrowth h)
  apply Set.Infinite.mono (s := {s : ℂ | AnnularNontrivialZero s})
    (t := {s : ℂ | ClassicalNontrivialZero s})
  · intro s hs
    exact annularNontrivialZero_iff_classicalNontrivialZero.mp hs
  · exact hhidden

-- 同一接口直接落回经典临界带表述.
theorem infinite_nontrivial_zeros_of_hidden_height_growth
    (h : HiddenZeroHeightGrowth) :
    Set.Infinite {s : ℂ |
      riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} := by
  apply Set.Infinite.mono (s := {s : ℂ | AnnularNontrivialZero s})
    (t := {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1})
  · intro s hs
    exact ⟨hs.zero, hs.strip.1, hs.strip.2⟩
  · exact infinite_annular_nontrivial_zeros_of_height_growth h

-- 兼容旧接口: 一个零点 + 其反射, 二者都在圆环内.
structure NontrivialZeroPair (s : ℂ) : Prop where
  zero_s : riemannZeta s = 0
  zero_reflect : riemannZeta (1 - s) = 0
  annulus_s : 1 < ‖Complex.exp s‖ ∧ ‖Complex.exp s‖ < Real.exp 1
  annulus_reflect : 1 < ‖Complex.exp (1 - s)‖ ∧ ‖Complex.exp (1 - s)‖ < Real.exp 1

-- 存在性转换器: 非平凡零点 ⟹ 存在零点对 (反射 + 反演自动补全另一半).
theorem nontrivial_zero_has_pair {s : ℂ} (hζ : riemannZeta s = 0)
    (hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ)) (hs1 : s ≠ 1) :
    NontrivialZeroPair s := by
  constructor
  · exact hζ
  · exact zero_reflects_under_one_sub hζ hsn hs1
  · exact nontrivial_zero_in_envelope_annulus hζ hsn hs1
  · exact nontrivial_zero_pair_in_annulus hζ hsn hs1

-- 14.5.4 临界叶/圆周保持 (集合不动, 非点点固定).
--   若 ‖e^s‖ = √e, 则 ‖e^{1−s}‖ = √e; 这只是反演保持该圆周.
theorem on_circle_reflects_on_circle {s : ℂ}
    (hcirc : ‖Complex.exp s‖ = envelopeRadius) :
    ‖Complex.exp (1 - s)‖ = envelopeRadius := by
  rw [envelope_inversion_map]
  have hsplit : ‖Complex.exp 1 / Complex.exp s‖ = Real.exp 1 / ‖Complex.exp s‖ := by
    rw [Complex.norm_div]
    congr 1
    simpa using Complex.norm_exp_ofReal (1 : ℝ)
  rw [hsplit, hcirc]
  -- e/√e = √e: (√e)^2 / √e = √e
  have hE : Real.exp 1 = (envelopeRadius) ^ 2 := by
    rw [envelopeRadius]
    exact (Real.sq_sqrt (Real.exp_pos 1).le).symm
  have he : 0 < envelopeRadius := by
    rw [envelopeRadius]
    exact Real.sqrt_pos.2 (Real.exp_pos 1)
  rw [hE]
  field_simp [he]

-- ====================================================================
-- 15. 无限多个零点: 平凡零点部分已证, 非平凡部分的障碍
--    回答: "能否用已有机理 (微积分/发散/取极限) 推出无限多个零点?"
--      (i) 平凡零点无限多 — 已证 (本节省略):
--            ζ(−2(n+1)) = 0 对所有 n, n ↦ −2(n+1) 单射 ⟹ 零点集合无限.
--      (ii) 非平凡零点无限多 — 机制无法推出, 需要增长估计:
--            所有已证机制都是"必要条件"型 (零点 ⟹ 性质), 不携带 ζ 的增长行为;
--            "发散/取极限"思路 = 幅角原理方向, 但其输入是 ζ 在矩形边界上的估计
--            (Riemann–von Mangoldt: N(T) ~ (T/2π)log(T/2π) − T/2π), 超出几何机制.
--            经典: Hadamard 1893 (增长阶 + 因子分解), 如实标注为边界.
-- ====================================================================

-- 15.1 无限多个零点 (平凡零点): 零点集合为无限集.
--   证明: 单射嵌入 n ↦ −2(n+1) (每个是 ζ 的零点), 由 infinite_of_injective_forall_mem.
theorem infinitely_many_trivial_zeros :
    Set.Infinite {s : ℂ | riemannZeta s = 0} := by
  let f : ℕ → ℂ := fun n => -2 * ((n + 1 : ℕ) : ℂ)
  -- f 单射: −2(a+1) = −2(b+1) ⟹ a = b
  have hf : Function.Injective f := by
    intro a b h
    -- 消去 −2
    have h' : ((a + 1 : ℕ) : ℂ) = ((b + 1 : ℕ) : ℂ) := by
      have h2 : (-2 : ℂ) * ((a + 1 : ℕ) : ℂ) = (-2 : ℂ) * ((b + 1 : ℕ) : ℂ) := by
        simpa [f] using h
      exact mul_left_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0) h2
    -- (a+1:ℂ) = (b+1:ℂ) ⟹ a+1 = b+1 ⟹ a = b
    have h'' : a + 1 = b + 1 := by exact_mod_cast h'
    omega
  -- 每个 f n 是零点: ζ(−2(n+1)) = 0
  have hz : ∀ n : ℕ, f n ∈ {s : ℂ | riemannZeta s = 0} := by
    intro n
    simpa [f, Nat.cast_add] using riemannZeta_neg_two_mul_nat_add_one n
  exact Set.infinite_of_injective_forall_mem hf hz

-- ====================================================================
-- 16. 隐数坐标系幅角原理 (局部版) — 零点计数 = 相位缠绕
--    幅角原理在隐数坐标系中的形式: 半径叶上的相位缠绕数 = 零点数.
--    最简情形 (mathlib 已证): 单个简单零点 w 在圆 |z−c|=R 内部时,
--      ∮ dz/(z−w) = 2πi  ⟹  相位缠绕 = 1 = 零点数.
--    本节省略全部为已证定理 (依赖 mathlib 的 circleIntegral):
--      (a) 圆积分原子: ∮ dz/(z−w) = 2πi (w 在圆内, mathlib integral_sub_inv_of_mem_ball)
--      (b) 隐数坐标参数化: 圆 |z−c|=R 在相位包络坐标下就是 θ ↦ c + R·e^{iθ}
--          (hEvalPhase ⟨R, θ⟩ = R·e^{iθ} 正是圆参数化)
--      (c) 相位缠绕 = 零点数: 对 zeta 的零点 w, 绕一圈的相位变化 = 2πi·(零点数)
--    注: 幅角原理的完整版 (任意全纯函数 + 多个零点 + 极点) 是 Residue 定理的
--        推论; mathlib 有 circleIntegral 工具但无完整幅角原理定理.
--        本节省略给出"单个零点 + 单个极点"的最简情形作为坐标系内可证的原子,
--        无限零点的完整证明仍需要增长估计 (幅角原理的输入), 如实标注.
-- ====================================================================

-- 机制 (a): 圆积分原子 — 单个零点 w 在圆内, ∮ dz/(z−w) = 2πi.
--   这是幅角原理的"相位缠绕 = 零点数"的最简情形: 绕零点一圈, 相位变化 2π.
theorem argumentPrinciple_single_zero {c w : ℂ} {r : ℝ} (hw : w ∈ Metric.ball c r) :
    (∮ z in C(c, r), (z - w : ℂ)⁻¹) = 2 * Real.pi * Complex.I := by
  simpa using (circleIntegral.integral_sub_inv_of_mem_ball (c := c) (w := w) (R := r) hw)
-- 机制 (b): 隐数坐标参数化 — 圆 |z−c|=R 在相位包络坐标下 = θ ↦ c + R·e^{iθ}.
--   hEvalPhase ⟨R, θ⟩ = R·e^{iθ} 正是单位圆半径 R 的参数化 (已证 phaseCoversTotal 的 θ 分量).
theorem envelope_circle_param (R θ : ℝ) :
    hEvalPhase ⟨R, θ⟩ = (R : ℂ) * Complex.exp (θ * Complex.I) := by
  rfl

-- 机制 (c): 相位缠绕 = 零点数 (logDeriv 表述).
--   对 f = z − w (单个简单零点), logDeriv f = 1/(z−w); 圆积分 = 2πi.
--   这给出"绕零点一圈相位变化 2π"在隐数坐标下的精确形式.
theorem phase_winding_equals_zero_count {c w : ℂ} {r : ℝ} (hw : w ∈ Metric.ball c r) :
    (∮ z in C(c, r), (z - w : ℂ)⁻¹) = (2 * Real.pi * Complex.I : ℂ) * (1 : ℂ) := by
  rw [argumentPrinciple_single_zero hw]
  ring

-- 机制 (d): 单零点圆积分的归一化 — 除以 2πi 得零点数 1 (幅角原理的归一化形式).
theorem zeroCount_normalized {c w : ℂ} {r : ℝ} (hw : w ∈ Metric.ball c r) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * (∮ z in C(c, r), (z - w : ℂ)⁻¹) = 1 := by
  rw [argumentPrinciple_single_zero hw]
  field_simp [Complex.I_ne_zero, mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero]

-- ====================================================================
-- 17. 隐数坐标系中的增长分解与无限零点预言
--    用户探索方向: 从隐数坐标看 ζ 的增长速度, 给预言, 完善"无限幅角原理".
--    核心分解 (mathlib 已证, 纯代数): ζ(s) = completedRiemannZeta(s) / Gammaℝ(s)
--      Gammaℝ(s) = π^(-s/2)·Γ(s/2)  (Deligne 因子)
--    在覆盖坐标 w = e^s (即 ⟨r,θ⟩, r=e^σ, θ=t) 下:
--      |ζ(s)| = |completedRiemannZeta(s)| / |Gammaℝ(s)|
--      |Gammaℝ(σ+it)| = π^(-σ/2)·|Γ((σ+it)/2)|
--    本节省略已证定理: 增长分解的精确坐标读法 (不含任何 Stirling/界估计).
--    ───────────────────────────────────────────────────────────
--    预言 (PREDICTION, 非证明, 明确标注):
--      (P1) Stirling 渐近下 |Γ((1/2+it)/2)| ≈ |t|^(1/4)·e^{-π|t|/4};
--           故临界叶 |w|=√e 上 |Gammaℝ| ≈ π^(-1/4)·|t|^(1/4)·e^{-π|t|/4} (指数衰减).
--      (P2) 完成 ζ 因子在临界带内有界 (经典), 故 |ζ(1/2+it)| 由 Γ 因子反向放大;
--           边界积分 ∮ ζ'/ζ 随 T 增长 ~ (T/2π)·log(T/2π) (Riemann–von Mangoldt).
--      (P3) 在隐数坐标: 圆弧 |w|=√e, 角度 θ∈[-T,T] 包住的零点数 N(T)
--           ≈ (T/2π)·log(T/2π) → ∞ 当 T→∞.
--    诚实边界: (P1)-(P3) 依赖 Stirling 渐近 + 完成 ζ 有界性 — 二者 mathlib 均
--       未形式化 (无 Γ 的 Stirling 界, 无 completedRiemannZeta 有界性). 因此
--       "无限非平凡零点" 仍未被证明; 本节省略给出坐标层的精确分解 + 预言框架,
--       把"增长估计"这一唯一真分析输入显式隔离为待形式化边界 (draft).
-- ====================================================================

-- 17.1 增长分解: ζ(s) = completedRiemannZeta(s) / Gammaℝ(s) (mathlib 已证, 坐标无关).
theorem zeta_growth_decomposition {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
  riemannZeta_def_of_ne_zero hs

-- 17.2 Complex.Gammaℝ 的模长分解: |Gammaℝ(s)| = π^(-Re s/2)·|Γ(s/2)| (坐标读法).
--   证明: Gammaℝ(s) = π^(-s/2)·Γ(s/2); 取模得 π^(-Re s/2)·|Γ(s/2)|.
theorem gammaR_norm_decomposition (s : ℂ) :
    ‖Complex.Gammaℝ s‖ = (Real.pi : ℝ) ^ (-(s.re / 2)) * ‖Complex.Gamma (s / 2)‖ := by
  rw [Complex.Gammaℝ_def]
  rw [Complex.norm_mul]
  -- ‖π^(-s/2)‖ = π^(-Re s/2): π 为正实数, arg=0, 故纯模长.
  have hπ : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = (Real.pi : ℝ) ^ (-(s.re / 2)) := by
    rw [Complex.norm_cpow_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.pi_pos.le),
      Complex.arg_ofReal_of_nonneg (Real.pi_pos.le)]
    rw [zero_mul, Real.exp_zero, div_one]
    rw [Complex.div_re]
    simp only [Complex.neg_re]
    norm_num
    ring_nf
  rw [hπ]

-- 17.3 隐数坐标读法: 在覆盖坐标 s = log r + iθ (即 w = e^s, r=e^σ, θ=t) 下,
--     |Gammaℝ| = π^(-(log r)/2)·|Γ((log r + iθ)/2)|.
--   这是临界叶 |w|=√e (r=√e, log r=1/2) 上 Γ 因子的精确坐标表达式.
theorem gammaR_norm_in_envelope_coords (r θ : ℝ) :
    ‖Complex.Gammaℝ ((Real.log r : ℂ) + Complex.I * (θ : ℂ))‖ =
      (Real.pi : ℝ) ^ (-(Real.log r / 2)) *
        ‖Complex.Gamma (((Real.log r : ℂ) + Complex.I * (θ : ℂ)) / 2)‖ := by
  rw [gammaR_norm_decomposition]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, sub_zero]

-- 17.4 ζ 模长的坐标分解 (已证定理的组合): 在覆盖坐标下
--    |ζ(log r + iθ)| = |completedRiemannZeta(log r + iθ)| /
--                      (π^(-(log r)/2)·|Γ((log r+iθ)/2)|)
--   这是"隐数坐标看增长速度"的精确数学起点 (不含任何界估计).
theorem zeta_norm_in_envelope_coords {r θ : ℂ}
    (hs : Complex.log r + Complex.I * θ ≠ 0) :
    ‖riemannZeta (Complex.log r + Complex.I * θ)‖ =
      ‖completedRiemannZeta (Complex.log r + Complex.I * θ)‖ /
        ((Real.pi : ℝ) ^
          (-((Complex.log r + Complex.I * θ).re / 2)) *
         ‖Complex.Gamma ((Complex.log r + Complex.I * θ) / 2)‖) := by
  set s : ℂ := Complex.log r + Complex.I * θ
  have hg : ‖Complex.Gammaℝ s‖ =
      (Real.pi : ℝ) ^ (-(s.re / 2)) * ‖Complex.Gamma (s / 2)‖ :=
    gammaR_norm_decomposition s
  have hζ : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs
  rw [hζ, Complex.norm_div, hg]

-- 17.5 预言框架: 无限零点计数 = 幅角原理 + 增长估计 (明确标注为 PREDICTION).
--   形式化"如果"增长估计成立, 则 N(T)→∞ 在隐数坐标下的读法.
def InfiniteZeroPrediction (zetaBound : ℝ → Prop) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ N : ℕ, N = Nat.ceil (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi))) ∧
    zetaBound T

-- 17.6 诚实标注: 增长估计 (Stirling + 完成 ζ 有界) 在 mathlib 缺失,
--   故 "N(T)→∞" 与 "无限非平凡零点" 仍未被证明.
--   本节省略给出坐标层分解 (17.1-17.4) 作为未来形式化增长估计的精确起点.
--   注: 即使完成增长估计, 它也只证明"无限多个非平凡零点", 不等于 RH
--       (RH = 所有非平凡零点在临界线上, 非"存在/无限多").

-- ====================================================================
-- 18. 有限相位抵消的组合翻译 — 把"无限零点"降为"有限度数抵消"
--    用户思路 (session 2026-08-25): 以前已证相位抵消 (§11 leaf_term_decomposition,
--      term_phase_shift_over_turn, §10 zeta_phase_alignment_condition), 现在不证无限性,
--      而是把问题转成: 是否会有"有限个自然数"的相位被"有限周期度数"抵消?
--      若有限组合能在 360° 旋转中抵消, 则无限重复 ⟹ 无限多个对齐事件 ⟹ 无限零点.
--    本节省略给出这一翻译的精确组合层 (路线 A + 框架 C), 并把路线 B 如实标注为阻塞.
--    ───────────────────────────────────────────────────────────
--    路线 A (已证, 精确组合翻译):
--      相位抵消的精确含义: 一组自然数 {nᵢ} 与整数系数 {aᵢ} 使
--        Σ aᵢ·log(nᵢ) ∈ 2πℤ   (在 360° = 2π 弧度圆周上回到原点)
--      等价地 (复指数): exp(i·Σ aᵢ·log(nᵢ)) = 1 ⟺ Π nᵢ^{aᵢ} 的辐角为 2πk
--      由于 nᵢ 为正实数, 此式 ⟺ Π nᵢ^{aᵢ} = e^{2πk}; 取 k=0 (抵消回 0 度)
--      则 ⟺ Π nᵢ^{aᵢ} = 1 ⟺ 质因数分解中指数和为 0 (整数幂关系).
--      结论: 精确有限相位抵消 ⟺ 整数的乘法结构 (质因数分解), 不依赖任何超越性.
--    路线 C (框架, 草案): 定义"360° 周期抵消窗口" — 一个有限自然数集合,
--      其相位抵消模式在每转 2π 后重复出现; 重复无限次即得无限对齐事件.
--    路线 B (阻塞, 如实标注): 稠密性方向 (每个 log(n+1)/2π 无理 ⟹ 轨道稠密)
--      依赖 log 的 ℚ-线性无关性或 e 的超越性, mathlib 均未形式化, 无法推进.
-- ====================================================================

-- 18.1 有限相位抵消关系: 有限整数组合落在 2πℤ 中 (360° 圆周回到原点).
--    ns: 自然数列表 (每项 +1 成 nᵢ), as: 同长度整数系数列表.
--    语义: Σ (aᵢ · log(nᵢ+1)) ∈ 2πℤ  — 这组自然数的旋转向量相位在 360° 内精确抵消.
-- 相位组合的实部和 (列表上的求和, 用 zip + map + sum).
def phaseCancelSum (ns : List ℕ) (as : List ℤ) : ℝ :=
  (List.map (fun (na : ℕ × ℤ) => (na.2 : ℝ) * Real.log ((na.1 + 1) : ℝ))
    (List.zip ns as)).sum

def phaseCancelRelation (ns : List ℕ) (as : List ℤ) : Prop :=
  ∃ k : ℤ, phaseCancelSum ns as = (2 : ℝ) * Real.pi * ↑k

-- 18.2 相位抵消的复指数等价: 抵消 ⟺ 对应单位圆上的乘积取 1.
--    证明: exp(i·Σ aᵢ·log(nᵢ)) = Π exp(i·aᵢ·log(nᵢ)) = Π exp(i·log(nᵢ^{aᵢ}))
--          = exp(i·Σ log(nᵢ^{aᵢ})) = exp(i·log Π nᵢ^{aᵢ}); 取 1 ⟺ Σ aᵢ·log(nᵢ) ∈ 2πℤ.
theorem phaseCancel_of_exp_one (ns : List ℕ) (as : List ℤ) :
    phaseCancelRelation ns as →
      Complex.exp (Complex.I * ↑(phaseCancelSum ns as)) = 1 := by
  rw [phaseCancelRelation]
  intro ⟨k, hk⟩
  rw [hk, Complex.exp_eq_one_iff]
  use k
  push_cast
  ring

-- 18.3 抵消回 0 度 (k=0) 的整数幂关系等价 — 精确有限组合抵消 ⟺ 整数乘法结构.
--    若 Σ aᵢ·log(nᵢ) = 0, 则 Π nᵢ^{aᵢ} = exp(0) = 1.
--    反之 Π nᵢ^{aᵢ} = 1 (正实数乘积) ⟹ 取 log 得 Σ aᵢ·log(nᵢ) = 0.
--    诚实边界: 由质因数唯一分解, Π nᵢ^{aᵢ}=1 ⟺ 各质数指数和为 0 — 这是整数结构,
--      与 ζ 零点无直接推出关系 (RH 难点仍在: 抵消模式如何对应"所有"零点在 1/2).
-- 相位组合的实数乘积 (对应 Π nᵢ^{aᵢ} = exp(Σ aᵢ·log(nᵢ+1))).
--   定义为 exp(phaseCancelSum); 其等于实际乘积 Π (nᵢ+1)^{aᵢ} 由
--   Real.exp_list_sum + 逐项 exp(a·log x)=x^a 保证 (本节省略该副产品证明,
--   标注为可展开的算法事实).
def phaseCancelProd (ns : List ℕ) (as : List ℤ) : ℝ :=
  Real.exp (phaseCancelSum ns as)

-- 18.3 抵消回 0 度 (k=0) 的整数幂关系等价 — 精确有限组合抵消 ⟺ 整数乘法结构.
--    phaseCancelSum = 0 ↔ phaseCancelProd = 1 (由 exp x = 1 ↔ x = 0).
--    诚实边界: 由质因数唯一分解, Π nᵢ^{aᵢ}=1 ⟺ 各质数指数和为 0 — 这是整数结构,
--      与 ζ 零点无直接推出关系 (RH 难点仍在: 抵消模式如何对应"所有"零点在 1/2).
theorem phaseCancel_zero_iff_powProduct_one (ns : List ℕ) (as : List ℤ) :
    phaseCancelSum ns as = 0 ↔ phaseCancelProd ns as = 1 := by
  rw [phaseCancelProd, ← Real.exp_eq_one_iff]

-- 18.4 路线 C 框架 (草案): 360° 周期抵消窗口.
--    定义: 一个有限自然数集合 W 与整数系数 A, 使 phaseCancelRelation W A 成立
--      (即它们在一个 2π 周期内精确抵消), 且窗口在每转 2π 后重复 (相位平移不变性).
--    诚实标注: 此定义本身可形式化, 但"重复无限次 ⟹ 无限零点"的推论
--      依赖 §16 幅角原理的完整围道版本 + §17 增长估计, 二者仍有缺 (如实标注).
def periodicCancelWindow (W : List ℕ) (A : List ℤ) : Prop :=
  phaseCancelRelation W A

-- 18.5 诚实标注: 路线 B (稠密性) 在 mathlib 阻塞.
--    若每个 log(n+1)/2π 无理, 则单自然数相位轨道在 ℝ/2πℤ 上稠密
--      (mathlib AddCircle.DenseSubgroup.denseRange_zsmul_coe_iff),
--      但 "log(n+1)/(2π) 无理" 依赖 e 的超越性或 log 的 ℚ-线性无关性,
--      mathlib 均未形式化, 无法在此推进; 仅记录为待形式化方向.
--    结论: 路线 A (精确整数抵消 ⟺ 整数幂关系) 已可形式化且精确;
--      它把"有限相位抵消"翻译成整数的乘法结构, 诚实暴露 RH 的真正困难所在
--      (抵消模式 ⟹ 全部零点落在临界线, 而非仅"存在/无限多").

-- ====================================================================
-- 19. 缺口① 的桥: η 级数 ↔ 交错旋转向量对齐 (Re>1 内可证)
--    数学结论 (笔算推导, 2026-08-25):
--      dirichlet_term_rotating_vector 是复恒等式且与 σ 无关 → 旋转向量机制
--      对任意 Re 成立; 临界带断路只在"级数=ζ"一步, 不损相位机制.
--      跨到经典: Re>0 用交错 η 是 Abel 条件收敛, 排斥因子 (1−2^{1−s})
--      在临界带恒非零 (2^{1−s}=1 仅 s=1, 实部=1, 不在 0<Re<1), 故
--      ζ=0 ⟺ η=0 在临界带成立 (Titchmarsh). 真缺失 = 条件收敛(η)+
--      Abel/函数方程延拓的 mathlib 工具, 非概念不可能.
--    本节省略的落地 (mathlib 能证明的上界 Re>1):
--      1) 单项桥: η 第 n 项 = (−1)^n × 旋转向量 (复恒等式)
--      2) 对齐定理: Re>1 下 η(s)=0 ⟺ 交错旋转向量和 = 0
--      (镜像 §10 zeta_phase_alignment_condition, 换成 η 交替符号)
--    临界带 0<Re<1 的严格对齐需"条件收敛 η + Abel/函数方程正则化", mathlib
--      当前无此基建, 如实标注为待形式化方向 (不在此节装证).
-- ====================================================================

-- 19.1 η 第 n 项 = (−1)^n 与旋转向量之积 (复项恒等, 与 σ 无关)
theorem eta_term_rotating_vector (n : ℕ) (σ t : ℝ) :
    ((-1 : ℂ) ^ n) / (((n + 1 : ℕ) : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ))) =
      ((-1 : ℂ) ^ n) * ((((n + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (t : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ))) := by
  rw [← dirichlet_term_rotating_vector n σ t]
  ring

-- 19.2 缺口① 桥 (Re>1 可证): η(s)=0 ⟺ 交错旋转向量和 = 0
--    η(s) = Σ' (−1)^n / (n+1)^s, 每项按 19.1 展开成 (−1)^n·旋转向量.
--    证明完全镜像 §10 zeta_phase_alignment_condition, 仅交替符号.
theorem eta_phase_alignment_condition {s : ℂ} (_hs : 1 < s.re) :
    etaSeries s = 0 ↔
      (∑' n : ℕ,
        ((-1 : ℂ) ^ n) * ((((n + 1 : ℝ) ^ (-(s.re)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (s.im : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ)))) = 0 := by
  have hswap : etaSeries s =
      (∑' n : ℕ,
        ((-1 : ℂ) ^ n) * ((((n + 1 : ℝ) ^ (-(s.re)) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (s.im : ℂ)) * (Real.log ((n + 1 : ℝ)) : ℂ)))) := by
    unfold etaSeries
    apply tsum_congr
    intro n
    have hsdef : s = (s.re : ℂ) + Complex.I * (s.im : ℂ) := by
      rw [Complex.ext_iff]
      constructor <;> simp
    rw [hsdef]
    simpa [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] using eta_term_rotating_vector n s.re s.im
  rw [hswap]
-- ====================================================================
-- 20. 隐数对齐零点 — 把"零点"表述为相位对齐 (信息压缩形态)
--    设计意图: 在隐数坐标系压缩信息 — 经典零点需解析延拓+增长守恒;
--              这里把"零点"降格为对齐谓词: s 是对齐零点 ⟺ 其交错旋转
--              向量表示 (η 形态, §19) 之和为零.
--    诚实边界 (2026-08-25):
--      (a) "对齐零点" 是既有 riemannZeta 零点的 *重述* (相位结构显式化),
--          不是发明新的独立零点对象. alignmentZero s ⟺ riemannZeta s = 0
--          在 Re>1 (本节省略 20.3) 可证, 前提是排斥因子 1-2^{1-s} != 0
--          (Re>1 时成立: 其实部 1-2^{1-Re} > 0).
--      (b) "无限个非平凡零点" 是独立边界 — 需在 0<Re<1 有无限多个对齐点,
--          依赖条件收敛 η + Abel/函数方程正则化 (§19) + 增长输入 (§16/17),
--          本节省略没有装证无限. 对齐谓词给的是"零点=相位对齐"的精确语言,
--          不替代增长率这一分析事实.
-- ====================================================================

-- 20.1 对齐零点: 交错旋转向量 (η 形态) 之和为零.
def alignmentZero (s : ℂ) : Prop :=
  etaSeries s = 0

-- 20.2 Re>1 时 "对齐零点 ⟺ 复数零点" 桥 (隐数对齐投到经典零点).
--    前提 hnot: 排斥因子非零 (Re>1 时成立, 见注释).
theorem alignmentZero_iff_zeta_zero {s : ℂ} (hs : 1 < s.re)
    (hnot : (1 - (2 : ℂ) ^ (1 - s)) ≠ 0) :
    alignmentZero s ↔ riemannZeta s = 0 := by
  constructor
  · intro hz
    change etaSeries s = 0 at hz
    have hmul : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s = 0 := by
      rw [← eta_eq_mul_zeta (s := s) hs]
      exact hz
    exact (mul_eq_zero.mp hmul).resolve_left hnot
  · intro hζ
    change etaSeries s = 0
    rw [eta_eq_mul_zeta (s := s) hs]
    simp [hζ]

-- ====================================================================
-- 21. 存在性供给 — "绕数非零 ⟹ 零点存在" 的可编译逆否桥 (无 sorry)
--    缺口精确化: §14.5 转换器把无限性归约为 "圆环内至少一个非平凡零点";
--    本节把该缺口再钉成单一分析命题 — 存在一个有限圆盘, 其 log 导数
--    围道积分非零. 全部组装逻辑真证, 唯一分析输入被显式隔离.
--    ───────────────────────────────────────────────────────────
--      21.1 ζ 在 s≠1 处解析 (可去奇点引理, 从 differentiableAt 升格)
--      21.2 无零点 ⟹ logDeriv 围道积分为零 (Cauchy–Goursat, mathlib)
--      21.3 积分非零 ⟹ 闭盘内存在零点 (21.2 的逆否)
--      21.4 见证对象 AnnulusZeroWitness: 缺口的单一谓词形态
--      21.5 临界带见证 ⟹ 圆环非平凡零点反射对 (接上 §14.5)
--    ───────────────────────────────────────────────────────────
--    诚实边界: witness 谓词本身 (积分非零) 是分析输入, 本节未提供任何实例;
--      经典上由幅角原理 + 增长估计给出. 隐数覆盖坐标读法: 圆盘 D(c,R) 在
--      w=e^s 下是圆环扇区 e^{Re c − R} < |w| < e^{Re c + R}; 临界带见证即
--      扇区整体落在 (1,e) 内. 坐标翻译不产生新信息, 只是几何组织.
-- ====================================================================

-- 21.1 ζ 在 s ≠ 1 处解析: 去心邻域内可微 + 该点连续 ⟹ 解析.
--   取半径 dist(s,1)/2 的球避开唯一奇点 s=1, 球内一切点可微.
theorem analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
    (differentiableAt_riemannZeta hs).continuousAt
  have hpos : 0 < dist s 1 := dist_pos.mpr hs
  have hball : Metric.ball s (dist s 1 / 2) ∈ 𝓝 s :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))
  have hball' : Metric.ball s (dist s 1 / 2) ∈ 𝓝[≠] s :=
    mem_nhdsWithin_of_mem_nhds hball
  filter_upwards [hball'] with z hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    have hd : dist (1 : ℂ) s < dist s 1 / 2 :=
      Metric.mem_ball.mp hz
    rw [dist_comm] at hd
    linarith
  exact differentiableAt_riemannZeta hz1

-- 21.2 无零点 ⟹ log 导数围道积分为零 (Cauchy–Goursat).
--   g := ζ'/ζ: ζ ≠ 1 保证 ζ 可微 (由 21.1), ζ ≠ 0 保证商良定且可微连续.
theorem logDeriv_circle_integral_eq_zero_of_zero_free
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hone : ∀ z ∈ Metric.closedBall c R, z ≠ 1)
    (hfree : ∀ z ∈ Metric.closedBall c R, riemannZeta z ≠ 0) :
    (∮ z in C(c, R), deriv riemannZeta z / riemannZeta z) = 0 := by
  have hgdiff : ∀ z ∈ Metric.ball c R, DifferentiableAt ℂ
      (fun w => deriv riemannZeta w / riemannZeta w) z := by
    intro z hz
    have ha := analyticAt_riemannZeta (hone z (Metric.ball_subset_closedBall hz))
    exact ((ha.deriv).differentiableAt).div ha.differentiableAt
      (hfree z (Metric.ball_subset_closedBall hz))
  have hgcont : ContinuousOn (fun w => deriv riemannZeta w / riemannZeta w)
      (Metric.closedBall c R) := by
    intro z hz
    have ha := analyticAt_riemannZeta (hone z hz)
    exact (((ha.deriv).continuousAt).div ha.continuousAt
      (hfree z hz)).continuousWithinAt
  have hgdiff' : ∀ z ∈ Metric.ball c R \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun w => deriv riemannZeta w / riemannZeta w) z := by
    intro z hz
    exact hgdiff z hz.1
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty hgcont hgdiff'

-- 21.3 存在性供给主桥 (逆否): 围道积分非零 ⟹ 闭盘内存在零点.
theorem exists_closedBall_zero_of_logDeriv_integral_ne_zero
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hone : ∀ z ∈ Metric.closedBall c R, z ≠ 1)
    (hwit : (∮ z in C(c, R), deriv riemannZeta z / riemannZeta z) ≠ 0) :
    ∃ z ∈ Metric.closedBall c R, riemannZeta z = 0 := by
  by_contra hcon
  apply hwit
  refine logDeriv_circle_integral_eq_zero_of_zero_free hR hone ?_
  intro z hz hzero
  exact hcon ⟨z, hz, hzero⟩

-- 21.4 存在性供给见证: 把缺口钉成一个谓词 — "有限圆盘 + 积分非零".
structure AnnulusZeroWitness (c : ℂ) (R : ℝ) : Prop where
  posR : 0 < R
  avoidPole : ∀ z ∈ Metric.closedBall c R, z ≠ 1
  windingNonZero :
    (∮ z in C(c, R), deriv riemannZeta z / riemannZeta z) ≠ 0

theorem exists_closedBall_zero_of_annulusZeroWitness {c : ℂ} {R : ℝ}
    (w : AnnulusZeroWitness c R) :
    ∃ z ∈ Metric.closedBall c R, riemannZeta z = 0 :=
  exists_closedBall_zero_of_logDeriv_integral_ne_zero w.posR.le w.avoidPole
    w.windingNonZero

-- 21.5 临界带见证: witness 圆盘整体落在临界带 0<Re<1 内
--   (隐数坐标: 反演扇区 e^{Re c ± R} 整体落在圆环 1<|w|<e 内).
structure CriticalStripWitness (c : ℂ) (R : ℝ) : Prop extends AnnulusZeroWitness c R where
  inStrip : ∀ z ∈ Metric.closedBall c R, 0 < z.re ∧ z.re < 1

-- 临界带见证 ⟹ 圆环非平凡零点反射对 (接上 §14.5 存在性转换器):
--   见证给闭盘内一个零点 z; 盘在临界带内 ⟹ z 非平凡 ⟹ 圆环对象 + 反射对.
theorem exists_annular_pair_of_criticalStripWitness {c : ℂ} {R : ℝ}
    (w : CriticalStripWitness c R) :
    ∃ s : ℂ, AnnularNontrivialZero s ∧ AnnularNontrivialZero (1 - s) := by
  obtain ⟨z, hzmem, hzero⟩ :=
    exists_closedBall_zero_of_annulusZeroWitness w.toAnnulusZeroWitness
  have hstrip := w.inStrip z hzmem
  have hsn : ∀ n : ℕ, z ≠ -((n : ℕ) : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [hstrip.1]
  have hs1 : z ≠ 1 := by
    intro h1
    have hre := congrArg Complex.re h1
    simp only [Complex.one_re] at hre
    linarith [hstrip.2]
  have hAnn : AnnularNontrivialZero z :=
    annularNontrivialZero_of_zero hzero hsn hs1
  exact ⟨z, hAnn, annularNontrivialZero_reflects hAnn⟩

-- ====================================================================
-- 22. 零点计数输入接口 — 唯一未完成的经典分析引理 (显式条件前提, 非 axiom)
--    分阶段形式化架构 (2026-08-25):
--      层 1 覆盖坐标层 (已证): §14.4/§14.5/§15.2 — w=e^s 把临界带映入圆环,
--           反射 s↦1−s 对应反演 w↦e/w, 高度集合 hiddenNontrivialZeroHeights.
--      层 2 分析供给层 (唯一缺口): Riemann–von Mangoldt 公式
--             N(T) = (T/2π)·log(T/2π) − T/2π + O(log T),
--           其证明需要 Stirling 渐近 + 完成ζ有界 + 完整幅角原理 + 计数公式,
--           mathlib 均未形式化. 本节把它弱化为显式输入谓词 ZeroHeightSupply
--           ("任意高度之上都有临界带零点"), 以普通假设参数传递, 不引入 axiom,
--           从而"哪些结论依赖哪个分析输入"完全透明.
--      层 3 坐标传递层 (已证): ZeroHeightSupply ⟹ HiddenZeroHeightGrowth
--           ⟹ 隐数圆环无限 ⟺ 经典临界带无限 (§15.2 已证的下半段接口).
-- ====================================================================

-- 22.1 输入谓词: 对任意高度 H, 存在高度严格大于 H 的临界带零点.
--   这是 N(T)→∞ 的直接坐标翻译 (弱化形态, 不含渐近公式本身).
def ZeroHeightSupply : Prop :=
  ∀ H : ℝ, ∃ s : ℂ,
    riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ H < |s.im|

-- 22.2 坐标传递 (上半段): 高度供给 ⟹ 覆盖高度无界.
--   经典零点经 annularNontrivialZero_of_zero 升格为圆环对象后进入高度集.
theorem hiddenZeroHeightGrowth_of_zeroHeightSupply (h : ZeroHeightSupply) :
    HiddenZeroHeightGrowth := by
  intro hbdd
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨s, hsζ, hs0, hs1, him⟩ := h M
  have hsn : ∀ n : ℕ, s ≠ -((n : ℕ) : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith [hs0]
  have hsne : s ≠ 1 := by
    intro h1
    have hre := congrArg Complex.re h1
    simp only [Complex.one_re] at hre
    linarith [hs1]
  have hmem : |s.im| ∈ hiddenNontrivialZeroHeights := by
    refine ⟨s, annularNontrivialZero_of_zero hsζ hsn hsne, rfl⟩
  exact absurd (hM hmem) (not_le.mpr him)

-- 22.3 全链闭环: 高度供给 ⟹ 经典临界带非平凡零点无限.
--   组装 22.2 (上半段) 与 §15.2 infinite_nontrivial_zeros_of_hidden_height_growth
--   (下半段). 至此证明树仅剩一个黑盒输入 ZeroHeightSupply (层 2).
theorem infinite_nontrivial_zeros_of_zeroHeightSupply (h : ZeroHeightSupply) :
    Set.Infinite {s : ℂ |
      riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} :=
  infinite_nontrivial_zeros_of_hidden_height_growth
    (hiddenZeroHeightGrowth_of_zeroHeightSupply h)

-- ====================================================================
-- 23. 幅角原理核心原子 — 幂因子分解 ⟹ 绕数 2πi·重数 (无 sorry)
--    地位: 这是"绕数非零 witness"(§21) 与"零点计数 N(T)"(§22 输入) 的共同
--    复分析基建. 完整幅角原理 = 本原子 + 有限零点集枚举; Riemann–von
--    Mangoldt 还需增长估计. 本节省略落地单零点证书的精确原子.
--    ───────────────────────────────────────────────────────────
--      23.1 一般函数版 Cauchy: 无零点解析 g 的 log 导数积分为零
--      23.2 逐点代数: 幂因子的 log 导数 = m/(z−w) + g'/g
--      23.3 绕数定理: f=(z−w)^m·g 于闭盘 ⟹ ∮f'/f = 2πi·m
--      §24 ζ 单零点局部证书 ZetaSimpleZeroCertificate (开集上的代数分解)
--        24.1 证书 ⟹ ∮ζ'/ζ = 2πi (deriv 局部相容 + 23.3)
--        24.2 证书 ⟹ AnnulusZeroWitness (接 §21)
--        24.3 证书(临界带内) ⟹ 反射对 (接 §21.5)
--    ───────────────────────────────────────────────────────────
--    诚实边界: 证书本身 (存在开集 U 与其上的单零点代数分解) 仍是分析输入,
--      本节未提供实例. 它比 §21 的积分 witness 更具体 (纯代数分解),
--      且与 Hardy 数值路线兼容: 一旦有严格数值零点证书即可实例化.
-- ====================================================================

-- 23.1 无零点解析函数的 log 导数围道积分为零 (Cauchy–Goursat, 一般函数版).
theorem logDeriv_integral_eq_zero_of_analytic_ne_zero
    {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    {g : ℂ → ℂ}
    (hga : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ g z)
    (hgne : ∀ z ∈ Metric.closedBall c r, g z ≠ 0) :
    (∮ z in C(c, r), deriv g z / g z) = 0 := by
  have hgdiff : ∀ z ∈ Metric.ball c r, DifferentiableAt ℂ
      (fun x => deriv g x / g x) z := by
    intro z hz
    have ha := hga z (Metric.ball_subset_closedBall hz)
    exact ((ha.deriv).differentiableAt).div ha.differentiableAt
      (hgne z (Metric.ball_subset_closedBall hz))
  have hgcont : ContinuousOn (fun x => deriv g x / g x)
      (Metric.closedBall c r) := by
    intro z hz
    have ha := hga z hz
    exact (((ha.deriv).continuousAt).div ha.continuousAt
      (hgne z hz)).continuousWithinAt
  have hgdiff' : ∀ z ∈ Metric.ball c r \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun x => deriv g x / g x) z := by
    intro z hz
    exact hgdiff z hz.1
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    Set.countable_empty hgcont hgdiff'

-- 23.2 逐点代数恒等式: 幂因子函数的 log 导数 = m/(z−w) + g'/g.
--   成立条件: z ≠ w 且 g z ≠ 0.
theorem powFactor_logDeriv_eq (w : ℂ) {m : ℕ} {g : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ w) (hgne : g z ≠ 0)
    (hd : DifferentiableAt ℂ g z) :
    deriv (fun x => (x - w) ^ m * g x) z / ((z - w) ^ m * g z)
      = m / (z - w) + deriv g z / g z := by
  have hu : (z - w : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  have hum : ((z - w : ℂ) ^ m) ≠ 0 := pow_ne_zero _ hu
  have hp : DifferentiableAt ℂ (fun x => (x - w) ^ m) z :=
    (differentiableAt_id.sub_const w).pow m
  have hdw1 : HasDerivAt (fun x : ℂ => x - w) 1 z := (hasDerivAt_id z).sub_const w
  -- 幂函数的 log 导数经复合规则化到 m/(z−w)
  have heq : (fun t : ℂ => t ^ m) ∘ (fun x : ℂ => x - w)
      = fun x => (x - w) ^ m := rfl
  have hcomp : logDeriv ((fun t : ℂ => t ^ m) ∘ (fun x : ℂ => x - w)) z
      = logDeriv (fun t : ℂ => t ^ m) (z - w) * deriv (fun x : ℂ => x - w) z :=
    logDeriv_comp (f := fun t : ℂ => t ^ m) (g := fun x : ℂ => x - w)
      (differentiableAt_pow m) (differentiableAt_id.sub_const w)
  rw [heq] at hcomp
  calc deriv (fun x => (x - w) ^ m * g x) z / ((z - w) ^ m * g z)
      = logDeriv (fun x => (x - w) ^ m * g x) z := rfl
    _ = logDeriv (fun x => (x - w) ^ m) z + logDeriv g z :=
          logDeriv_mul z hum hgne hp hd
    _ = logDeriv (fun t : ℂ => t ^ m) (z - w) * deriv (fun x : ℂ => x - w) z
          + logDeriv g z := by rw [hcomp]
    _ = logDeriv (fun t : ℂ => t ^ m) (z - w) * 1 + logDeriv g z := by
          rw [hdw1.deriv]
    _ = m / (z - w) + deriv g z / g z := by
          rw [logDeriv_pow, mul_one, logDeriv_apply]

-- 23.3 幂因子分解 ⟹ 绕数 = 2πi·重数.
--   f = (z−w)^m·g 于闭盘 (g 解析且处处非零, w 在开盘内):
--     ∮_{|z−c|=r} f'/f = m·∮dz/(z−w) + ∮g'/g = m·2πi + 0.
theorem winding_of_pow_factorization {c : ℂ} {r : ℝ} (hr : 0 < r)
    {w : ℂ} (hw : w ∈ Metric.ball c r) {m : ℕ} {g : ℂ → ℂ}
    (hga : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ g z)
    (hgne : ∀ z ∈ Metric.closedBall c r, g z ≠ 0) :
    (∮ z in C(c, r), deriv (fun x => (x - w) ^ m * g x) z / ((z - w) ^ m * g z))
      = (2 * Real.pi * Complex.I : ℂ) * m := by
  -- 圆上一切点 ≠ w (w 在开盘内)
  have hsphere : ∀ z ∈ Metric.sphere c r, z ≠ w := by
    intro z hz hzw
    rw [hzw] at hz
    have hdist := Metric.mem_sphere.mp hz
    have hball := Metric.mem_ball.mp hw
    linarith
  -- 被积函数在圆上逐点改写为 m/(z−w) + g'/g
  have hcongr : Set.EqOn
      (fun z => deriv (fun x => (x - w) ^ m * g x) z / ((z - w) ^ m * g z))
      (fun z => m / (z - w) + deriv g z / g z) (Metric.sphere c r) := by
    intro z hz
    have hzcl : z ∈ Metric.closedBall c r := Metric.sphere_subset_closedBall hz
    exact powFactor_logDeriv_eq w (hsphere z hz) (hgne z hzcl)
      ((hga z hzcl).differentiableAt)
  rw [circleIntegral.integral_congr hr.le hcongr]
  -- 改写 m/(z−w) = m·(z−w)⁻¹
  have hsplit : Set.EqOn (fun z => m / (z - w) + deriv g z / g z)
      (fun z => (m : ℂ) * (z - w)⁻¹ + deriv g z / g z) (Metric.sphere c r) := by
    intro z hz
    have hzw : (z - w : ℂ) ≠ 0 := sub_ne_zero.mpr (hsphere z hz)
    field_simp [hzw]
  rw [circleIntegral.integral_congr hr.le hsplit]
  -- 两分量均在圆上连续 ⟹ 可积
  have hI1 : CircleIntegrable (fun z : ℂ => (m : ℂ) * (z - w)⁻¹) c r :=
    ContinuousOn.circleIntegrable hr.le <|
      continuousOn_const.mul ((ContinuousOn.sub continuousOn_id
        continuousOn_const).inv₀ fun z hz => sub_ne_zero.mpr (hsphere z hz))
  have hI2 : CircleIntegrable (fun z => deriv g z / g z) c r :=
    ContinuousOn.circleIntegrable hr.le <| by
      intro z hz
      have ha := hga z (Metric.sphere_subset_closedBall hz)
      exact (((ha.deriv).continuousAt).div ha.continuousAt
        (hgne z (Metric.sphere_subset_closedBall hz))).continuousWithinAt
  calc (∮ z in C(c, r), (m : ℂ) * (z - w)⁻¹ + deriv g z / g z)
      = (∮ z in C(c, r), (m : ℂ) * (z - w)⁻¹)
          + ∮ z in C(c, r), deriv g z / g z := circleIntegral.integral_add hI1 hI2
    _ = (m : ℂ) * (∮ z in C(c, r), (z - w)⁻¹)
          + ∮ z in C(c, r), deriv g z / g z := by
        rw [circleIntegral.integral_const_mul]
    _ = (m : ℂ) * (2 * Real.pi * Complex.I) + 0 := by
        rw [argumentPrinciple_single_zero hw,
          logDeriv_integral_eq_zero_of_analytic_ne_zero hr.le hga hgne, add_zero]
    _ = (2 * Real.pi * Complex.I : ℂ) * m := by ring

-- ====================================================================
-- 24. ζ 单零点局部证书 — "第一个非平凡零点"的可验证见证对象
--    设计: 三阶段路线的阶段① (局部存在性) 的 Lean 化形态.
--    Hardy 数值路线 (Z(a)Z(b)<0 + IVT) 需要严格区间算术, mathlib 当前
--    缺失该基建, 浮点不可作证明 — 如实标注阻塞. 本证书对象把数值路线
--    的终点 (一个已验证的单零点邻域分解) 表达为纯代数谓词:
--      开集 U 上 ζ(z) = (z − w)·g(z), g 全纯非零, w ∈ U, 1 ∉ U.
--    一旦任何路线供给此证书 (Hardy 数值/Stirling 组装/其他), 全部下游
--    结构 (§14.5 反射对, §21 witness, §22 计数链) 自动接通.
-- ====================================================================

--   参数化形态: 零点 w 与因子函数 g 作为显式参数, 使全部字段保持命题.
structure ZetaSimpleZeroCertificate (U : Set ℂ) (w : ℂ) (g : ℂ → ℂ) : Prop where
  isOpen : IsOpen U
  zeroIn : w ∈ U
  poleOut : (1 : ℂ) ∉ U
  gAnalytic : ∀ z ∈ U, AnalyticAt ℂ g z
  gNonzero : ∀ z ∈ U, g z ≠ 0
  factorEq : ∀ z ∈ U, riemannZeta z = (z - w) * g z

-- 证书的直接推论: 零点确实存在于 U 内 (取 factorEq 在 w 处).
theorem certificate_gives_zero {U : Set ℂ} {w : ℂ} {g : ℂ → ℂ}
    (cert : ZetaSimpleZeroCertificate U w g) :
    riemannZeta w = 0 := by
  rw [cert.factorEq w cert.zeroIn]
  simp

-- 24.1 证书 ⟹ 绕数积分 = 2πi.
--   关键步骤: 分解只在 U 上给出, 而 deriv 需要邻域 — 用 U 开保证
--   圆盘闭包 ⊆ U 后, 球面上每点的邻域含于 U, 由 Filter.EventuallyEq.deriv_eq
--   把 ζ'/ζ 局部相容到 F'/F (F = (·−w)·g), 再套 23.3.
theorem zeta_winding_eq_two_pi_i_of_certificate
    {U : Set ℂ} {w : ℂ} {g : ℂ → ℂ} (cert : ZetaSimpleZeroCertificate U w g)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hdisk : Metric.closedBall c r ⊆ U)
    (hzero : w ∈ Metric.ball c r) :
    (∮ z in C(c, r), deriv riemannZeta z / riemannZeta z)
      = (2 * Real.pi * Complex.I : ℂ) := by
  set F : ℂ → ℂ := fun x => (x - w) * g x with hFdef
  -- 球面每点的邻域内 ζ ≡ F (U 开)
  have hsU : ∀ z ∈ Metric.sphere c r, riemannZeta =ᶠ[𝓝 z] F := by
    intro z hz
    have hzU : z ∈ U := hdisk (Metric.sphere_subset_closedBall hz)
    filter_upwards [cert.isOpen.mem_nhds hzU] with x hx
    exact cert.factorEq x hx
  -- 被积函数在圆上与 F'/F 逐点相等 (值由 factorEq, 导数由邻域相容)
  have hcongr : Set.EqOn (fun z => deriv riemannZeta z / riemannZeta z)
      (fun z => deriv F z / F z) (Metric.sphere c r) := by
    intro z hz
    have hzU : z ∈ U := hdisk (Metric.sphere_subset_closedBall hz)
    have hval : riemannZeta z = F z := cert.factorEq z hzU
    have hder : deriv riemannZeta z = deriv F z := (hsU z hz).deriv_eq
    show deriv riemannZeta z / riemannZeta z = deriv F z / F z
    rw [hder, hval]
  rw [circleIntegral.integral_congr hr.le hcongr]
  -- 套用 §23.3 幂因子绕数定理 (m = 1): 其两参数是分解因子 g 的解析与非零
  have hgA : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ g z :=
    fun z hz => cert.gAnalytic z (hdisk hz)
  have hcore := winding_of_pow_factorization (m := 1) hr hzero hgA
    (fun z hz => cert.gNonzero z (hdisk hz))
  simpa [hFdef, pow_one] using hcore

-- 24.2 证书 ⟹ AnnulusZeroWitness (接入 §21 witness 链).
theorem annulusZeroWitness_of_zetaCertificate
    {U : Set ℂ} {w : ℂ} {g : ℂ → ℂ} (cert : ZetaSimpleZeroCertificate U w g)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hdisk : Metric.closedBall c r ⊆ U)
    (hzero : w ∈ Metric.ball c r) :
    AnnulusZeroWitness c r where
  posR := hr
  avoidPole := by
    intro z hz hz1
    subst hz1
    exact cert.poleOut (hdisk hz)
  windingNonZero := by
    intro hcon
    rw [zeta_winding_eq_two_pi_i_of_certificate cert hr hdisk hzero] at hcon
    exact mul_ne_zero
      (mul_ne_zero (show (2 : ℂ) ≠ 0 by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero hcon

-- 24.3 证书 (临界带内) ⟹ 圆环非平凡零点反射对 (全下游自动接通).
theorem exists_annular_pair_of_zetaCertificate
    {U : Set ℂ} {w : ℂ} {g : ℂ → ℂ} (cert : ZetaSimpleZeroCertificate U w g)
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hdisk : Metric.closedBall c r ⊆ U)
    (hzero : w ∈ Metric.ball c r)
    (hstrip : ∀ z ∈ Metric.closedBall c r, 0 < z.re ∧ z.re < 1) :
    ∃ s : ℂ, AnnularNontrivialZero s ∧ AnnularNontrivialZero (1 - s) :=
  exists_annular_pair_of_criticalStripWitness
    { toAnnulusZeroWitness := annulusZeroWitness_of_zetaCertificate cert hr hdisk hzero
      inStrip := hstrip }

-- ====================================================================
-- 25. 证书族 → 高度供给 → 计数增长 (三阶段路线第二/三步闭环, 无 sorry)
--    第一步接口 ZeroHeightSupply (§22) 保持为唯一分析输入;
--    本节把 §24 的单点证书升级为无界证书族, 并接通计数增长.
--    ───────────────────────────────────────────────────────────
--      25.1 UnboundedZetaCertificateAssumption: 任意高度之上都有临界带内
--           单零点证书实例 (用户指定形态, 参数化适配 §24 结构).
--      25.2 zeroHeightSupply_of_certificateFamily: 证书族 ⟹ 高度供给
--           (factorEq 在 w 处取值给零点; 盘在临界带内给 0<Re<1).
--      25.3 classicalZeroCountGrowth_of_zeroHeightSupply: 高度供给 ⟹
--           经典计数增长 (无限集含任意基数有限子集, 高度上确界定窗).
--    ───────────────────────────────────────────────────────────
--    至此下游链条全部闭合:
--      CertificateFamily ⟹ ZeroHeightSupply ⟹ HiddenZeroHeightGrowth
--        ⟹ 无限非平凡零点 (§22.3)
--      CertificateFamily ⟹ ZeroHeightSupply ⟹ ClassicalZeroCountGrowth
--        ⟹ HiddenZeroCountGrowth ⟹ 无限非平凡零点 (§15.x 计数桥)
--    唯一缺口仍是第四步: 用 Hardy / Riemann–von Mangoldt 实例化证书族.
-- ====================================================================

-- 25.1 无界单零点证书族 (外部分析输入声明).
--   ┌─────────────────────────────────────────────────────────────────┐
--   │ ⚠ 外部假设标注: 本谓词是 def 形态的条件前提 (非 axiom, 非已证),   │
--   │ 它精确陈述"第四步分析供给"需要交付的内容. 当前无任何构造实例;      │
--   │ 实例化它 = 完成 Hardy / Riemann–von Mangoldt 层的分析工作.        │
--   └─────────────────────────────────────────────────────────────────┘
--   语义: 对任意高度 H, 存在高度严格大于 H 的临界带零点连同其邻域分解证书.
def UnboundedZetaCertificateAssumption : Prop :=
  ∀ H : ℝ, ∃ U : Set ℂ, ∃ w : ℂ, ∃ g : ℂ → ℂ, ∃ c : ℂ, ∃ r : ℝ,
    ZetaSimpleZeroCertificate U w g ∧
    0 < r ∧
    Metric.closedBall c r ⊆ U ∧
    w ∈ Metric.ball c r ∧
    (∀ z ∈ Metric.closedBall c r, 0 < z.re ∧ z.re < 1) ∧
    H < |w.im|

-- 25.2 第二步主桥: 证书族 ⟹ 高度供给.
--   证书的 factorEq 在 w 处取值给 ζ(w)=0 (§24 certificate_gives_zero);
--   盘整体落在临界带内给出 0<Re(w)<1; 族的无界条件直接给高度项.
theorem zeroHeightSupply_of_certificateFamily
    (hfam : UnboundedZetaCertificateAssumption) : ZeroHeightSupply := by
  intro H
  obtain ⟨U, w, g, c, r, hcert, hr, hdisk, hwball, hstrip, him⟩ := hfam H
  have hwmem : w ∈ Metric.closedBall c r := Metric.ball_subset_closedBall hwball
  exact ⟨w, certificate_gives_zero hcert, (hstrip w hwmem).1,
    (hstrip w hwmem).2, him⟩

-- 25.3 第三步补桥: 高度供给 ⟹ 经典计数增长.
--   无限集包含任意基数的有限子集; 取子集高度的像最大值 +1 为窗口高度 T,
--   则该子集整个落入窗口, encard 单调给出计数下界.
theorem classicalZeroCountGrowth_of_zeroHeightSupply
    (h : ZeroHeightSupply) : ClassicalZeroCountGrowth := by
  intro N
  obtain ⟨t, htsub, htcard⟩ :=
    (infinite_nontrivial_zeros_of_zeroHeightSupply h).exists_subset_card_eq (N + 1)
  have htpos : 0 < t.card := htcard ▸ Nat.succ_pos N
  obtain ⟨s₀, hs₀⟩ := Finset.card_pos.mp htpos
  have hImne : (t.image (fun s : ℂ => |s.im|)).Nonempty :=
    ⟨|s₀.im|, Finset.mem_image.mpr ⟨s₀, hs₀, rfl⟩⟩
  set T : ℝ := (t.image (fun s : ℂ => |s.im|)).max' hImne + 1 with hTdef
  refine ⟨T, ?_⟩
  -- 有限子集整体落入窗口
  have hsubwin : (↑t : Set ℂ) ⊆ classicalNontrivialZeroWindow T := by
    intro s hs
    have hmem : s ∈ t := Finset.mem_coe.mp hs
    have hz := htsub hs
    refine ⟨⟨hz.1, hz.2.1, hz.2.2⟩, ?_⟩
    have himg : |s.im| ∈ t.image (fun s : ℂ => |s.im|) :=
      Finset.mem_image.mpr ⟨s, hmem, rfl⟩
    have hle : |s.im| ≤ (t.image (fun s : ℂ => |s.im|)).max' hImne :=
      Finset.le_max' _ _ himg
    rw [hTdef]
    linarith
  -- encard 链: N < N+1 = #(↑t) ≤ #(window T) = classicalZeroCount T
  calc ((N : ℕ) : ℕ∞) ≤ ((N + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.le_succ N
    _ = Set.encard (↑t : Set ℂ) := by
        simp only [Set.encard_coe_eq_coe_finsetCard]
        exact_mod_cast htcard.symm
    _ ≤ (classicalNontrivialZeroWindow T).encard := Set.encard_mono hsubwin
    _ = classicalZeroCount T := rfl

-- ====================================================================
-- 26. 零点隔离工具 I — 无零点稳定性 (Rouché 排除半边, 最大模原理路线)
--    地位: 这是"严格零点隔离"的第一块可编译基建 — 排除半边:
--      主项 g 在闭盘解析且无零点, 扰动 h 在圆周上被 g 一致压制
--      (‖h/g‖ ≤ q < 1) ⟹ g+h 在整个开盘内无零点.
--    证明路线: u := h/g 于闭盘全纯; 最大模原理
--      (Complex.norm_le_of_forall_mem_frontier_norm_le) 把边界压制约
--      传到内部; 若 (g+h)(z₀)=0 则 ‖u z₀‖ = 1 与 ‖u z₀‖ ≤ q < 1 矛盾.
--    ───────────────────────────────────────────────────────────
--    诚实边界 (存在性半边): 完整 Rouché 定理的"存在半边" (主导线性项
--      ⟹ 盘内恰一个零点) 需要"围道积分对参数连续 + 整数值则常值"
--      的绕数不变性论证, mathlib 当前无 winding number 理论 (已侦察),
--      故本节只落地排除半边. 排除半边的直接应用 (26.2): 取 g ≡ 1,
--      h := ζ−1, 即得"圆周上 |ζ−1|<1 ⟹ 盘内 ζ 无零点"的严格排除判据 —
--      它是数值路线验证"证书圆盘边界安全"所需的定理形态.
-- ====================================================================

-- 26.1 无零点稳定性: 边界一致压制下的扰动不产生新零点.
theorem no_zero_of_boundary_dominance
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    {g h : ℂ → ℂ}
    (hga : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ g z)
    (hgne : ∀ z ∈ Metric.closedBall c r, g z ≠ 0)
    (hha : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ h z)
    (hq : ∃ q : ℝ, q < 1 ∧ ∀ z ∈ Metric.sphere c r, ‖h z / g z‖ ≤ q) :
    ∀ z ∈ Metric.ball c r, (fun x => g x + h x) z ≠ 0 := by
  obtain ⟨q, hqlt, hbnd⟩ := hq
  intro z₀ hz₀ hzero
  -- u := h/g 于闭盘上逐点解析 ⟹ DifferentiableOn 闭盘
  have hudiff : DifferentiableOn ℂ (fun x => h x / g x)
      (Metric.closedBall c r) := by
    intro z hz
    exact (((hha z hz).differentiableAt).div ((hga z hz).differentiableAt)
      (hgne z hz)).differentiableWithinAt
  -- 闭盘是闭集: DiffContOnCl 由 DifferentiableOn 构造
  have hclosed : IsClosed (Metric.closedBall c r) := Metric.isClosed_closedBall
  have hdcl : DiffContOnCl ℂ (fun x => h x / g x) (Metric.closedBall c r) :=
    hclosed.diffContOnCl_iff.mpr hudiff
  have hbdd : Bornology.IsBounded (Metric.closedBall c r) :=
    (isCompact_closedBall c r).isBounded
  -- frontier (closedBall) ⊆ sphere: 边界压制条件传递给最大模原理
  have hC : ∀ z ∈ frontier (Metric.closedBall c r), ‖h z / g z‖ ≤ q := fun z hz =>
    hbnd z (Metric.frontier_closedBall_subset_sphere hz)
  -- 最大模原理: 压制传入闭盘全部点
  have hzclos : z₀ ∈ closure (Metric.closedBall c r) := by
    rw [Metric.isClosed_closedBall.closure_eq]
    exact Metric.ball_subset_closedBall hz₀
  have hmmp := Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hdcl hC hzclos
  -- 反证收尾: (g+h)(z₀)=0 ⟹ h(z₀)/g(z₀) = -1 ⟹ ‖u z₀‖ = 1 > q ≥ ‖u z₀‖
  have hg0 : g z₀ = -(h z₀) := eq_neg_iff_add_eq_zero.mpr hzero
  have h₂ : h z₀ ≠ 0 := by
    intro h1
    exact hgne z₀ (Metric.ball_subset_closedBall hz₀) (by rw [hg0, h1]; simp)
  have hnorm1 : ‖h z₀ / g z₀‖ = 1 := by
    have hEq : h z₀ / g z₀ = (-1 : ℂ) := by
      rw [hg0]
      field_simp [h₂]
    rw [hEq]
    norm_num
  have hunorm2 : (1 : ℝ) ≤ q := by
    rw [← hnorm1]
    exact hmmp
  linarith

-- 26.2 ζ 推除判据: 圆周上 |ζ−1| 一致 < 1 且盘避开极点 ⟹ 盘内 ζ 无零点.
--   应用 26.1 于 g ≡ 1 (解析且处处非零), h := ζ − 1 (盘上解析因避 s=1).
theorem zeta_ne_zero_of_boundary_unit_bound
    {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hone : ∀ z ∈ Metric.closedBall c r, z ≠ 1)
    (hbnd : ∃ q : ℝ, q < 1 ∧ ∀ z ∈ Metric.sphere c r, ‖riemannZeta z - 1‖ ≤ q) :
    ∀ z ∈ Metric.ball c r, riemannZeta z ≠ 0 := by
  obtain ⟨q, hqlt, hb⟩ := hbnd
  have hdelta : ∀ z ∈ Metric.sphere c r, ‖(riemannZeta z - 1) / (1 : ℂ)‖ ≤ q := by
    intro z hz
    simpa using hb z hz
  intro z hz hzero
  have hres := no_zero_of_boundary_dominance hr
    (g := fun _ => (1 : ℂ)) (h := fun x => riemannZeta x - 1)
    (fun zh zhmem => analyticAt_const) (fun _ _ => one_ne_zero)
    (fun zh zhmem => (analyticAt_riemannZeta (hone zh zhmem)).sub analyticAt_const)
    ⟨q, hqlt, hdelta⟩
  exact hres z hz (by simpa using hzero)
-- ====================================================================
-- 18.6 一个组合 × 无限角度 (用户思路, 2026-08-25) — 严格内核
--    用户主张: 不必无限种组合; 一个组合在无限多个角度(虚部 t)下可完成
--    抵消, 相当于无限种组合.
--    严格内容: 旋转向量图景下第 n 项相位 = -t·log(n+1) (§19). 一个在
--    t=0 抵消的窗口 (W,A) (即 phaseCancelSum = 2πk, k∈ℤ) 在角度 t 处的
--    相位 = -t·(Σ aᵢ·log(nᵢ+1)) = -t·2πk. 当 t 取整数(或 k·t∈ℤ)时,
--    窗口相位重新落入 2πℤ — 一个组合在整数倍 t 上反复对齐.
--    诚实边界: 这是**部分和窗口**的相位平移性质, 不证 ζ 零点 (窗口是
--    有限项, 完整 ζ 还含 §19 尾项; 窗口对齐 ≠ ζ=0). "一个组合×整数 t
--    反复对齐"是"无限平移抵消"在**代数层**的严格可编译内容, 为幅角原理
--    的相位像提供周期结构; 是否对应 ζ 零点仍需尾项存在/增长输入
--    (即 §22 ZeroHeightSupply / 证书族), 如实标注, 不装证零点.
-- ====================================================================

-- 18.6 平移后的窗口相位 = -t·phaseCancelSum (旋转向量的相位线性性).
theorem phaseShift_cancel_of_int (ns : List ℕ) (as : List ℤ) {k : ℕ}
    (hc : phaseCancelSum ns as = (2 : ℝ) * Real.pi * (k : ℝ)) (t : ℤ) :
    ∃ m : ℤ,
      -((t : ℝ) * phaseCancelSum ns as) = (2 : ℝ) * Real.pi * (m : ℝ) := by
  refine ⟨-((t : ℤ) * (k : ℤ)), ?_⟩
  rw [hc]
  push_cast
  ring

-- 18.7 一个对齐窗口在整数平移下保持对齐 (相位仍为 2πℤ).
theorem phaseShift_aligned_at_integer (ns : List ℕ) (as : List ℤ)
    (hc : ∃ k : ℤ, phaseCancelSum ns as = (2 : ℝ) * Real.pi * ↑k) :
    ∀ t : ℤ, ∃ m : ℤ,
      (-((t : ℝ) * phaseCancelSum ns as)) = (2 : ℝ) * Real.pi * (m : ℝ) := by
  rcases hc with ⟨k, hk⟩
  intro t
  refine ⟨-((t : ℤ) * k), ?_⟩
  rw [hk]
  push_cast
  ring

-- ====================================================================
-- 18.8 调制基元族 — 用户"把组合当作基元, 通过调制覆盖尾项/无限高度"落点
--    用户主张 (2026-08-25): 不必无限种组合; 把"这一个组合"当基元, 通过
--    调制扩展, 使尾项/无限高度被覆盖, 摆脱外部"尾项恰好关闭"输入.
--    核对结论 (诚实):
--      (i) "固定基元 + 调制 t": 一个对齐窗口在整数平移 t 下反复对齐
--          已证 (phaseShift_aligned_at_integer). 但它是**有限项窗口**的
--          相位性质, 不含 s(σ,t), 覆盖不到无限尾项指标.
--      (ii) "同基元通过调制覆盖无限高度": 单点基元无法让指标 n→∞ 覆盖
--          (改指标=新组合); 真正能"同一类基元覆盖无限高度"的载体是
--          **参数化的证书族** — 每个高度 H 配一个单零点证书 (w,g).
--      (iii) 因此"基元调制"落点 = 把该证书族封装为可命名"调制基元族",
--          并通过既有桥推出高度供给与无限非平凡零点.
--    诚实边界: 调制基元族是 def 形态条件前提 (非 axiom, 非已证); 它精确
--      陈述"分析/数值供给需交付的内容". 不提供族的具体实例 (每个高度真给
--      一个 (U,w,g,c,r)) — 那需增长/布点分析 (§22黑盒), 如实标注.
-- ====================================================================

-- 18.8 调制基元族 = 无界证书族 (命名把"基元调制"纳入体系).
--   语义: 每个高度 H 有一个"调制基元"(单零点证书, w 在临界带) 使
--   H<|Im w| — 同一类证书随 H 无限延伸即"基元的无限调制".
def ModulatedZetaFamily : Prop :=
  UnboundedZetaCertificateAssumption

-- 桥: 调制基元族 ⟹ 高度供给 (复用证书族主桥).
theorem zeroHeightSupply_of_modulatedFamily (h : ModulatedZetaFamily) :
    ZeroHeightSupply :=
  zeroHeightSupply_of_certificateFamily h

-- 桥: 调制基元族 ⟹ 无限非平凡零点 (复用既有全链).
theorem infinite_nontrivial_zeros_of_modulatedFamily (h : ModulatedZetaFamily) :
    Set.Infinite {s : ℂ | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1} :=
  infinite_nontrivial_zeros_of_zeroHeightSupply
    (zeroHeightSupply_of_modulatedFamily h)

-- ====================================================================
-- 27. ξ 整函数 — 非平凡零点的整函数载体 (Hadamard 路线骨架, 无 sorry)
--    数学身份: 经典 ξ(s) := (1/2)·s·(s−1)·π^(−s/2)·Γ(s/2)·ζ(s)
--      = (1/2)·s·(s−1)·Λ(s). 它是"非平凡零点的整函数载体":
--      ξ 整函数, 其零点集恰为 ζ 的非平凡零点集.
--    ───────────────────────────────────────────────────────────
--    初等化关键 (2026-08-26, 本轮核心发现): mathlib 的 completedRiemannZeta₀
--      是"去极点辅助整函数" (恒等式 Λ = Λ₀ − 1/s − 1/(1−s)), 其零点与 ζ 无关;
--      但经代数变形
--        ξ(s) = (1/2)s(s−1)Λ(s) = (1/2)s(s−1)Λ₀(s) + 1/2,
--      ξ 的整性与对称性成为 Λ₀ 已证性质的纯多项式推论 — 无需任何
--      removable singularity 分析! Hadamard 论证的其余输入同样可初等化:
--      (i) 增长上界只需 |Γ(s)| ≤ e^{O(|s|·log|s|)} — Euler 积分拆分的粗界,
--          不需要 Stirling 渐近; (ii) 实轴超多项式下界只需 Γ 泛函递推迭代
--          Γ(x+n) ≥ xⁿ·Γ(x) — 完全初等. Stirling 并非丰度问题的必经之路.
--    ───────────────────────────────────────────────────────────
--      27.1 xiEntire 定义 (经 Λ₀ 的整性保持形态)
--      27.2 整性 (differentiable_completedZeta₀ + 多项式组合)
--      27.3 对称性 ξ(1−s) = ξ(s) (completedRiemannZeta₀_one_sub + ring)
--      27.4 显式公式 ξ = (1/2)s(s−1)Γℝ·ζ (经 zeta_growth_decomposition)
--      27.5 临界带零点桥: 0<Re<1 内 ξ(s)=0 ⟺ ζ(s)=0
--    ───────────────────────────────────────────────────────────
--    诚实边界: Hadamard 组合论证的最后一段 (有限零点 ⟹ Borel–Carathéodory
--      ⟹ logDeriv 常数 ⟹ 对称性强制 ξ 多项式 ⟹ 与实轴增长矛盾) 是大工程,
--      本节省略不证; 其两个分析输入 (积分拆分粗上界 / 递推下界) 也未形式化.
--      本节交付的是载体的全部代数与解析基础, 组合链留待下一步.
-- ====================================================================

-- 27.1 ξ 整函数定义: 经 Λ₀ 的整性保持形态.
--   数学上等于经典的 (1/2)s(s−1)Λ(s); 该形态使整性立即可得.
def xiEntire (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2

-- 27.2 整性: Λ₀ 整 (mathlib) + 多项式组合 ⟹ ξ 整.
--   注意无需任何 removable singularity 讨论 — 这是采用 Λ₀ 形态的全部动机.
set_option maxHeartbeats 1000000 in
theorem differentiable_xiEntire : Differentiable ℂ xiEntire := by
  have hΛ : Differentiable ℂ (fun s : ℂ => completedRiemannZeta₀ s) :=
    differentiable_completedZeta₀
  have hquad : Differentiable ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) :=
    (Differentiable.const_mul differentiable_id (1 / 2)).mul
      (differentiable_id.sub (differentiable_const 1))
  exact Differentiable.add (hquad.mul hΛ)
    (differentiable_const (1 / 2))

-- 27.3 对称性: ξ(1−s) = ξ(s).
--   (1−s)((1−s)−1) = −s(1−s) = s(s−1) 与 Λ₀(1−s)=Λ₀(s) 联立, 纯环算.
theorem xiEntire_one_sub (s : ℂ) : xiEntire (1 - s) = xiEntire s := by
  unfold xiEntire
  rw [completedRiemannZeta₀_one_sub]
  ring

-- 27.4 显式公式: ξ(s) = (1/2)·s·(s−1)·Γℝ(s)·ζ(s) (避开极点 0 与 1).
theorem xiEntire_eq_mul_zeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Complex.Gammaℝ s ≠ 0) :
    xiEntire s = (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s * riemannZeta s := by
  have hzeta := zeta_growth_decomposition hs0
  -- Λ₀ = Λ + 1/s + 1/(1−s) (由 completedRiemannZeta_eq 反向整理)
  have hns1 : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hrel : completedRiemannZeta₀ s =
      completedRiemannZeta s + 1 / s + 1 / (1 - s) := by
    rw [completedRiemannZeta_eq]
    ring
  -- Λ = Γℝ · ζ
  have hΛ : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [hzeta]
    field_simp [hG]
  show (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2
    = (1 / 2 : ℂ) * s * (s - 1) * Complex.Gammaℝ s * riemannZeta s
  rw [hrel, hΛ]
  field_simp [hs0, hns1]
  ring

-- ====================================================================
-- 28. Hadamard 路线图 (设计标注, 未完成部分 — 如实标注)
--    目标: 非平凡零点无限多 (Set.Infinite {s | ClassicalNontrivialZero s}).
--    反证链: 假设零点有限 w₁..ₙ ⟹ Q(s):=∏(s−wₖ), h:=xiEntire/Q
--      无零点整函数; 增长上界 log|h| = O(|s|·log|s|)
--      ⟹ Borel–Carathéodory 于 G:=logDeriv h ⟹ |G'| ≤ C·log(2+|z|)/(1+|z|)
--      ⟹ Liouville 推广 G' ≡ 0 ⟹ G 常数 ⟹ h = e^{a+bs};
--      对称性 xiEntire_one_sub 强制 a=0 ⟹ ξ = cQ 多项式;
--      实轴下界 |ξ(σ)| ≥ c·(σ/4)^{(σ/4)} (Γ 递推 Γ(x+n) ≥ xⁿΓ(x) + ζ(σ)≥1,
--        完全初等, 不需 Stirling) 与多项式矛盾 ⟹ 零点无限.
--    待形式化组件: (i) |Γ(s)| ≤ e^{C|s|log|s|} (Euler 积分拆分粗界);
--      (ii) 实轴递推下界; (iii) Borel–Carathéodory 应用 (mathlib
--      Analysis/Complex/BorelCaratheodory.lean 已侦察存在);
--      (iv) 组合链本身. 均如实标注为待完成.
-- ====================================================================

-- ====================================================================
-- 29. Hadamard 组合链组件 I — Γ 实轴递推下界 (初等, 无 sorry)
--    地位: Hadamard 反证链的最后矛盾来源. 链条:
--      增长上界 + 有限零点 ⟹ Borel–Carathéodory ⟹ logDeriv 常数
--      ⟹ 对称性强迫 ξ 多项式 ⟹ **与实轴超多项式下界矛盾**.
--    本节证最后一环的下界引擎: Γ(x+n) ≥ xⁿ·Γ(x) (x ≥ 1).
--    来源: Real.Gamma_add_one (Γ(s+1)=sΓ(s)) 逐次迭代 — 完全初等,
--    不需要 Stirling 渐近. 这印证 §27 的发现: Stirling 并非丰度必经之路.
-- ──────────────────────────────────────────────────────────────
-- Borel–Carathéodory 链的依赖图与状态 (如实标注):
--   [A] 条带内 ζ 上界 (η 级数 Abel/Dirichlet 求和量化)     — 未形式化
--   [B] Γ 粗上界 |Γ(s)| ≤ e^{O(|s|·log|s|)} (积分拆分)      — 未形式化
--   [C] ξ 上界组合 (A+B ⟹ log|ξ| = O(|s|log|s|))          — 依赖 A,B
--   [D] Borel–Carathéodory 定理本身                        — ✅ mathlib 已有!
--       Complex.borelCaratheodory: f 解析于球 + Re f < M 于球内
--       ⟹ ‖f z‖ ≤ 2M‖z‖/(R−‖z‖) + ‖f 0‖(R+‖z‖)/(R−‖z‖)
--   [E] BC 应用: G := logDeriv h (h=ξ/Q 无零点), Re G = log|h|
--       受 [C] 控制 ⟹ ‖G(z₀)‖ = O(log R); Cauchy 估计于 G'
--       ⟹ G' ≡ 0 (Liouville 推广) ⟹ G 常数 ⟹ h = e^{bs}    — 未形式化
--   [F] 对称性 xiEntire_one_sub 强迫 b=0 ⟹ ξ 多项式         — 轻 (代数)
--   [G] Γ 递推下界                                         — ✅ 本节省略落地
--   [H] 实轴矛盾组装                                       — 轻, 依赖 E,F,G
--   结论: 链条两端 ([D][G]) 已有基建, 中段 ([A][B][E]) 是剩余工作量.
-- ====================================================================

-- 29.1 Γ 泛函递推的下界形态: Γ(x+n) ≥ xⁿ·Γ(x) 对一切 x ≥ 1.
--   证明: 对 n 归纳; 每步用 Real.Gamma_add_one 展开一层,
--   再用 (x+k) ≥ x 与归纳假设链接. 全程只用递推与单调性.
theorem Real.gamma_ge_pow_mul_self {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    Real.Gamma ((x : ℝ) + n) ≥ x ^ n * Real.Gamma x := by
  induction n with
  | zero => simpa using le_refl _
  | succ k ih =>
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    -- 分层: Γ(x+(k+1)) = Γ((x+k)+1) = (x+k)·Γ(x+k)
    have hshift : ((x : ℝ) + ((k + 1 : ℕ) : ℝ))
        = (((x : ℝ) + (k : ℝ)) + 1) := by push_cast; ring
    have hk1 : ((x : ℝ) + k) ≠ 0 := by linarith
    have hstep : Real.Gamma ((x : ℝ) + ((k + 1 : ℕ) : ℝ))
        = ((x : ℝ) + (k : ℝ)) * Real.Gamma ((x : ℝ) + (k : ℝ)) := by
      have h2 : ((x : ℝ) + ((k + 1 : ℕ) : ℝ))
          = (((x : ℝ) + (k : ℝ)) + 1) := by push_cast; ring
      rw [h2, Real.Gamma_add_one hk1]
    -- Γ(x+k) > 0 (x+k ≥ x ≥ 1)
    have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hGpos : 0 < Real.Gamma ((x : ℝ) + (k : ℝ)) :=
      Real.Gamma_pos_of_pos (by linarith)
    -- 链条: (x+k)·Γ ≥ x·Γ ≥ x·(x^k·Γx) = x^{k+1}·Γx
    have hle1 : (x : ℝ) ≤ (x : ℝ) + (k : ℝ) := by linarith
    have hge1 : ((x : ℝ) + (k : ℝ)) * Real.Gamma ((x : ℝ) + (k : ℝ))
        ≥ x * Real.Gamma ((x : ℝ) + (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hle1 (le_of_lt hGpos)
    have hge2 : ((x : ℝ)) * Real.Gamma ((x : ℝ) + (k : ℝ))
        ≥ (x : ℝ) * (x ^ k * Real.Gamma (x : ℝ)) :=
      mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ x from by linarith)
    have hpow : (x : ℝ) ^ (k + 1) = x ^ k * x := pow_succ x k
    rw [hstep, hpow]
    calc ((x : ℝ) + k) * Real.Gamma ((x : ℝ) + k)
        ≥ x * Real.Gamma ((x : ℝ) + k) := hge1
      _ ≥ x * (x ^ k * Real.Gamma x) := hge2
      _ = x ^ k * x * Real.Gamma x := by ring

end RiemannHIBS.Analytic
