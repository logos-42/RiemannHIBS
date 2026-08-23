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
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section
open scoped Topology

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

end RiemannHIBS.Analytic
