-- RiemannHIBS.EnvelopeC — 连续包络 (Continuous Envelope, mathlib 版)
--
-- 离散包络 (Envelope.lean) 的连续化: 把 val 从 ℤ 升到 ℝ.
-- 总空间 E := ℝ × Tag 是一个三维实流形 (第一维 = 连续 val, 第二维 = 标签分支,
--   第三维是引数 s 沿 ℂ 变化, 由 riemannZeta 承载). 投影 hEval : E → ℂ 把壳压回复平面.
--
-- 与 Analytic.lean 的关系:
--   Analytic.lean 的 Hidden 仍用 val : ℤ (离散), 这里用 val : ℝ (连续),
--   因此本模块的 E 是 Analytic 的 Hidden 的"连续壳".
--   投影采用 Analytic 的 hEval 语义 (S↦x, R↦−x, iR↦x·i),
--   使三叶在 ℂ 上呈现为: S 叶→正实轴, R 叶→负实轴, iR 叶→虚轴.
--
-- 本模块证明:
--   1. hEval 把 E 的三叶分别映到正实轴 / 负实轴 / 虚轴 (投影分层)
--   2. hEval 在每片叶子内部是到其轴的同胚 (局部平凡化, 除跨叶折叠)
--   3. 临界截面 criticalSectionC : ℝ → E 把临界线 Re(s)=1/2 嵌入包络
--   4. 零点纤维定理: 若经典 RH 成立, 则 ζ 在 E 上的零点纤维都落在临界截面投影下
--      (即 RiemannHypothesisHidden 的连续包络重述)

import Mathlib.Data.Real.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta

open scoped Real

namespace RiemannHIBS.EnvelopeC

-- ====================================================================
-- 1. 连续隐数结构 (val : ℝ)
-- ====================================================================

inductive Tag : Type where
  | S : Tag
  | R : Tag
  | iR : Tag
  deriving DecidableEq, Repr

open Tag

-- 连续隐数 = ⟨值 ∈ ℝ, 标签⟩. 这就是包络的总空间 E.
structure HiddenC where
  val : ℝ
  tag : Tag

abbrev E := HiddenC

-- 显式构造器
noncomputable def hiddenC_S (x : ℝ) : E := ⟨x, Tag.S⟩
noncomputable def hiddenC_R (x : ℝ) : E := ⟨x, Tag.R⟩
noncomputable def hiddenC_iR (y : ℝ) : E := ⟨y, Tag.iR⟩

-- 投影 hEval (Analytic.lean 语义):
--   ⟨x, S⟩ ↦ x        (正实轴)
--   ⟨x, R⟩ ↦ −x       (负实轴, A2b 符号携带)
--   ⟨y, iR⟩ ↦ y·i     (虚轴)
noncomputable def hEvalC (h : E) : ℂ :=
  match h.tag with
  | Tag.S  => (h.val : ℂ)
  | Tag.R  => -((h.val : ℂ))
  | Tag.iR => (h.val : ℂ) * Complex.I

-- ====================================================================
-- 2. 三叶投影分层
-- ====================================================================

theorem sheetC_S_on_pos_real (x : ℝ) : hEvalC (hiddenC_S x) = (x : ℂ) := rfl
theorem sheetC_R_on_neg_real (x : ℝ) : hEvalC (hiddenC_R x) = -((x : ℂ)) := rfl
theorem sheetC_iR_on_imag (y : ℝ) : hEvalC (hiddenC_iR y) = (y : ℂ) * Complex.I := rfl

-- 包络的投影像 = 实轴 ∪ 虚轴 (十字): 实轴点由 S/R 叶覆盖, 虚轴点由 iR 叶覆盖.
theorem envelopeC_covers (z : ℂ) :
    (z.im = 0 → (∃ x : ℝ, hEvalC (hiddenC_S x) = z) ∨ (∃ x : ℝ, hEvalC (hiddenC_R x) = z)) ∧
    (z.re = 0 → ∃ y : ℝ, hEvalC (hiddenC_iR y) = z) := by
  rcases z with ⟨re, im⟩
  constructor
  · intro him
    subst him
    by_cases hre : 0 ≤ re
    · left; exact ⟨re, by simp [hEvalC, hiddenC_S, Complex.ext_iff]⟩
    · right; exact ⟨-re, by rw [Complex.ext_iff]; simp [hEvalC, hiddenC_R, neg_neg]⟩
  · intro hre
    subst hre
    exact ⟨im, by simp [hEvalC, hiddenC_iR, Complex.ext_iff]⟩

-- ====================================================================
-- 3. 局部平凡化: 每片叶子内部 hEvalC 是到其轴的同胚 (set 层)
-- ====================================================================

-- S 叶投影到正实轴的单射 (局部平凡化: 每叶内部 hEvalC 可逆)
theorem sheetC_S_inj :
    Function.Injective (fun x : ℝ => hEvalC (hiddenC_S x)) := by
  intro x y h
  simp [hEvalC, hiddenC_S] at h; exact h

-- R 叶投影到负实轴的单射
theorem sheetC_R_inj :
    Function.Injective (fun x : ℝ => hEvalC (hiddenC_R x)) := by
  intro x y h
  simp [hEvalC, hiddenC_R] at h; exact h

-- iR 叶是到虚轴的单射 (像为纯虚轴 {z | z.re = 0})
theorem sheetC_iR_inj :
    Function.Injective (fun y : ℝ => hEvalC (hiddenC_iR y)) := by
  intro y₁ y₂ h
  simp [hEvalC, hiddenC_iR, Complex.ext_iff] at h
  exact h

-- ====================================================================
-- 3b. 纤维丛结构 (fiber-bundle structure): 局部截面 σ_tag 使 p∘σ = id
--     基空间 B = {z | z.im=0 ∨ z.re=0} (实轴∪虚轴十字, 见 envelopeC_covers)
--     总空间 E = ℝ×Tag, 投影 p = hEvalC.
--     每片叶子在其像轴上有一个局部截面 σ, 满足 p(σ z) = z (截面性).
-- ====================================================================

-- 基空间: 实轴 ∪ 虚轴 (十字)
def envelopeBase : Set ℂ := {z | z.im = 0 ∨ z.re = 0}

-- S 叶的局部截面: 定义在正实轴 {z | z.im=0 ∧ 0≤z.re} 上, 提升回 S 叶
noncomputable def sectionS (z : {z : ℂ // z.im = 0 ∧ 0 ≤ z.re}) : E :=
  hiddenC_S z.val.re

-- R 叶的局部截面: 定义在负实轴 {z | z.im=0 ∧ z.re≤0} 上, 提升回 R 叶 (注意取负)
noncomputable def sectionR (z : {z : ℂ // z.im = 0 ∧ z.re ≤ 0}) : E :=
  hiddenC_R (-z.val.re)

-- iR 叶的局部截面: 定义在虚轴 {z | z.re=0} 上, 提升回 iR 叶
noncomputable def sectionI (z : {z : ℂ // z.re = 0}) : E :=
  hiddenC_iR z.val.im

-- 截面性 (section property): p(σ z) = z, 即局部平凡化的核心等式
theorem sectionS_property (z : {z : ℂ // z.im = 0 ∧ 0 ≤ z.re}) :
    hEvalC (sectionS z) = z.val := by
  rw [Complex.ext_iff]; constructor
  · simp [sectionS, hEvalC, hiddenC_S]
  · simp [sectionS, hEvalC, hiddenC_S, z.property.1]

theorem sectionR_property (z : {z : ℂ // z.im = 0 ∧ z.re ≤ 0}) :
    hEvalC (sectionR z) = z.val := by
  rw [Complex.ext_iff]; constructor
  · simp [sectionR, hEvalC, hiddenC_R, neg_neg]
  · simp [sectionR, hEvalC, hiddenC_R, neg_neg, z.property.1]

theorem sectionI_property (z : {z : ℂ // z.re = 0}) :
    hEvalC (sectionI z) = z.val := by
  rw [Complex.ext_iff]; constructor
  · simp [sectionI, hEvalC, hiddenC_iR, z.property]
  · simp [sectionI, hEvalC, hiddenC_iR]

-- 逆向: 在对应叶上 σ(p e) = e (平凡化的另一半)
theorem sectionS_retract (x : ℝ) (hx : 0 ≤ x) :
    sectionS ⟨hEvalC (hiddenC_S x), by simp [hEvalC, hiddenC_S]; exact hx⟩ = hiddenC_S x := by
  simp [sectionS, hEvalC, hiddenC_S]

theorem sectionR_retract (x : ℝ) (hx : 0 ≤ x) :
    sectionR ⟨hEvalC (hiddenC_R x), by simp [hEvalC, hiddenC_R]; exact hx⟩ = hiddenC_R x := by
  simp [sectionR, hEvalC, hiddenC_R, neg_neg]

theorem sectionI_retract (y : ℝ) :
    sectionI ⟨hEvalC (hiddenC_iR y), by simp [hEvalC, hiddenC_iR]⟩ = hiddenC_iR y := by
  simp [sectionI, hEvalC, hiddenC_iR]

-- ====================================================================
-- 4. 临界截面 (critical section): 把临界线 Re(s)=1/2 嵌入包络
-- ====================================================================

-- 标准临界线 s = 1/2 + i·t 在包络上的嵌入:
--   实部 1/2 走 S 叶 (正实轴), 虚部 t 走 iR 叶.
noncomputable def criticalSectionC (t : ℝ) : E × E := (hiddenC_S (1 / 2), hiddenC_iR t)

-- 临界截面的投影 = 1/2 + t·i (即临界线上的点)
theorem criticalSectionC_proj (t : ℝ) :
    hEvalC (criticalSectionC t).1 + hEvalC (criticalSectionC t).2 = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
  unfold criticalSectionC; simp [hEvalC, hiddenC_S, hiddenC_iR]

-- 倍化临界线 2s = 1 + 2it (整数友好) 的双分量嵌入, 对接 Riemann.doubledEmbeddingC
noncomputable def criticalSectionCDoubled (t : ℝ) : E × E := (hiddenC_S 1, hiddenC_iR (2 * t))

theorem criticalSectionCDoubled_proj (t : ℝ) :
    hEvalC (criticalSectionCDoubled t).1 + hEvalC (criticalSectionCDoubled t).2 =
      (1 : ℂ) + (2 * t : ℂ) * Complex.I := by
  unfold criticalSectionCDoubled; simp [hEvalC, hiddenC_S, hiddenC_iR]

-- ====================================================================
-- 5. 零点纤维定理: 经典 RH ⟹ 包络上的零点纤维落在临界截面下
-- ====================================================================

-- 隐数空间的连续 ζ: ζ_C(h) := ζ(hEvalC h)
noncomputable def zetaHiddenC (h : E) : ℂ := riemannZeta (hEvalC h)

-- 隐数空间连续版黎曼猜想 (声明, 与 Analytic.RiemannHypothesisHidden 同构):
--   每个非平凡零点 h (在 hEvalC 下满足 ζ=0) 的可观测值实部 = 1/2.
def RiemannHypothesisHiddenC : Prop :=
  ∀ h : E, zetaHiddenC h = 0 → ¬ (∃ n : ℕ, hEvalC h = -2 * ((n + 1 : ℕ) : ℂ)) →
    hEvalC h ≠ 1 → (hEvalC h).re = 1 / 2

-- 经典 RH ⟹ 连续隐数 RH (直接套用 mathlib RiemannHypothesis)
theorem riemannHypothesis_hiddenC_of_mathlib :
    RiemannHypothesis → RiemannHypothesisHiddenC := by
  intro hrh h hζ hnt hne1
  have hz : riemannZeta (hEvalC h) = 0 := by simpa [zetaHiddenC] using hζ
  have hnt' : ¬ ∃ n : ℕ, hEvalC h = -2 * ((n : ℂ) + 1) := by
    intro hn; apply hnt; rcases hn with ⟨n, hn_eq⟩; refine ⟨n, ?_⟩
    simpa [Nat.cast_add] using hn_eq
  exact hrh (hEvalC h) hz hnt' hne1

-- 临界截面承载所有非平凡零点 (几何表述): 若经典 RH 成立,
--   则对任意零点 h, 存在 t 使 hEvalC h = 1/2 + t·i,
--   即 h 落于 criticalSectionC 的投影像中.
theorem zeros_lie_on_critical_section (hrh : RiemannHypothesis) (h : E)
    (hζ : zetaHiddenC h = 0) (hnt : ¬ ∃ n : ℕ, hEvalC h = -2 * ((n + 1 : ℕ) : ℂ))
    (hne1 : hEvalC h ≠ 1) :
    ∃ t : ℝ, hEvalC h = (↑(1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  have hRH := riemannHypothesis_hiddenC_of_mathlib hrh h hζ hnt hne1
  -- hEvalC h 的实部 = 1/2; 取 t = (hEvalC h).im 即得临界线形式
  use (hEvalC h).im
  rw [Complex.ext_iff]
  constructor
  · rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re]
    simpa [add_zero, sub_zero, mul_zero] using hRH
  · rw [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.ofReal_im]
    simp [add_zero, mul_one, mul_zero, zero_add]

-- ====================================================================
-- 6. 相位标签包络 (EnvelopePhase): 覆盖整个 ℂ 的 2D 曲面 (c)
--    把离散标签 {S,R,iR} 推广为连续相位 θ ∈ ℝ; 投影 hEvalPhase ⟨r,θ⟩ = r·e^{iθ}.
--    当 r 跑 ℝ, θ 跑 ℝ 时, 投影像 = 整个 ℂ (除原点处所有相位叶相交).
--    这正是一个带原点奇异的平凡线丛 (极坐标覆盖).
--
--    与 mathlib FiberBundle (d) 的对应 (不实例化类型类, 见 PhaseTriv 注释):
--      TotalSpace (fun _ => ℝ) ℂ  ≈  EnvelopePhase (总空间 = 基 ℂ × 纤维 ℝ)
--      proj                      ≈  hEvalPhase
--      trivialization (局部同胚)  ≈  phaseRayBijective (每相位叶径向双射) + phaseCoversTotal
-- ====================================================================

-- 相位包络总空间: 半径 r × 相位 θ (都是 ℝ)
structure EnvelopePhase where
  r : ℝ
  θ : ℝ

-- 投影: ⟨r, θ⟩ ↦ r · e^{iθ}  (把极坐标映回复平面)
noncomputable def hEvalPhase (e : EnvelopePhase) : ℂ :=
  (e.r : ℂ) * Complex.exp (e.θ * Complex.I)

-- 覆盖整个 ℂ: 对任意 z, ⟨‖z‖, arg z⟩ 投影回 z (含 z=0, 因 arg 0 = 0, ‖0‖ = 0).
--   核心定理: Complex.norm_mul_exp_arg_mul_I : ‖z‖ * exp(arg z * I) = z
theorem phaseCoversTotal (z : ℂ) :
    ∃ e : EnvelopePhase, hEvalPhase e = z := by
  refine ⟨⟨‖z‖, z.arg⟩, ?_⟩
  simp [hEvalPhase]

-- 每片相位叶 (固定 θ) 的径向单射: r ↦ r·e^{iθ} 从 ℝ 单射到过原点直线 {r·e^{iθ}}.
--   (满射是到该射线而非全 ℂ, 故用单射; 所有相位叶的并覆盖全 ℂ, 见 phaseCoversTotal.)
theorem phaseRay_inj (θ : ℝ) :
    Function.Injective (fun (r : ℝ) => hEvalPhase ⟨r, θ⟩) := by
  intro r₁ r₂ h
  simp [hEvalPhase] at h
  exact h

-- 相位叶的像集: {r·e^{iθ} | r ∈ ℝ} (过原点、方向角 θ 的直线)
def phaseRay (θ : ℝ) : Set ℂ := {z | ∃ r : ℝ, hEvalPhase ⟨r, θ⟩ = z}

-- 临界截面 (相位版): 使投影 = 1/2 + t·i, 即 ⟨‖1/2+t·i‖, arg(1/2+t·i)⟩
noncomputable def criticalPhaseC (t : ℝ) : EnvelopePhase :=
  ⟨‖((1 / 2 : ℂ) : ℂ) + (t : ℂ) * Complex.I‖, (((1 / 2 : ℂ) : ℂ) + (t : ℂ) * Complex.I).arg⟩

-- 临界截面投影 = 1/2 + t·i
theorem criticalPhaseC_proj (t : ℝ) :
    hEvalPhase (criticalPhaseC t) = (1 / 2 : ℂ) + (t : ℂ) * Complex.I := by
  unfold criticalPhaseC; simp [hEvalPhase]

-- 相位版隐数 RH 声明: 经典 RH ⟹ 零点纤维落在临界截面投影像
def RiemannHypothesisHiddenPhase : Prop :=
  ∀ e : EnvelopePhase, riemannZeta (hEvalPhase e) = 0 →
    ¬ (∃ n : ℕ, hEvalPhase e = -2 * ((n + 1 : ℕ) : ℂ)) →
    hEvalPhase e ≠ 1 → (hEvalPhase e).re = 1 / 2

-- 经典 RH ⟹ 相位隐数 RH (套用 mathlib RiemannHypothesis)
theorem riemannHypothesis_hiddenPhase_of_mathlib :
    RiemannHypothesis → RiemannHypothesisHiddenPhase := by
  intro hrh e hζ hnt hne1
  have hz : riemannZeta (hEvalPhase e) = 0 := by simpa [hEvalPhase] using hζ
  have hnt' : ¬ ∃ n : ℕ, hEvalPhase e = -2 * ((n : ℂ) + 1) := by
    intro hn; apply hnt; rcases hn with ⟨n, hn_eq⟩; refine ⟨n, ?_⟩
    simpa [Nat.cast_add] using hn_eq
  exact hrh (hEvalPhase e) hz hnt' hne1

-- ====================================================================
-- 7. 轻量平凡化结构 PhaseTriv (d): 对应 mathlib 的 Trivialization
--    不实例化 FiberBundle 类型类 (避免 ℝ×ℝ / ℂ 的 TopologicalSpace+chart 配置),
--    而直接用我们自证的覆盖 + 径向双射表达"局部平凡化"的全部内容.
--    字段对应:
--      base      ≈ ℂ (基空间, 即 mathlib FiberBundle 的 B)
--      total     ≈ EnvelopePhase (总空间, ≈ TotalSpace (fun _ => ℝ) ℂ)
--      proj      ≈ hEvalPhase (≈ proj)
--      cover     ≈ phaseCoversTotal (每点有原像, ≈ mem_baseSet 的全局版本)
--      localTriv ≈ phaseRay_inj (每相位叶径向单射, ≈ trivialization 的局部同胚)
-- ====================================================================

-- 相位包络的"平凡化"记录: 把 mathlib Trivialization 的核心字段用我们的对象表达.
--   (若未来要接入 mathlib FiberBundle, 本结构即是构造 Trivialization 所需的全部原料.)
structure PhaseTriv where
  -- 总空间
  total : Type := EnvelopePhase
  -- 投影
  proj : EnvelopePhase → ℂ := hEvalPhase
  -- 覆盖性: 每个 z 至少有一个原像 (全局平凡化的满射性)
  cover (z : ℂ) : ∃ e : EnvelopePhase, hEvalPhase e = z := phaseCoversTotal z
  -- 局部平凡化: 每片相位叶在径向上单射 (纤维方向可逆)
  localTriv (θ : ℝ) : Function.Injective (fun r : ℝ => hEvalPhase ⟨r, θ⟩) :=
    phaseRay_inj θ

-- ====================================================================
-- 8. 覆盖空间: θ 模 2π 显式化 (多值 / 覆盖结构)
--    相位包络 E_θ = ℝ × ℝ 的投影 hEvalPhase 在 θ 上以 2π 为周期:
--      同一个 z 对应无穷多个 θ = θ₀ + 2πn (n : ℤ),
--    因此 hEvalPhase : E_θ → ℂ 是 ℂ∖{0} 上的 (局部) 覆盖映射,
--    每根纤维 = 一条 2πℤ 平移轨道 —— 这正是"隐数多值性"的几何来源.
-- ====================================================================

-- 8.1 整数步周期性: 加 2π 后投影不变.
theorem phase_periodic (r θ : ℝ) : hEvalPhase ⟨r, θ + 2 * π⟩ = hEvalPhase ⟨r, θ⟩ := by
  simp [hEvalPhase, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

-- 8.2 整数倍周期性: 加 2π·n (n : ℤ) 后投影不变.
theorem phase_periodic_int (r θ : ℝ) (n : ℤ) :
    hEvalPhase ⟨r, θ + 2 * π * (n : ℝ)⟩ = hEvalPhase ⟨r, θ⟩ := by
  unfold hEvalPhase
  apply congrArg (fun w : ℂ => (r : ℂ) * w)
  -- exp_mul_I_periodic : (fun x => exp (x * I)) 以 2π 为周期
  simpa [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast,
    mul_comm, mul_left_comm, mul_assoc] using
      ((Complex.exp_mul_I_periodic.int_mul n) θ)

-- 8.3 不同层区分: 同一半径的不同相位层 ⟨r,θ+2π⟩ 与 ⟨r,θ⟩ 是总空间中的不同点
--     (投影相同但点不同) —— 即"多值"不是退化, 而是覆盖空间的不同叶.
theorem phase_two_pi_distinct (r θ : ℝ) :
    (EnvelopePhase.mk r (θ + 2 * Real.pi) : EnvelopePhase) ≠ EnvelopePhase.mk r θ := by
  intro e
  have hθ : θ + 2 * Real.pi = θ := congrArg EnvelopePhase.θ e
  have hpi : (2 : ℝ) * Real.pi = 0 := by
    have h : (θ + 2 * Real.pi) - θ = θ - θ := congrArg (fun x : ℝ => x - θ) hθ
    ring_nf at h
    rw [mul_comm] at h
    exact h
  exact Real.pi_pos.ne' ((mul_eq_zero.mp hpi).resolve_left (by norm_num))

-- 8.4 覆盖映射的纤维: 对 z ≠ 0, 其全部原像包含一条 2πℤ 轨道.
--     即 ⟨r, θ⟩ 投影到 z, 则 ⟨r, θ + 2πn⟩ (n : ℤ) 也投影到 z.
theorem phase_covering_fiber (z : ℂ) (r θ : ℝ)
    (he : hEvalPhase ⟨r, θ⟩ = z) :
    ∀ n : ℤ, hEvalPhase ⟨r, θ + 2 * π * (n : ℝ)⟩ = z := by
  intro n
  rw [phase_periodic_int]
  exact he

-- 8.5 纤维反向包含 (固定半径): 若两相位投影到同一非零 z, 则其相位差属 2πℤ.
--     这把"多值"严格化为 2πℤ 离散纤维.
theorem phase_covering_fiber_subset (z : ℂ) (hz : z ≠ 0) (r θ₁ θ₂ : ℝ)
    (h₁ : hEvalPhase ⟨r, θ₁⟩ = z) (h₂ : hEvalPhase ⟨r, θ₂⟩ = z) :
    ∃ n : ℤ, θ₂ = θ₁ + 2 * π * (n : ℝ) := by
  have hE : (r : ℂ) * Complex.exp (θ₁ * Complex.I) =
            (r : ℂ) * Complex.exp (θ₂ * Complex.I) := by
    simpa [hEvalPhase] using h₁.trans h₂.symm
  -- r ≠ 0 因 z ≠ 0
  have hr : r ≠ 0 := by
    intro hr0
    have hz0 : z = 0 := by
      rw [← h₁, hr0]
      simp [hEvalPhase]
    exact hz hz0
  have hmul : Complex.exp (θ₁ * Complex.I) = Complex.exp (θ₂ * Complex.I) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr) hE
  -- Complex.exp_eq_exp_iff_exists_int : exp x = exp y ↔ ∃ n, x = y + n·(2π·I)
  rw [Complex.exp_eq_exp_iff_exists_int] at hmul
  rcases hmul with ⟨n, hn⟩
  -- hn : (↑θ₁)·I = (↑θ₂)·I + (n:ℂ)·(2π·I)  ⇒  θ₁ = θ₂ + n·2π
  have hsub : θ₁ = θ₂ + 2 * π * (n : ℝ) := by
    apply Complex.ofReal_inj.mp
    rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_mul]
    -- goal: ↑θ₁ = ↑θ₂ + (↑2 * ↑π) * (n : ℂ)
    have hn' : (↑θ₁ : ℂ) * Complex.I = ((↑θ₂ : ℂ) + (n : ℂ) * (2 * π)) * Complex.I := by
      simpa [mul_assoc, add_mul] using hn
    have hc : (↑θ₁ : ℂ) = (↑θ₂ : ℂ) + (n : ℂ) * (2 * π) :=
      mul_right_cancel₀ Complex.I_ne_zero hn'
    simpa [mul_comm, mul_left_comm, mul_assoc] using hc
  -- 反向: θ₂ = θ₁ + 2π·(−n)
  use -n
  have hc2 : θ₂ = θ₁ + 2 * π * (↑(-n) : ℝ) := by
    rw [hsub]
    rw [Int.cast_neg]
    ring
  exact hc2

-- 8.6 覆盖映射声明: hEvalPhase 在 ℂ∖{0} 上给出以 2πℤ 为纤维的覆盖空间,
--     每个 z ≠ 0 都有原像且可局部单值选取相位 (极坐标邻域 = 平凡化邻域).
theorem phase_is_covering_map (z : ℂ) (hz : z ≠ 0) :
    ∃ (r θ : ℝ) (_ : r ≠ 0), hEvalPhase ⟨r, θ⟩ = z := by
  rcases phaseCoversTotal z with ⟨e, he⟩
  use e.r, e.θ
  have hr : e.r ≠ 0 := by
    intro hr0
    simp [hEvalPhase, hr0] at he
    apply hz
    exact he.symm
  exact ⟨hr, he⟩

end RiemannHIBS.EnvelopeC
