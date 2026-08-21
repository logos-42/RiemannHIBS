-- RiemannHIBS.Hidden — 隐数系统 (Hidden-number system)
-- 对齐上游 HIBS 新版 Definitions.lean (commit cc08ceb 之后):
--   ℂ 带 Add/Mul 实例与 conj, ι_R/hiddenImag/hiddenReal 构造器,
--   CompositeHidden 双分量嵌入, DecidableEq 实例.
-- 隐数运算法则 (HIBS 公理 A2/A3 的实例化):
--   A2a: 加/减留在隐层 (tag = S)
--   A2b: 乘法强制流向实部 (tag = R)
--   A3 : 开方强制流向虚部 (tag = iR)
-- 值类型用 Int (core Lean 无 ℝ/ℚ, 整数坐标足够承载代数骨架).

inductive Tag : Type where
  | S  : Tag
  | R  : Tag
  | iR : Tag
  deriving DecidableEq, Repr

open Tag

-- 虚投影的目标类型 (A1 的 g : S → iℝ)
structure Imag where
  val : Int

-- 复数 (可观测切片), 整数坐标, 带加法/乘法实例与共轭
structure ℂ where
  re : Int
  im : Int

instance : Add ℂ where
  add z w := ℂ.mk (z.re + w.re) (z.im + w.im)

instance : Mul ℂ where
  mul z w := ℂ.mk (z.re * w.re - z.im * w.im) (z.re * w.im + z.im * w.re)

def ℂ0 : ℂ := ℂ.mk 0 0
def ℂ1 : ℂ := ℂ.mk 1 0
def ℂI : ℂ := ℂ.mk 0 1
def conj (z : ℂ) : ℂ := ℂ.mk z.re (-z.im)

theorem ℂ_ext (z w : ℂ) (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; subst hre; subst him; rfl

-- 隐数: ⟨值, 信号标签⟩. 标签是 Flow 运算子的形式实现.
structure Hidden where
  val : Int
  tag : Tag

abbrev S := Hidden

theorem Hidden_ext (h h' : Hidden) (hv : h.val = h'.val) (ht : h.tag = h'.tag) : h = h' := by
  cases h; cases h'; subst hv; subst ht; rfl

-- 显式构造器 (三个信号分支)
def ι_R (a : Int) : S := ⟨a, Tag.R⟩
def hiddenImag (b : Int) : S := ⟨b, Tag.iR⟩
def hiddenReal (a : Int) : S := ⟨a, Tag.S⟩

-- 隐数四则 + 开方 (运算法则)
def hAdd (h₁ h₂ : S) : S := ⟨h₁.val + h₂.val, Tag.S⟩
def hSub (h₁ h₂ : S) : S := ⟨h₁.val - h₂.val, Tag.S⟩
def hMul (h₁ h₂ : S) : S := ⟨h₁.val * h₂.val, Tag.R⟩
def hSqrt (h : S) : S := ⟨h.val, Tag.iR⟩

-- 投影 (A1 的一对非单射投影)
def projR (h : S) : Int := h.val
def projImag (h : S) : Imag := ⟨h.val⟩
def flowTarget (h : S) : Tag := h.tag

-- 嵌入 ι: 复数 → 隐数 (实部走 R 支, 虚部走 iR 支, 再加法合并)
def ι (z : ℂ) : S := hAdd (ι_R z.re) (hiddenImag z.im)

-- 投影 π: 隐数 → 可观测复数
def π (h : S) : ℂ :=
  match h.tag with
  | Tag.S  => ℂ.mk h.val 0
  | Tag.R  => ℂ.mk h.val 0
  | Tag.iR => ℂ.mk 0 h.val

-- 双分量嵌入 (定理 6.5 的 ι'): 实部/虚部分别承载, 避免 hAdd 合并值
structure CompositeHidden where
  realPart : S
  imagPart : S

-- 双分量投影 π': 直接读出两分量值
def π' (c : CompositeHidden) : ℂ := ℂ.mk c.realPart.val c.imagPart.val

-- DecidableEq 实例 (case 拆分 + 手动递归, core 无 deriving 支持结构递归)
instance : DecidableEq ℂ := by
  intro z w
  cases z; rename_i zr zi; cases w; rename_i wr wi
  if hre : zr = wr then
    if him : zi = wi then
      apply isTrue; subst hre; subst him; rfl
    else
      apply isFalse; intro h; apply him
      have h' := congrArg (λ (c : ℂ) => c.im) h; simpa using h'
  else
    apply isFalse; intro h; apply hre
    have h' := congrArg (λ (c : ℂ) => c.re) h; simpa using h'

instance : DecidableEq Hidden := by
  intro h₁ h₂
  cases h₁; rename_i v1 t1; cases h₂; rename_i v2 t2
  if hv : v1 = v2 then
    if ht : t1 = t2 then
      apply isTrue; subst hv; subst ht; rfl
    else
      apply isFalse; intro h; apply ht
      have h' := congrArg (λ (h : Hidden) => h.tag) h; simpa using h'
  else
    apply isFalse; intro h; apply hv
    have h' := congrArg (λ (h : Hidden) => h.val) h; simpa using h'

instance : DecidableEq CompositeHidden := by
  intro a b
  cases a; rename_i r1 i1; cases b; rename_i r2 i2
  if hr : r1 = r2 then
    if hi : i1 = i2 then
      apply isTrue; subst hr; subst hi; rfl
    else
      apply isFalse; intro h; apply hi
      have h' := congrArg (λ (c : CompositeHidden) => c.imagPart) h; simpa using h'
  else
    apply isFalse; intro h; apply hr
    have h' := congrArg (λ (c : CompositeHidden) => c.realPart) h; simpa using h'

-- ============ 隐数运算法则 (流规则) ============

theorem add_flow_S (h₁ h₂ : S) : (hAdd h₁ h₂).tag = Tag.S := rfl
theorem sub_flow_S (h₁ h₂ : S) : (hSub h₁ h₂).tag = Tag.S := rfl
theorem mul_flow_R (h₁ h₂ : S) : (hMul h₁ h₂).tag = Tag.R := rfl
theorem sqrt_flow_iR (h : S) : (hSqrt h).tag = Tag.iR := rfl

-- 运算法则整体声明 (A2a ∧ A2b ∧ A3)
structure HiddenArithmetic : Prop where
  add_flow_S  : ∀ h₁ h₂ : S, (hAdd h₁ h₂).tag = Tag.S
  sub_flow_S  : ∀ h₁ h₂ : S, (hSub h₁ h₂).tag = Tag.S
  mul_flow_R  : ∀ h₁ h₂ : S, (hMul h₁ h₂).tag = Tag.R
  sqrt_flow_iR : ∀ h : S, (hSqrt h).tag = Tag.iR

theorem hiddenArithmetic_holds : HiddenArithmetic :=
  { add_flow_S := add_flow_S
    sub_flow_S := sub_flow_S
    mul_flow_R := mul_flow_R
    sqrt_flow_iR := sqrt_flow_iR }

-- 投影非单射 (A1): 不同隐数可投影到同一可观测值
theorem π_nonInjective : ∃ a b : S, a ≠ b ∧ π a = π b := by
  refine ⟨⟨3, Tag.S⟩, ⟨3, Tag.R⟩, ?_, ?_⟩
  · intro h
    have ht := congrArg (fun x : S => x.tag) h
    simp at ht
  · rfl
