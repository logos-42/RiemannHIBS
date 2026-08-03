-- RiemannHIBS.Hidden — 隐数系统 (Hidden-number system)
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

-- 隐数: ⟨值, 信号标签⟩. 标签是 Flow 运算子的形式实现.
structure Hidden where
  val : Int
  tag : Tag

abbrev S := Hidden

theorem Hidden_ext (h h' : S) (hv : h.val = h'.val) (ht : h.tag = h'.tag) : h = h' := by
  cases h; cases h'; subst hv; subst ht; rfl

-- 复数 (可观测切片), 整数坐标
structure ℂ where
  re : Int
  im : Int

theorem ℂ_ext (z w : ℂ) (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  cases z; cases w; subst hre; subst him; rfl

def ℂ0 : ℂ := ⟨0, 0⟩

-- 隐数四则 + 开方 (运算法则)
def hAdd (h₁ h₂ : S) : S := ⟨h₁.val + h₂.val, Tag.S⟩
def hSub (h₁ h₂ : S) : S := ⟨h₁.val - h₂.val, Tag.S⟩
def hMul (h₁ h₂ : S) : S := ⟨h₁.val * h₂.val, Tag.R⟩
def hSqrt (h : S) : S := ⟨h.val, Tag.iR⟩

-- 显式构造器
def hiddenReal (a : Int) : S := ⟨a, Tag.S⟩
def hiddenProj (a : Int) : S := ⟨a, Tag.R⟩
def hiddenImag (b : Int) : S := ⟨b, Tag.iR⟩

-- 投影 π: 隐数 → 可观测复数
def π (h : S) : ℂ :=
  match h.tag with
  | Tag.S  => ⟨h.val, 0⟩
  | Tag.R  => ⟨h.val, 0⟩
  | Tag.iR => ⟨0, h.val⟩

-- 嵌入 ι: 复数 → 隐数
def ι (z : ℂ) : S := hAdd (hiddenReal z.re) (hiddenImag z.im)

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
