-- RiemannHIBS.Axioms — HIBS 三公理 (A1)(A2)(A3) 的形式声明与模型验证
-- 对齐上游 HIBS 新版 Axioms.lean (commit cc08ceb 之后):
--   Axiom1/Axiom2/Axiom3 为参数化结构, HIBS_Axioms 汇总三公理,
--   all_axioms_hold 在标签对模型 S = ℤ×{S,R,iR} 上验证成立.

import RiemannHIBS.Hidden

open Tag

-- (A1) 单向流的存在性: 一对非单射投影 S ↠ ℝ 与 S ↠ iℝ
structure Axiom1 (S : Type) (f : S → Int) (g : S → Imag) : Prop where
  f_nonInjective : ∃ (a b : S), a ≠ b ∧ f a = f b
  g_nonInjective : ∃ (c d : S), c ≠ d ∧ g c = g d

theorem axiom1_holds : Axiom1 S projR projImag :=
  { f_nonInjective := by
      refine ⟨⟨3, Tag.S⟩, ⟨3, Tag.R⟩, ?_, ?_⟩
      · intro h
        injection h with _ htag
        exact Tag.noConfusion htag
      · rfl
    g_nonInjective := by
      refine ⟨⟨3, Tag.S⟩, ⟨3, Tag.R⟩, ?_, ?_⟩
      · intro h
        injection h with _ htag
        exact Tag.noConfusion htag
      · rfl
  }

-- (A2) ± 在隐层封闭; ×,÷ 强制投影到 ℝ (R 支)
structure Axiom2 (S : Type) (tag : S → Tag) (add sub mul : S → S → S) : Prop where
  add_tag_S  : ∀ (h₁ h₂ : S), tag (add h₁ h₂) = Tag.S
  sub_tag_S  : ∀ (h₁ h₂ : S), tag (sub h₁ h₂) = Tag.S
  mul_tag_R  : ∀ (h₁ h₂ : S), tag (mul h₁ h₂) = Tag.R

theorem axiom2_holds : Axiom2 S flowTarget hAdd hSub hMul :=
  { add_tag_S := by intro h₁ h₂; rfl
    sub_tag_S := by intro h₁ h₂; rfl
    mul_tag_R := by intro h₁ h₂; rfl
  }

-- (A3) 开方强制投影到 iℝ (iR 支)
structure Axiom3 (S : Type) (tag : S → Tag) (sqrt : S → S) : Prop where
  sqrt_tag_iR : ∀ (h : S), tag (sqrt h) = Tag.iR

theorem axiom3_holds : Axiom3 S flowTarget hSqrt :=
  { sqrt_tag_iR := by intro h; rfl }

-- 完整公理系统
structure HIBS_Axioms : Prop where
  a1 : Axiom1 S projR projImag
  a2 : Axiom2 S flowTarget hAdd hSub hMul
  a3 : Axiom3 S flowTarget hSqrt

theorem all_axioms_hold : HIBS_Axioms :=
  { a1 := axiom1_holds
    a2 := axiom2_holds
    a3 := axiom3_holds
  }
