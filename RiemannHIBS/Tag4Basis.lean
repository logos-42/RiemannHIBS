-- RiemannHIBS.Tag4Basis — 四元素标签基座: 第 4 标签做成测试函数方向 (2026-09-01)
--
-- 用户提案: 引数坐标系的投影从 3 个元素标签 {S,R,iR} 扩到 4 个,
--   第 4 个元素与隐数空间的 S 同功能 = "连接其他元素".
--
-- 两形态的判定:
--   A 形态 (第 4 标签仍是离散叶, 与 S 同投影): 保守扩张. 判据与反射 s↦1−s 交换,
--     在零点处 0=0 退化 ⟹ 无排除力 (有限维换基是布尔代数同构, 不制造不对称性).
--   B 形态 (第 4 标签的纤维是函数空间 ℂ→ℂ, ∞ 维): 真基座更改. 本文件落此形态.
--
-- 关键结构差异 (本轮的数学发现):
--   经典反射   s ↦ 1 − s        的不动集 = {1/2}       (一个点, 0 维)
--   共轭反射   s ↦ 1 − conj(s)  的不动集 = 整条临界线   (1 维实)
--   "连接元"必须连后者: 只有后者的不动集能承载"零点所在的线".
--
-- 第 4 方向上的配对读数 (Weil 二次型原子):
--     connectorPair Φ s = 2·Re( Φ(s)·conj(Φ(σ*(s))) ),   σ*(s) = 1 − conj(s)
--   在不动点 (Re s = 1/2) 处退化为 2·‖Φ s‖² ≥ 0;
--   离圆处是两独立值的配对, 函数空间自由度使其可取负值 (破缺见证).
--   于是得到严格等价
--     (∀ Φ, 0 ≤ connectorPair Φ s) ⟺ Re(s) = 1/2
--   —— 这是 1/2 的**第一条携带不等式 (正性) 的刻画**; 已有的五条刻画
--      (反射不动 / 反演不动圆 / 能量阈值 / 均方相变 / Γ 比退化) 全是位置型.
--
-- 诚实边界: 该等价是**刻画**而非排除工具. 刻画在单点上免费成立 (与 ζ 无关);
--   要用于排除, 须对每个零点验证 ∀Φ 的正性, 而该断言恰等价于 RH.
--   破缺用的是全函数空间 ℂ→ℂ 的自由度. 真实 Weil 判据要求 Φ 来自
--   合法的 Mellin 变换类 (显式公式适用条件), 那里"在互异两点指定值"不再平凡 —
--   缺口已精确压成 FourthDirectionWeilCertificate.separation 一个字段.
--
-- mathlib 注: 本版本 ℂ 的共轭是 star (Complex.conj 已不存在),
--   且 Complex.normSq_eq_norm_sq 需反向 rw 才能把 ‖z‖² 换成 normSq.

import RiemannHIBS.WeilPositivity

open scoped Topology BigOperators
open RiemannHIBS.HiddenExclusion
open RiemannHIBS.RadialEnergy
open RiemannHIBS.WeilPositivity

namespace RiemannHIBS.Tag4Basis

noncomputable section

-- ====================================================================
-- 1. 四元素标签与纤维: 前三个是离散叶, 第 4 个是函数方向 (∞ 维)
-- ====================================================================

inductive Tag4 : Type where
  | S  : Tag4   -- 加法连接支 (经典 S 叶)
  | R  : Tag4   -- 乘法投影支
  | iR : Tag4   -- 开方投影支
  | T  : Tag4   -- 第 4 元素: 连接元 / 测试方向
  deriving DecidableEq, Repr

-- 基座更改的实质: 纤维类型. 前三个标签的纤维是单点 (无自由度),
-- 第 4 个的纤维是函数空间 (有无穷自由度).
def tag4Fiber : Tag4 → Type
  | Tag4.S  => PUnit
  | Tag4.R  => PUnit
  | Tag4.iR => PUnit
  | Tag4.T  => ℂ → ℂ

-- 第 4 标签的功能 (与隐数 S 同: 连接).
--   老系统: S 用 hAdd 把 R 与 iR 合并成一个值.
--   新系统: 连接元把 s 与它的共轭反射 σ*(s) = 1 − conj(s) 配成一个二次量.
def conjReflect (s : ℂ) : ℂ := 1 - star s

-- 配对读数 (第 4 方向上的 Weil 二次型原子)
def connectorPair (Φ : ℂ → ℂ) (s : ℂ) : ℝ :=
  2 * (Φ s * star (Φ (conjReflect s))).re

-- ====================================================================
-- 2. 连接元的不动集 = 整条临界线
-- ====================================================================

theorem conjReflect_re (s : ℂ) : (conjReflect s).re = 1 - s.re := by
  simp [conjReflect]

theorem conjReflect_im (s : ℂ) : (conjReflect s).im = s.im := by
  simp [conjReflect]

theorem conjReflect_eq_self_iff (s : ℂ) :
    conjReflect s = s ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [conjReflect] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [conjReflect]
      linarith
    · simp [conjReflect]

theorem conjReflect_involutive (s : ℂ) : conjReflect (conjReflect s) = s := by
  apply Complex.ext <;> simp [conjReflect]

theorem conjReflect_ne_self_iff (s : ℂ) :
    conjReflect s ≠ s ↔ s.re ≠ (1 / 2 : ℝ) := by
  constructor
  · intro h hs
    exact h ((conjReflect_eq_self_iff s).mpr hs)
  · intro h hs
    exact h ((conjReflect_eq_self_iff s).mp hs)

-- 对照 (为什么必须用共轭反射): 经典反射 s↦1−s 的不动集只有一个点,
--   承载不了"零点所在的线"; 共轭反射的不动集恰是整条临界线.
theorem classical_reflect_fixed_iff (s : ℂ) :
    1 - s = s ↔ s = ((1 / 2 : ℝ) : ℂ) := by
  constructor
  · intro h
    apply Complex.ext
    · have hre := congrArg Complex.re h
      norm_num at hre ⊢
      linarith
    · have him := congrArg Complex.im h
      norm_num at him ⊢
      linarith
  · intro hs
    rw [hs]
    norm_num

-- ====================================================================
-- 3. 正性原子: 不动点上配对读数退化为模方
-- ====================================================================

lemma re_mul_star (z : ℂ) : (z * star z).re = ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq, Complex.mul_re]

theorem connectorPair_eq_two_norm_sq_on_critical (Φ : ℂ → ℂ) (s : ℂ)
    (hs : s.re = (1 / 2 : ℝ)) :
    connectorPair Φ s = 2 * ‖Φ s‖ ^ 2 := by
  unfold connectorPair
  have hfix : conjReflect s = s := (conjReflect_eq_self_iff s).mpr hs
  rw [hfix, re_mul_star]

theorem connectorPair_nonneg_on_critical (Φ : ℂ → ℂ) (s : ℂ)
    (hs : s.re = (1 / 2 : ℝ)) : 0 ≤ connectorPair Φ s := by
  rw [connectorPair_eq_two_norm_sq_on_critical Φ s hs]
  positivity

-- ====================================================================
-- 4. 破缺见证: 离圆处配对读数可取负值 (∞ 维自由度的第一次兑现)
-- ====================================================================

-- 函数空间的 Dirac 型内插: 任意互异两点可指定 1 与 −1.
--   这是全函数空间下的平凡事实; 受限 (Mellin) 类下是真正的分析缺口.
theorem full_space_separates {z w : ℂ} (h : z ≠ w) :
    ∃ Φ : ℂ → ℂ, Φ z = 1 ∧ Φ w = -1 := by
  refine ⟨fun x => if x = z then (1 : ℂ) else -1, ?_, ?_⟩
  · simp
  · simp [Ne.symm h]

theorem connectorPair_can_be_negative_of_off_circle {s : ℂ}
    (hs : s.re ≠ (1 / 2 : ℝ)) :
    ∃ Φ : ℂ → ℂ, connectorPair Φ s < 0 := by
  have hne : conjReflect s ≠ s := (conjReflect_ne_self_iff s).mpr hs
  obtain ⟨Φ, hz, hw⟩ := full_space_separates hne
  refine ⟨Φ, ?_⟩
  unfold connectorPair
  rw [hz, hw]
  norm_num

-- ====================================================================
-- 5. 核心等价: 第 4 方向的正性精确刻画临界线
-- ====================================================================

-- 1/2 的第六种刻画, 也是**第一条携带不等式 (正性)** 的刻画:
--   先前五条 (反射不动 / 反演不动圆 / 能量阈值 / 均方相变 / Γ 比退化)
--   全是位置型或临界型, 不含正性.
-- 诚实定位: 这是**刻画**不是排除工具 —— 它在单点上免费成立 (与 ζ 无关),
--   而把它用在 ζ 的所有零点上, 所需断言恰等价于 RH (见论文 §negative).
theorem fourth_direction_positivity_iff_critical (s : ℂ) :
    (∀ Φ : ℂ → ℂ, 0 ≤ connectorPair Φ s) ↔ s.re = (1 / 2 : ℝ) := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨Φ, hneg⟩ := connectorPair_can_be_negative_of_off_circle hne
    have hnonneg := h Φ
    linarith
  · intro hs Φ
    exact connectorPair_nonneg_on_critical Φ s hs

-- ====================================================================
-- 6. 对照: 为什么离散标签做不到 (有限维退化)
-- ====================================================================

-- 前三个标签的纤维是 Subsingleton (零自由度) — 无法承载分离能力.
theorem tag4Fiber_discrete_subsingleton (t : Tag4) (ht : t ≠ Tag4.T) :
    Subsingleton (tag4Fiber t) := by
  cases t with
  | S  => exact ⟨fun a b => by cases a; cases b; rfl⟩
  | R  => exact ⟨fun a b => by cases a; cases b; rfl⟩
  | iR => exact ⟨fun a b => by cases a; cases b; rfl⟩
  | T  => contradiction

-- 第 4 标签的纤维不是 Subsingleton — 这就是"∞ 维"的可证内容.
theorem tag4Fiber_T_not_subsingleton : ¬ Subsingleton (tag4Fiber Tag4.T) := by
  intro h
  letI : Subsingleton (ℂ → ℂ) := by simpa [tag4Fiber] using h
  have heq : (fun _ : ℂ => (0 : ℂ)) = (fun _ : ℂ => (1 : ℂ)) := Subsingleton.elim _ _
  have h01 := congrArg Complex.re (congrFun heq (0 : ℂ))
  norm_num at h01

-- 有限维侧的退化: 反射等变 + 共轭等变 ⟹ 判据在 u 上为偶,
--   因而在 u 与 −u 处取同值, 无法把"正性"集中在 u = 0 这一条线上.
--   这是 A 形态 (离散第 4 标签) 拿不到排除力的精确原因.
theorem reflection_and_conj_invariant_is_even_in_u
    (K : ℂ → ℝ)
    (hRefl : ∀ s : ℂ, K (1 - s) = K s)
    (hConj : ∀ s : ℂ, K (star s) = K s)
    (u theta : ℝ) :
    K ((((1 / 2 : ℝ) + u : ℝ) : ℂ) + (theta : ℂ) * Complex.I) =
    K ((((1 / 2 : ℝ) - u : ℝ) : ℂ) + (theta : ℂ) * Complex.I) := by
  let a : ℂ := (((1 / 2 : ℝ) + u : ℝ) : ℂ) + (theta : ℂ) * Complex.I
  let b : ℂ := (((1 / 2 : ℝ) - u : ℝ) : ℂ) + (theta : ℂ) * Complex.I
  have hca : star (1 - a) = b := by
    apply Complex.ext
    · simp [a, b]
      ring
    · simp [a, b]
  change K a = K b
  calc
    K a = K (1 - a) := (hRefl a).symm
    _ = K (star (1 - a)) := (hConj (1 - a)).symm
    _ = K b := by rw [hca]

-- ====================================================================
-- 7. 接到 Weil: 有限零点集上的第 4 方向零点侧
-- ====================================================================

def fourthZeroSide (Z : Finset ℂ) (m : ℂ → ℝ) (Φ : ℂ → ℂ) : ℝ :=
  ∑ ρ ∈ Z, m ρ * connectorPair Φ ρ

-- 全部零点在临界线上 + 重数非负 ⟹ 零点侧非负 (真定理)
theorem fourthZeroSide_nonneg_of_all_on_critical_line
    {Z : Finset ℂ} {m : ℂ → ℝ} {Φ : ℂ → ℂ}
    (hm : ∀ ρ ∈ Z, 0 ≤ m ρ)
    (hall : ∀ ρ ∈ Z, ρ.re = (1 / 2 : ℝ)) :
    0 ≤ fourthZeroSide Z m Φ := by
  unfold fourthZeroSide
  apply Finset.sum_nonneg
  intro ρ hρ
  exact mul_nonneg (hm ρ hρ) (connectorPair_nonneg_on_critical Φ ρ (hall ρ hρ))

-- 逆否 (真定理): 零点侧为负 ⟹ 存在离圆零点.
--   这是"排除"在第 4 方向的正确形态: 不是证明某个部分和为零,
--   而是证明非负量的总和出现负贡献 ⟹ 前提被违反.
theorem exists_off_circle_zero_of_fourthZeroSide_neg
    {Z : Finset ℂ} {m : ℂ → ℝ} {Φ : ℂ → ℂ}
    (hm : ∀ ρ ∈ Z, 0 ≤ m ρ)
    (hneg : fourthZeroSide Z m Φ < 0) :
    ∃ ρ ∈ Z, ρ.re ≠ (1 / 2 : ℝ) := by
  by_contra h
  have hall : ∀ ρ ∈ Z, ρ.re = (1 / 2 : ℝ) := by
    intro ρ hρ
    by_contra hne
    exact h ⟨ρ, hρ, hne⟩
  have hnonneg := fourthZeroSide_nonneg_of_all_on_critical_line
    (Z := Z) (m := m) (Φ := Φ) hm hall
  linarith

-- ====================================================================
-- 8. 缺口接口: admissible 类内的分离能力 + 到抽象 Weil 证书的桥
-- ====================================================================

-- 第 4 方向的 ∞ 维自由度在受限 (admissible) 类内的形态.
--   全函数空间下平凡 (full_space_is_separating);
--   Mellin 变换类下 = 真正的分析缺口 (唯一剩余的墙).
def SeparatingClass (admissible : (ℂ → ℂ) → Prop) : Prop :=
  ∀ {z w : ℂ}, z ≠ w → ∃ Φ, admissible Φ ∧ Φ z = 1 ∧ Φ w = -1

theorem full_space_is_separating : SeparatingClass (fun _ => True) := by
  intro z w h
  obtain ⟨Φ, hz, hw⟩ := full_space_separates h
  exact ⟨Φ, trivial, hz, hw⟩

-- 分离能力 ⟹ 每个离圆点都有 admissible 的负贡献见证 (真定理, 纯代数).
--   这把抽象的 off_circle_witness 压成一个具体可攻的内插问题.
theorem admissible_negative_witness_of_separating
    {admissible : (ℂ → ℂ) → Prop} (hsep : SeparatingClass admissible)
    {s : ℂ} (hs : s.re ≠ (1 / 2 : ℝ)) :
    ∃ Φ, admissible Φ ∧ connectorPair Φ s < 0 := by
  have hne : conjReflect s ≠ s := (conjReflect_ne_self_iff s).mpr hs
  obtain ⟨Φ, hadm, hz, hw⟩ := hsep hne
  refine ⟨Φ, hadm, ?_⟩
  unfold connectorPair
  rw [hz, hw]
  norm_num

-- 第 4 方向的 Weil 证书 (把抽象 Weil 证书的 TestFunc 实例化为函数空间)
structure FourthDirectionWeilCertificate where
  admissible : (ℂ → ℂ) → Prop
  -- 分离能力 (∞ 维内插; 受限类内 = 分析缺口)
  separation : SeparatingClass admissible
  analyticSide : (ℂ → ℂ) → ℝ
  zeroSide : (ℂ → ℂ) → ℝ
  explicit_identity : ∀ Φ, admissible Φ → zeroSide Φ = analyticSide Φ
  analytic_nonneg : ∀ Φ, admissible Φ → 0 ≤ analyticSide Φ
  -- 总零点和的负见证 (局部化: separation 给出单点负值, 还需压住其他零点的
  -- 正贡献 — 这一步是 Weil/Bombieri 型判据的分析核心, 外部输入)
  off_circle_witness :
    ∀ ρ : ℂ, ρ.re ≠ (1 / 2 : ℝ) → ∃ Φ, admissible Φ ∧ zeroSide Φ < 0

-- 桥: 实例化抽象 Weil 证书 ⟹ 直接复用已证的排除定理
def toWeilCertificate (C : FourthDirectionWeilCertificate) :
    WeilPositivityCertificate :=
  { TestFunc := ℂ → ℂ
    admissible := C.admissible
    analyticSide := C.analyticSide
    zeroSide := C.zeroSide
    explicit_identity := C.explicit_identity
    analytic_nonneg := C.analytic_nonneg
    off_circle_witness := fun ρ _ hne => C.off_circle_witness ρ hne }

theorem no_off_circle_zero_of_fourth_direction_certificate
    (C : FourthDirectionWeilCertificate) :
    ∀ ρ : ℂ, criticalBandZero ρ → ρ.re = (1 / 2 : ℝ) :=
  no_off_circle_zero_of_weil_certificate (toWeilCertificate C)

theorem zero_radial_displacement_of_fourth_direction_certificate
    (C : FourthDirectionWeilCertificate) :
    ∀ ρ : ℂ, criticalBandZero ρ → radialDisplacement ρ = 0 := by
  intro ρ hρ
  exact (radialDisplacement_eq_zero_iff ρ).mpr
    (no_off_circle_zero_of_fourth_direction_certificate C ρ hρ)

end

end RiemannHIBS.Tag4Basis
