-- RiemannHIBS.Envelope — 隐数包络 (Hidden Envelope): 把"隐数平面 + 标签分支"卷成壳
--
-- 研究动机 (用户提问): 隐数能否做出一个"包络结构", 把整个曲面找出来?
--   复平面是一维 (可观测切片 ℂ), 隐数平面是第二维 (val : Int), 标签分支是第三维 (S/R/iR),
--   引数 s 是沿 ℂ 的第四方向. 隐数空间 S = ℤ×{S,R,iR} 已是离散的三维格点.
--   投影 π (或 hEval) 非单射 (π_nonInjective 已证) ⟹ S 是 ℂ 上的一个三叶覆盖 (3-sheeted cover),
--   其影像正是 ℝ (实轴, S/R 两叶) 与 iℝ (虚轴, iR 一叶): 这就是包络的离散胚胎.
--
-- 本模块 (core, 无 mathlib): 在已有 Hidden 之上正式定义"包络"并证明:
--   1. 三叶壳的投影分层 (each sheet lands on its axis)
--   2. 非单射投影 = 包络的"折叠" (fold)
--   3. 双分量嵌入 ι' 把每个复格点提升回包络 (局部截面, π'∘ι'=id)
--   4. 临界线截面 criticalSection: 把倍化临界线 1+2it 嵌入为包络上的一维截面
--   5. 衔接 Zeta.lean 的 η/ζ 桥 与 Euler.lean 的隐桥 (包络在可观测切片上一致)
--
-- 连续化 (val : ℤ → ℝ, 真正的微分几何曲面) 见 EnvelopeC.lean (mathlib 版).

import RiemannHIBS.Hidden
import RiemannHIBS.Zeta
import RiemannHIBS.Euler
import RiemannHIBS.Riemann

open Tag

-- ====================================================================
-- 0. 包络的总空间: 就是隐数空间 S = ℤ × {S,R,iR}
-- ====================================================================

-- 包络 = 隐数空间本身. 称其为"包络"以强调其几何角色:
--   总空间 E (total space) = S, 基空间 B (base) = ℂ, 投影 = π.
--   (指标 n / 引数 s 是沿 B 的第四方向, 由 Zeta.lean 的 w : Nat→Int 承载.)
abbrev Envelope := Hidden

-- 包络的投影 (与 Hidden.π 同): 把三叶壳压回可观测复平面
def envelopeProj (e : Envelope) : ℂ := π e

-- 包络的显式构造器 (复用 Hidden 的三个分支)
def envS (a : Int) : Envelope := hiddenReal a      -- S 叶 (加法封闭支)
def envR (a : Int) : Envelope := ι_R a             -- R 叶 (乘法投影支, A2b)
def envI (b : Int) : Envelope := hiddenImag b      -- iR 叶 (开方投影支, A3)

-- ====================================================================
-- 1. 三叶壳的投影分层: 每片叶子落在自己的轴上
-- ====================================================================

-- S 叶投影到正实轴
theorem sheet_S_on_real (a : Int) : envelopeProj (envS a) = ℂ.mk a 0 := by
  simp [envelopeProj, π, envS, hiddenReal]

-- R 叶投影到正实轴 (注意 A2b 值不变, 仅标签变; 这里 π 对 R 取正实轴,
--   与 Analytic.lean 的 hEval(R↦−x) 区分 — 见 §6 讨论)
theorem sheet_R_on_real (a : Int) : envelopeProj (envR a) = ℂ.mk a 0 := by
  simp [envelopeProj, π, envR, ι_R]

-- iR 叶投影到虚轴
theorem sheet_iR_on_imag (b : Int) : envelopeProj (envI b) = ℂ.mk 0 b := by
  simp [envelopeProj, π, envI, hiddenImag]

-- 包络对 ℂ 的覆盖: 任意可观测点 ⟨x,0⟩ 至少有 S 叶与 R 叶两条原像,
--   ⟨0,y⟩ 至少有 iR 叶一条原像. 这正是"壳包住平面"的离散说法.
theorem envelope_covers_real (x : Int) :
    ∃ e₁ e₂ : Envelope, e₁ ≠ e₂ ∧ envelopeProj e₁ = ℂ.mk x 0 ∧ envelopeProj e₂ = ℂ.mk x 0 := by
  refine ⟨envS x, envR x, ?_, ?_⟩
  · intro h
    have ht := congrArg (fun e : Envelope => e.tag) h
    simp [envS, envR, hiddenReal, ι_R] at ht
  · simp [envelopeProj, π, envS, envR, hiddenReal, ι_R]

theorem envelope_covers_imag (y : Int) :
    ∃ e : Envelope, envelopeProj e = ℂ.mk 0 y := by
  refine ⟨envI y, ?_⟩
  simp [envelopeProj, π, envI, hiddenImag]

-- ====================================================================
-- 2. 折叠 (fold): 非单射投影 = 包络的"自交/重叠"
-- ====================================================================

-- 这正是 Hidden.π_nonInjective 的包络重述: 同一可观测值来自不同标签叶.
theorem envelope_fold : ∃ a b : Envelope, a ≠ b ∧ envelopeProj a = envelopeProj b :=
  π_nonInjective

-- 折叠的具体见证: ⟨3,S⟩ 与 ⟨3,R⟩ 在实轴上重叠
theorem envelope_fold_witness :
    envS 3 ≠ envR 3 ∧ envelopeProj (envS 3) = envelopeProj (envR 3) := by
  constructor
  · intro h
    have ht := congrArg (fun e : Envelope => e.tag) h
    simp [envS, envR, hiddenReal, ι_R] at ht
  · simp [envelopeProj, π, envS, envR, hiddenReal, ι_R]

-- ====================================================================
-- 3. 局部截面 (local section): 双分量嵌入把复格点提升回包络
-- ====================================================================

-- 复用 Riemann.lean 的 doubledEmbedding / CompositeHidden 思路,
-- 这里给出更一般的"复格点提升": (a,b) ↦ ⟨⟨a,S⟩, ⟨b,iR⟩⟩ (即 Hidden.ι' 的双分量)
def liftPoint (a b : Int) : CompositeHidden := ⟨envS a, envI b⟩

-- 投影回去恢复原点 (π'∘ι'=id 的包络版, 见 Riemann.lean doubledEmbedding_observable)
theorem liftPoint_section (a b : Int) :
    π' (liftPoint a b) = ℂ.mk a b := by
  simp [liftPoint, π', envS, envI, hiddenReal, hiddenImag]

-- 单分量提升 (只需实轴): 任意实点可经 S 叶提升
theorem lift_real_is_section (x : Int) : envelopeProj (envS x) = ℂ.mk x 0 :=
  sheet_S_on_real x

-- ====================================================================
-- 4. 临界线截面 (critical section): 把倍化临界线 1+2it 嵌入包络
-- ====================================================================

-- 倍化临界线 2s = 1+2it 在包络上的截面:
--   实部 1 走 S 叶, 虚部 2t 走 iR 叶 (复用 Riemann.doubledEmbedding 的构造).
def criticalSection (t : Int) : CompositeHidden := doubledEmbedding t

-- 截面的投影确实在倍化临界线上 (Re = 1)
theorem criticalSection_on_line (t : Int) :
    criticalLineDoubled (π' (criticalSection t)) := by
  simp [criticalSection, doubledEmbedding, π', hiddenReal, hiddenImag, criticalLineDoubled]

-- 截面的可观测值 = 1 + 2t·i
theorem criticalSection_observable (t : Int) :
    π' (criticalSection t) = ℂ.mk 1 (2 * t) := by
  simp [criticalSection, doubledEmbedding, π', hiddenReal, hiddenImag]

-- ====================================================================
-- 5. 衔接 ζ/η 桥 与 欧拉隐桥: 包络在可观测切片上一致
-- ====================================================================

-- Zeta.lean 的 ζ 部分和留在 S 叶, 投影到实轴之和 — 包络视角:
--   ζ 部分和作为 S 叶上的纤维, 投影后给出可观测实部值.
theorem zetaSum_fiber_in_envelope (w : Nat → Int) (N : Nat) :
    (zetaSum w N).tag = Tag.S := zetaSum_tag_S w N

theorem zetaSum_fiber_proj (w : Nat → Int) (N : Nat) :
    envelopeProj (zetaSum w N) = ℂ.mk (zetaSum w N).val 0 := by
  rw [envelopeProj, π, zetaSum_tag_S w N]

-- η 部分和同样在 S 叶
theorem etaSum_fiber_in_envelope (w : Nat → Int) (N : Nat) :
    (etaSum w N).tag = Tag.S := etaSum_tag_S w N

-- 欧拉隐桥的包络表述: 欧拉乘积 (R 叶, 乘法流) 与 网格和 (S 叶, 加法流)
--   投影到同一可观测值 — 包络的两叶在基空间"汇合"于同一点.
theorem euler_bridge_in_envelope (p q : Int) (a b : Nat) :
    envelopeProj (hMul (geomH p a) (geomH q b)) =
    envelopeProj (smoothH p q a b) := by
  exact euler_zeta_observable_bridge p q a b

-- ====================================================================
-- 6. 与 Analytic.lean 的 hEval 投影的对照 (A2b 符号约定)
-- ====================================================================

-- RiemannHIBS.Hidden 的 π 对 R 叶取正实轴; Analytic.lean 的 hEval 对 R 叶取 −x.
-- 两者是同一包络的两种"读数" (read-out), 差别正是 A2b 的符号携带信息:
--   在包络里 R 叶与 S 叶本就不同 (标签不同), 投影符号只是把标签信息压进实轴方向.
-- 下面是 π 与 hEval 风格的对照 (用本模块的 π 语义):
theorem proj_vs_hEval_note (a : Int) :
    envelopeProj (envR a) = ℂ.mk a 0 := sheet_R_on_real a

-- (连续化后, 见 EnvelopeC.lean: hEval 的 R↦−x 会显式出现,
--  那时包络的三叶壳在 ℂ 上呈现为: S 叶→正实轴, R 叶→负实轴, iR 叶→虚轴,
--  形成真正的三维实流形 E ⊆ ℝ³ 包住 ℂ.)
