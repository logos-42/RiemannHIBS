-- RiemannHIBS.Euler — 欧拉乘积: ζ 与质数的隐数桥
-- 经典恒等式: ζ(s) = ∏_p (1 − p^(−s))^(−1) = ∏_p Σ_e p^(−es)
-- 有限骨架 (整数模型): ∏_p (1 + p + p² + ... + p^e) = Σ_{p^i q^j} p^i q^j
--   "所有质数相乘, 生成所有整数"
-- 隐数视角:
--   几何因子 = S 支聚合 (加法流), 因子相乘 = R 支投影 (乘法流 A2b),
--   网格求和 = S 支聚合 (加法流 A2a);
--   隐桥定理: 两者在可观测切片 ℂ 上相等.

import RiemannHIBS.Hidden
import RiemannHIBS.FinSum

open Tag

-- 几何级数因子: geom p e = 1 + p + p² + ... + p^e
def geom (p : Int) (e : Nat) : Int :=
  finSum (e + 1) (fun i : Fin (e + 1) => p ^ i.val)

-- 双素数 {p, q} 生成的整数 (光滑数) 上的 ζ 部分和
def smoothSum (p q : Int) (a b : Nat) : Int :=
  finSum (a + 1) (fun i : Fin (a + 1) => finSum (b + 1) (fun j : Fin (b + 1) => p ^ i.val * q ^ j.val))

-- ============ 隐数版本的几何因子与网格和 ============

-- 几何因子作为隐数: 各项是 R 支 (乘方 = 乘法), 求和流回 S 支
def geomH (p : Int) : (e : Nat) → S
  | 0 => hiddenReal 1
  | e + 1 => hAdd (geomH p e) (hiddenProj (p ^ (e + 1)))

-- 隐数网格和: 逐项 hAdd
def hFinSum : (n : Nat) → (Fin n → S) → S
  | 0, _ => ⟨0, Tag.S⟩
  | n + 1, f => hAdd (hFinSum n (fun i : Fin n => f (Fin.castSucc i))) (f (Fin.last n))

-- p, q 生成的整数上的隐数 ζ 和
def smoothH (p q : Int) (a b : Nat) : S :=
  hFinSum (a + 1)
    (fun i : Fin (a + 1) => hFinSum (b + 1) (fun j : Fin (b + 1) => hiddenProj (p ^ i.val * q ^ j.val)))

-- ============ 流定理 ============

theorem geomH_tag_S (p : Int) (e : Nat) : (geomH p e).tag = Tag.S := by
  induction e with
  | zero => rfl
  | succ e ih => simp [geomH, hAdd]

theorem hFinSum_tag_S : ∀ n : Nat, ∀ f : Fin n → S, (hFinSum n f).tag = Tag.S
  | 0, _ => rfl
  | n + 1, f => by
      simp [hFinSum, hAdd]

theorem smoothH_tag_S (p q : Int) (a b : Nat) : (smoothH p q a b).tag = Tag.S := by
  unfold smoothH
  apply hFinSum_tag_S

-- 欧拉乘积 (两因子相乘): 乘法强制流向 R 支 (A2b)
theorem euler_product_tag_R (p q : Int) (a b : Nat) :
    (hMul (geomH p a) (geomH q b)).tag = Tag.R := rfl

-- ============ 值定理 ============

theorem geom_succ (p : Int) (e : Nat) : geom p (e + 1) = geom p e + p ^ (e + 1) := by
  simp [geom, finSum_succ]

theorem geomH_val (p : Int) (e : Nat) : (geomH p e).val = geom p e := by
  induction e with
  | zero => simp [geomH, geom, hiddenReal, finSum]
  | succ e ih =>
      simp [geomH, hAdd, hiddenProj, ih, geom_succ]

theorem hFinSum_val : ∀ n : Nat, ∀ f : Fin n → S,
    (hFinSum n f).val = finSum n (fun i : Fin n => (f i).val)
  | 0, _ => rfl
  | n + 1, f => by
      simp [hFinSum, hAdd, finSum_succ, hFinSum_val]

theorem smoothH_val (p q : Int) (a b : Nat) : (smoothH p q a b).val = smoothSum p q a b := by
  unfold smoothH smoothSum
  rw [hFinSum_val]
  apply finSum_congr
  intro i
  rw [hFinSum_val]
  apply finSum_congr
  intro j
  rfl

-- ============ 核心: 欧拉乘积展开 (生成定理) ============

-- ∏_p (1 + p + ... + p^a) = Σ_{p^i q^j} p^i q^j, 对任意 p, q, a, b
theorem euler_product_expansion (p q : Int) (a b : Nat) :
    smoothSum p q a b = geom p a * geom q b := by
  unfold smoothSum
  have hinner : ∀ i : Fin (a + 1),
      finSum (b + 1) (fun j : Fin (b + 1) => p ^ i.val * q ^ j.val) = p ^ i.val * geom q b := by
    intro i
    simpa [geom, Int.mul_comm, Int.mul_assoc, Int.mul_left_comm] using
      finSum_const_mul (fun j : Fin (b + 1) => q ^ j.val) (p ^ i.val)
  rw [finSum_congr hinner]
  simpa [geom] using
    finSum_const_mul (fun i : Fin (a + 1) => p ^ i.val) (geom q b)

-- ============ 隐桥定理 ============

-- 欧拉乘积 (R 支, 乘法流) 与 ζ 部分和 (S 支, 加法流)
-- 在可观测切片 ℂ 上给出同一值: π(∏_p Σ_e p^e) = π(Σ_{生成数})
theorem euler_zeta_observable_bridge (p q : Int) (a b : Nat) :
    π (hMul (geomH p a) (geomH q b)) = π (smoothH p q a b) := by
  apply ℂ_ext
  · simp [π, hMul, smoothH_tag_S, geomH_val, smoothH_val, euler_product_expansion]
  · rfl
