-- RiemannHIBS.FinSum — core Lean 无 Finset/∑, 用结构归纳求和代替
-- (模式来自 lean4-formalization skill 的参考库, 在 v4.28.0 下验证)

def finSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => finSum n (fun i : Fin n => f (Fin.castSucc i)) + f (Fin.last n)

theorem finSum_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [finSum, ih (fun i => h (Fin.castSucc i)), h (Fin.last n)]

theorem finSum_add {n : Nat} (f g : Fin n → Int) :
    finSum n (fun i => f i + g i) = finSum n f + finSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [finSum, ih, Int.add_assoc, Int.add_left_comm, Int.add_comm]

theorem finSum_sub {n : Nat} (f g : Fin n → Int) :
    finSum n (fun i => f i - g i) = finSum n f - finSum n g := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
      simp [finSum, ih]
      omega

theorem finSum_neg {n : Nat} (f : Fin n → Int) :
    finSum n (fun i => -f i) = -finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
      simp [finSum, ih]
      omega

theorem finSum_mul_const {n : Nat} (f : Fin n → Int) (k : Int) :
    finSum n (fun i => k * f i) = k * finSum n f := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
      simp [finSum, ih, Int.mul_add]

theorem finSum_const_mul {n : Nat} (f : Fin n → Int) (k : Int) :
    finSum n (fun i => f i * k) = finSum n f * k := by
  induction n with
  | zero => simp [finSum]
  | succ n ih =>
      simp [finSum, ih, Int.add_mul]

theorem finSum_succ (n : Nat) (f : Fin (n + 1) → Int) :
    finSum (n + 1) f = finSum n (fun i : Fin n => f (Fin.castSucc i)) + f (Fin.last n) := rfl

-- Fin 辅助事实 (core 不含 castSucc 单射)
theorem castSucc_inj {n : Nat} {a b : Fin n} (h : Fin.castSucc a = Fin.castSucc b) : a = b := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  simpa using hv

theorem castSucc_ne_last {n : Nat} (i : Fin n) : Fin.castSucc i ≠ Fin.last n := by
  intro h
  have hlt := Fin.castSucc_lt_last i
  rw [h] at hlt
  exact Nat.lt_irrefl _ hlt
