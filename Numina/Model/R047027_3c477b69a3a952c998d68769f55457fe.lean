import Mathlib

theorem algebra_146581 {a : ℕ → ℤ} (ha1 : a 1 = 3) (han : ∀ n ≥ 1, a (n + 1) = 2 * a n - 1) :
    ∀ n ≥ 1, a n = 2 ^ n + 1 := by 
  intro n hn 
  induction n with 
  | zero => 
    exfalso 
    linarith
  | succ n ih =>
    cases n with 
    | zero =>
      rw [ha1]
      all_goals norm_num 
    | succ n => 
      have h1 : a (n + 2) = 2 * a (n + 1) - 1 := by 
        specialize han (n + 1) (by linarith) 
        simpa using han 
      rw [h1] 
      rw [ih (by linarith)] 
      simp [pow_add, pow_mul, mul_add, sub_eq_add_neg]
      <;> ring