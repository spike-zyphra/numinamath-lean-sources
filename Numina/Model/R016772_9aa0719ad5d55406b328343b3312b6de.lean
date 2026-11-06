import Mathlib

theorem algebra_9182
    {a : ℕ → ℤ}
    (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 2 * a n + 1) :
    ∀ n ≥ 1, a n = 2 ^ n - 1 := by 
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
      have h1 : a (n + 1) = 2 ^ (n + 1) - 1 := ih (by linarith) 
      have eq1 : a ((n + 1) + 1) = 2 * a (n + 1) + 1 := han (n + 1) (by linarith)
      rw [eq1] 
      rw [h1]
      simp [pow_add, pow_mul, mul_add]
      <;> ring