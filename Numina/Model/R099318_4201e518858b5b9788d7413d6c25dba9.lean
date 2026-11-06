import Mathlib

theorem algebra_301707 {a : ℕ → ℤ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = 2 * a n + n ^ 2 * (1 + 3 ^ n)) :
    ∀ n ≥ 1, a n = -23 * 2 ^ (n - 1) + 3 ^ n * (n ^ 2 - 6 * n + 15) -
      n ^ 2 - 2 * n - 3 := by
  intro n hn
  induction n with
  | zero => 
    exfalso
    exact Nat.lt_irrefl 0 hn
  | succ n ih =>
    cases n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      simp [han (n + 1) (by linarith), ih (by linarith)]
      all_goals
        norm_num [pow_succ, mul_add, add_mul, sub_eq_add_neg]
        <;> ring_nf <;> omega