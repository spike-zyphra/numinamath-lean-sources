import Mathlib

theorem number_theory_52053 {n : ℕ} (hn : n > 2) :
    ¬Prime (Nat.ofDigits n [1, 0, 2, 0, 1]) := by
  have h1 : Nat.ofDigits n [1, 0, 2, 0, 1] = (n ^ 2 + 1) ^ 2 := by
    simp [Nat.ofDigits, mul_add, add_mul, pow_two, pow_succ]
    <;> ring
  rw [h1]
  apply not_prime_pow
  all_goals
    nlinarith [sq_pos_of_pos (show 0 < n by linarith), sq_nonneg (n : ℕ)]