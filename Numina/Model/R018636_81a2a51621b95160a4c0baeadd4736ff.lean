import Mathlib

theorem number_theory_206274 : ¬Prime (100^2 + 201) := by
  have h1 : (100 ^ 2 + 201 : ℕ) = 101 ^ 2 := by
    norm_num
  rw [h1]
  apply not_prime_pow
  all_goals norm_num