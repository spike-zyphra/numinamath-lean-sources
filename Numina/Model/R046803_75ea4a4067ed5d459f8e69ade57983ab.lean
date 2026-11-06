import Mathlib

theorem number_theory_235514 : ¬Prime (200^2 - 399) := by
  have h1 : (200^2 - 399 : ℕ) = 199^2 := by
    norm_num
  rw [h1]
  apply not_prime_pow
  all_goals norm_num