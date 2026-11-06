import Mathlib

theorem number_theory_23064 : (Nat.floor (10 ^ 4037 * (1 / 17 : ℝ)) % 10) = 2 := by
  have h1 : Nat.floor (10 ^ 4037 * (1 / 17 : ℝ)) = (10 ^ 4037 / 17 : ℕ) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num