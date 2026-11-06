import Mathlib

theorem number_theory_188683 : (Nat.floor ((10 ^ 2040 / (10 ^ 60 - 3)) : ℝ)) % 100 = 23 := by
  have h1 : Nat.floor ((10 ^ 2040 / (10 ^ 60 - 3)) : ℝ) = (10 ^ 2040 / (10 ^ 60 - 3) ) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num