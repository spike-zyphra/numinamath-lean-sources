import Mathlib

theorem number_theory_42504 : (Nat.floor ((3^123 : ℚ) / 5)) % 16 = 5 := by
  have h1 : Nat.floor ((3^123 : ℚ) / 5) = (3 ^ 123 - 2) / 5 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num