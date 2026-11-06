import Mathlib

theorem number_theory_280273 : (Nat.floor (10^123 * (1 / 7 : ℝ)) % 10) = 2 := by
  have h1 : Nat.floor (10^123 * (1 / 7 : ℝ)) = (10^123) / 7 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num