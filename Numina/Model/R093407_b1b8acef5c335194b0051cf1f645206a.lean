import Mathlib

theorem number_theory_134042 : (Nat.floor (10 ^ 2015 * (3 / 7 : ℝ)) % 10) = 7 := by
  have h1 : Nat.floor (10 ^ 2015 * (3 / 7 : ℝ)) = (3 * 10 ^ 2015) / 7 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num