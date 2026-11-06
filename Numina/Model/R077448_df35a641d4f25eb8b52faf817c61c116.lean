import Mathlib

theorem algebra_11909 : (Nat.floor (10^125 * (4 / 7 : ℝ)) % 10) = 2 := by
  have h1 : Nat.floor (10^125 * (4 / 7 : ℝ)) = (4 * 10^125) / 7 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num