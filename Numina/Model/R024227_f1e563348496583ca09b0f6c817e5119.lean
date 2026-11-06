import Mathlib

theorem number_theory_23140 : (Nat.floor ((123 / 999 : ℝ) * 10 ^ 123999)) % 10 = 3 := by
  have h1 : Nat.floor ((123 / 999 : ℝ) * 10 ^ 123999) = (123 * 10 ^ 123999) / 999 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num