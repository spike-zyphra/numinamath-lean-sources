import Mathlib

theorem number_theory_191448 : (Nat.floor (10 ^ 2017 * (1 / 7 : ℝ))) % 10 + (Nat.floor (10 ^ 7102 * (1 / 7 : ℝ))) % 10 = 9 := by
  have h1 : Nat.floor (10 ^ 2017 * (1 / 7 : ℝ)) = (10 ^ 2017) / 7 := by
    norm_num [Nat.floor_eq_iff]
  have h2 : Nat.floor (10 ^ 7102 * (1 / 7 : ℝ)) = (10 ^ 7102) / 7 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1, h2]
  norm_num