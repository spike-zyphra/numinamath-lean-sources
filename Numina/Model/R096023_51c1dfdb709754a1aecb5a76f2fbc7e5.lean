import Mathlib

theorem number_theory_11037 : (Nat.floor (100 * (3 / 11 : ℝ)) % 10) + (Nat.floor (1000 * (3 / 11 : ℝ)) % 10) = 9 := by
  have h1 : Nat.floor (100 * (3 / 11 : ℝ)) = 27 := by
    norm_num [Nat.floor_eq_iff]
  have h2 : Nat.floor (1000 * (3 / 11 : ℝ)) = 272 := by
    norm_num [Nat.floor_eq_iff]
  calc
    (Nat.floor (100 * (3 / 11 : ℝ)) % 10) + (Nat.floor (1000 * (3 / 11 : ℝ)) % 10) = (27 % 10) + (272 % 10) := by rw [h1, h2]
    _ = 7 + 2 := by norm_num
  all_goals norm_num