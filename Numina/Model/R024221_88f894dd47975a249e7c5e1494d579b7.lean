import Mathlib

theorem number_theory_238814 : (Nat.floor (10 ^ 2023 * (35 / 37 : ℝ))) % 10 = 9 := by
  have h1 : Nat.floor (10 ^ 2023 * (35 / 37 : ℝ)) = (35 * 10 ^ 2023) / 37 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num