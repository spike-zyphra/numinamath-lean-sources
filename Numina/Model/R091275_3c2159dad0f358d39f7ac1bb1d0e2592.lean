import Mathlib

theorem number_theory_16216 : (Nat.floor (10 ^ 43 * (1 / 13 : ℝ))) % 10 = 0 := by
  have h1 : Nat.floor (10 ^ 43 * (1 / 13 : ℝ)) = (10 ^ 43) / 13 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num