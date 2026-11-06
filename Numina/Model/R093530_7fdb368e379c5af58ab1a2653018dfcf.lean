import Mathlib

theorem number_theory_15970 : (Nat.floor (10^308 * (12 / 37 : ℝ))) % 10 = 2 := by
  have h1 : Nat.floor (10 ^ 308 * (12 / 37 : ℝ)) = (12 * 10 ^ 308) / 37 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num