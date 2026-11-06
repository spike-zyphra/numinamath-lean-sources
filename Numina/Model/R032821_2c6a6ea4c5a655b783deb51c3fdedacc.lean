import Mathlib

theorem number_theory_239543 : (Nat.floor (10^2008 * (1 / 41 : ℝ))) % 10 = 4 := by
  have h1 : Nat.floor (10^2008 * (1 / 41 : ℝ)) = (10 ^ 2008) / 41 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num