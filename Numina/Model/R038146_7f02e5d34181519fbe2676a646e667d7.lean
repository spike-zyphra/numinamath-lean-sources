import Mathlib

theorem algebra_20064 : (Nat.floor (10^2007 * (1 / 7 : ℝ)) % 10) = 2 := by
  have h1 : Nat.floor (10^2007 * (1 / 7 : ℝ)) = (10^2007) / 7 := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num