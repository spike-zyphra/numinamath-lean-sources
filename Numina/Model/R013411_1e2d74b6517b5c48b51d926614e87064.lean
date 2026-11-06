import Mathlib

theorem algebra_13652 : (Nat.floor (10^92 * (5 / 33 : ℝ)) % 10) = 5 := by
  have h1 : (Nat.floor (10^92 * (5 / 33 : ℝ)) : ℕ) = (5 * 10^92 / 33 : ℕ) := by 
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num