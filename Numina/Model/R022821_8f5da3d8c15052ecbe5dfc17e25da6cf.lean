import Mathlib

theorem algebra_15178 : (Nat.floor ((10^99 * 13 / 90 : ℝ) * 10)) % 10 = 4 := by 
  have h1 : Nat.floor ((10^99 * 13 / 90 : ℝ) * 10) = (13 * 10 ^ 100 / 90 : ℕ) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num