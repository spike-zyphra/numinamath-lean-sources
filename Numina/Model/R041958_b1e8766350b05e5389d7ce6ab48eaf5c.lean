import Mathlib

theorem algebra_16801 (x : ℝ) (hx : x = 1 / 7 + 1 / 3) : ⌊10 ^ 20 * x⌋₊ % 10 = 7 := by
  have h1 : x = (10 / 21 : ℝ) := by
    rw [hx]
    norm_num
  rw [h1]
  have h2 : ⌊(10 ^ 20 * (10 / 21 : ℝ))⌋₊ = 47619047619047619047 := by
    norm_num [Nat.floor_eq_iff]
  rw [h2]
  all_goals norm_num