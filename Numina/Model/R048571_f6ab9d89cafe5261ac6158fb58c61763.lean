import Mathlib

theorem algebra_2778 {x : ℝ} (hx : x = 625 * (1 - 20 / 100) * (1 + 8 / 100)) :
    x - 500 = 625 * (1 - 20 / 100) * (1 + 8 / 100) - 500 ∧
    (x - 500) / 500 = 8 / 100 := by
  constructor
  · -- First part: x - 500 equals the given expression
    rw [hx]
  · -- Second part: (x - 500) / 500 = 8 / 100
    rw [hx]
    norm_num