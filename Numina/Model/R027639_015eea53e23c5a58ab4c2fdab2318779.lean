import Mathlib

theorem algebra_95848 {x y : ℝ} (hx : x = 10000 * (1 - 20 / 100) * (1 - 20 / 100) * (1 - 10 / 100))
    (hy : y = 10000 * (1 - 40 / 100) * (1 - 5 / 100) * (1 - 5 / 100)) :
    x > y ∧ x - y = 345 := by
  rw [hx, hy]
  constructor
  · -- Show that the first discount strategy results in a larger amount
    norm_num
  · -- Show that the difference is exactly 345
    norm_num