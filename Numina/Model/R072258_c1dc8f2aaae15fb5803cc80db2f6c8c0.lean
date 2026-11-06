import Mathlib

theorem algebra_321209 (x y : ℝ) :
    (x * y - 1) ^ 2 + (x + y - 2) * (x + y - 2 * x * y) = (x - 1) ^ 2 * (y - 1) ^ 2 := by
  ring