import Mathlib

open BigOperators

theorem algebra_4966 {x y : ℝ} (h1 : (4 * x + 2 * y) / 8 - (8 * x - 4 * y) / 9 = 9) (h2 : (4 * x + 2 * y) / 6 - (8 * x - 4 * y) / 5 = 20) : y = 3 := by
  have eq1 : -28 * x + 50 * y = 648 := by
    linarith [h1]
  have eq2 : -28 * x + 34 * y = 600 := by
    linarith [h2]
  linarith [eq1, eq2]