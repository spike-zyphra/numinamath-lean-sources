import Mathlib

theorem algebra_5639 {x y : ℝ} (h1 : (5 * x + 2 * y) / 7 + (5 * x - 2 * y) / 6 = 3)
    (h2 : (5 * x + 2 * y) / 2 - (5 * x - 2 * y) / 3 = 5) : x = 2 := by
  have eq1 : 6 * (5 * x + 2 * y) + 7 * (5 * x - 2 * y) = 126 := by 
    linarith [h1]
  have eq2 : 3 * (5 * x + 2 * y) - 2 * (5 * x - 2 * y) = 30 := by
    linarith [h2]
  linarith [eq1, eq2]