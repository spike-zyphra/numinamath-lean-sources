import Mathlib

theorem algebra_21456 {x y z : ℝ} (h1 : 3 * x + 4 * y - 12 * z = 10) (h2 : -2 * x - 3 * y + 9 * z = -4) :
    x = 14 := by
  have eq1 : 9 * x + 12 * y - 36 * z = 30 := by 
    linarith [h1]
  have eq2 : -8 * x - 12 * y + 36 * z = -16 := by
    linarith [h2]
  linarith [eq1, eq2]