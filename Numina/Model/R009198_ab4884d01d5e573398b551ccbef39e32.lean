import Mathlib

theorem algebra_15741 {x y z : ℝ} (h1 : (x + y + z) * (x * y + x * z + y * z) = 18) (h2 : x ^ 2 * (y + z) + y ^ 2 * (x + z) + z ^ 2 * (x + y) = 6) :
    x * y * z = 4 := by
  have eq2 : (x + y + z) * (x * y + x * z + y * z) - 3 * (x * y * z) = 6 := by
    nlinarith [h2]
  linarith [h1, eq2]