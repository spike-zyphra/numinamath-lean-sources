import Mathlib

theorem algebra_243070 {x y z : ℝ} (h1 : x + y + 2 + 4 * x * y = 0) (h2 : y + z + 2 + 4 * y * z = 0)
    (h3 : z + x + 2 + 4 * z * x = 0) :
    False := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (z + 1 / 2),
          sq_nonneg (x + y + z), sq_nonneg (x * y * z)]