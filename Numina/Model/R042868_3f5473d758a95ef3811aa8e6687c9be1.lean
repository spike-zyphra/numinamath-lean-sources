import Mathlib

theorem algebra_10611 {x y : ℝ} (h1 : 3 * x + y = 10) (h2 : x + 3 * y = 14) :
    10 * x ^ 2 + 12 * x * y + 10 * y ^ 2 = 296 := by
  have h3 : x = 2 := by
    linarith
  have h4 : y = 4 := by
    linarith [h1, h3]
  rw [h3, h4]
  norm_num