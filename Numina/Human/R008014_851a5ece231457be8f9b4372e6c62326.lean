import Mathlib

theorem algebra_13796 {x y : ℝ} (h1 : 2 * x + y = 4) (h2 : x + 2 * y = 5) :
    5 * x ^ 2 + 8 * x * y + 5 * y ^ 2 = 41 := by
  have h3 : (2 * x + y) ^ 2 + (x + 2 * y) ^ 2 = 41 := by
    rw [h1, h2]
    norm_num
  linarith