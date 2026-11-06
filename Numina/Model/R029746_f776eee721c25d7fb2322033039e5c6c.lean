import Mathlib
theorem algebra_611151 (x y : ℝ) (h1 : x * y = 5) (h2 : x ^ 2 + y ^ 2 = 21) : x ^ 4 + y ^ 4 = 391:= by
  have h3 : x ^ 4 + y ^ 4 = (x^2 + y^2) ^ 2 - 2 * (x * y) ^ 2 := by
    ring
  rw [h3, h2, h1]
  norm_num