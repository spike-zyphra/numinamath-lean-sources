import Mathlib

theorem algebra_309774 (x y z : ℝ) (h1 : x + 2 * y - 5 * z = 3) (h2 : x - 2 * y - z = -5) :
    x ^ 2 + y ^ 2 + z ^ 2 ≥ 54 / 11 := by
  have h3 : x = 3 * z - 1 := by
    linarith [h1, h2]
  have h4 : y = z + 2 := by
    linarith [h1, h2]
  rw [h3, h4]
  nlinarith [sq_nonneg (z - 1 / 11)]