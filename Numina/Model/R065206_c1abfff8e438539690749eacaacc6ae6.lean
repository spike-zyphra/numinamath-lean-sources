import Mathlib

theorem algebra_322609 (x y z : ℝ) (h1 : x - y = 8) (h2 : x * y + z ^ 2 = -16) :
    x + y + z = 0 := by
  have h4 : x * y = -16 - z ^ 2 := by linarith
  have h3 : (x + y) ^ 2 = -4 * z ^ 2 := by
    nlinarith [sq_nonneg (x - y), h1, h4]
  have h5 : (x + y) ^ 2 ≥ 0 := by nlinarith
  have h6 : z ^ 2 ≥ 0 := by nlinarith
  have h7 : (x + y) ^ 2 = 0 := by nlinarith
  have h8 : x + y = 0 := by
    nlinarith
  have h9 : z ^ 2 = 0 := by
    nlinarith
  have h10 : z = 0 := by
    nlinarith
  linarith [h8, h10]