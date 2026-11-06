import Mathlib

theorem algebra_2250 (m n k : ℝ) (h1 : m * 2 - n * (-1) - (-3) = 7) (h2 : 2 * n * 2 - 3 * (-1) - 2 * m * (-3) = 5)
    (h3 : 2 + (-1) + (-3) = k) : m ^ 2 - 7 * n + 3 * k = 113 := by
  have eq1 : 2 * m + n = 4 := by 
    linarith
  have eq2 : 6 * m + 4 * n = 2 := by
    linarith
  have h4 : m = 7 := by 
    linarith [eq1, eq2]
  have h5 : n = -10 := by 
    linarith [eq1, h4]
  have h6 : k = -2 := by 
    linarith
  rw [h4, h5, h6]
  norm_num