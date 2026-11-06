import Mathlib

theorem algebra_58854 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : x ^ 2 - y = (z - 1) ^ 2) (h2 : y ^ 2 - z = (x - 1) ^ 2) (h3 : z ^ 2 - x = (y - 1) ^ 2) :
    (x, y, z) = (1, 1, 1) := by
  have h4 : x = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      h1, h2, h3]
  have h5 : y = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      h1, h2, h3]
  have h6 : z = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
      h1, h2, h3]
  simp [Prod.ext_iff, h4, h5, h6]
  all_goals nlinarith