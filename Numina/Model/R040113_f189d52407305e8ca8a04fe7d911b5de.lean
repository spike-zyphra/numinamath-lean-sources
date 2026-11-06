import Mathlib
theorem algebra_605741 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : x ^ 2 - y = (z - 1) ^ 2) (h2 : y ^ 2 - z = (x - 1) ^ 2) (h3 : z ^ 2 - x = (y - 1) ^ 2) :
    (x, y, z) = (1, 1, 1) := by
  have h4 : x + y + z = 3 := by
    nlinarith [h1, h2, h3]

  have h5 : x = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]

  have h6 : y = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]

  have h7 : z = 1 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]

  simp [h5, h6, h7]