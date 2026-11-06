import Mathlib

theorem inequalities_126568 (x y z : ℝ) (h : x + 0.5 > y^2 + z^2) :
    x + y + z > -1 := by
  by_contra h1
  push_neg at h1
  have h2 : x ≤ -1 - y - z := by linarith
  have h3 : x + 0.5 ≤ (-1 - y - z) + 0.5 := by linarith [h2]
  have h4 : (-1 - y - z) + 0.5 ≤ y ^ 2 + z ^ 2 := by
    nlinarith [sq_nonneg (y + 0.5), sq_nonneg (z + 0.5), sq_nonneg (y - z)]
  have h5 : x + 0.5 ≤ y ^ 2 + z ^ 2 := by linarith [h3, h4]
  linarith [h, h5]