import Mathlib

theorem algebra_25935 (x y z : ℝ)
    (h1 : x - y + z - 1 = 0)
    (h2 : x * y + 2 * z ^ 2 - 6 * z + 1 = 0) :
    (x - 1) ^ 2 + (y + 1) ^ 2 ≤ 11 := by 
  have hy : y = x + z - 1 := by
    linarith
  rw [hy] at h2
  nlinarith [sq_nonneg (x - z - 2), sq_nonneg (z - 2), sq_nonneg (x - 2), 
          sq_nonneg (y - 2), sq_nonneg (x - 1), sq_nonneg (z - 1), sq_nonneg (x - 2), 
          sq_nonneg (x - z), sq_nonneg (x - (z)), sq_nonneg (x + z - 2)]