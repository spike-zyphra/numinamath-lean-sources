import Mathlib

theorem algebra_2425 {x y : ℝ} (h : 3 * x ^ 2 + 4 * y - 10 = 0) :
    15 * x ^ 3 + 3 * x ^ 2 * y + 20 * x * y + 4 * y ^ 2 + 3 * x ^ 2 - 50 * x - 6 * y = 10 := by
  have h1 : 3 * x ^ 2 + 4 * y = 10 := by linarith
  have h2 : 15 * x ^ 3 + 3 * x ^ 2 * y + 20 * x * y + 4 * y ^ 2 = (3 * x ^ 2 + 4 * y) * (5 * x + y) := by
    ring
  have h3 : 15 * x ^ 3 + 3 * x ^ 2 * y + 20 * x * y + 4 * y ^ 2 + 3 * x ^ 2 - 50 * x - 6 * y =
      (3 * x ^ 2 + 4 * y) * (5 * x + y) + 3 * x ^ 2 - 50 * x - 6 * y := by
    rw [h2]
  rw [h3]
  rw [h1]
  nlinarith [sq_nonneg (x * 5 + y * 3), sq_nonneg (x * 2 - 10), sq_nonneg (y - 10 / 3), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2)]