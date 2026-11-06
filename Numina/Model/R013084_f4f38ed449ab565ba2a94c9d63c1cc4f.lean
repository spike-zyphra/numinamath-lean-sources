import Mathlib

theorem algebra_143995 {x y : ℝ} (h1 : x * (x + 1) * (3 * x + 5 * y) = 144) (h2 : x ^ 2 + 4 * x + 5 * y = 24) :
    (x, y) = (-4, 24 / 5) ∨ (x, y) = (3, 3 / 5) := by
  have eq1 : 5 * y = 24 - x ^ 2 - 4 * x := by linarith
  have eq2 : 3 * x + 5 * y = -x^2 - x + 24 := by
    have h3 : 5 * y = 24 - x ^ 2 - 4 * x := by linarith
    nlinarith
  rw [eq2] at h1
  have h3 : (x - 3) ^ 2 * (x + 4) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x ^ 2 + x - 12), sq_nonneg (x - 3), sq_nonneg (x + 4), sq_nonneg (x * (x + 4)), sq_nonneg ((x - 3) * (x + 4))]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case where (x - 3) ^ 2 = 0
    have hx : x = 3 := by
      nlinarith
    have hy : y = 3 / 5 := by
      nlinarith [eq1]
    right
    exact Prod.ext hx hy
  · -- Case where (x + 4) ^ 2 = 0
    have hx : x = -4 := by
      nlinarith
    have hy : y = 24 / 5 := by
      nlinarith [eq1]
    left
    exact Prod.ext hx hy