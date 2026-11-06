import Mathlib

theorem algebra_250203 {x y : ℝ} (h : (2 * x + y)^3 + x^3 + 3 * x + y = 0) : 3 * x + y = 0 := by
  have h1 : (3 * x + y) * ((3 * x + y) ^ 2 - 3 * x * (3 * x + y) + 3 * x ^ 2 + 1) = 0 := by
    have eq1 : (2 * x + y) ^ 3 + x ^ 3 + 3 * x + y = (3 * x + y) * ((3 * x + y) ^ 2 - 3 * x * (3 * x + y) + 3 * x ^ 2 + 1) := by
      ring_nf
    linarith [h, eq1]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case where 3x + y = 0, which is our goal.
    linarith
  · -- Case where the quadratic is true.
    nlinarith [sq_nonneg ((3 * x + y) - x), sq_nonneg (x), sq_nonneg ((3 * x + y) - 3 * x), sq_nonneg ((3 * x + y) + x), sq_nonneg (x - (3 * x + y)), sq_nonneg ((3 * x + y) * x), sq_nonneg (x * ((3 * x + y) - x)), sq_nonneg (x * (x)), sq_nonneg (( (3 * x + y) -2 * x -y) * ( (3 * x + y) -2 * x -y)), sq_nonneg ((3 * x + y) * ((3 * x + y) - 3 * x)), sq_nonneg ((x) * (x)), sq_nonneg ((3 * x + y) * x)]