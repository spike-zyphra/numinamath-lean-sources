import Mathlib

/- Real numbers $x$, $y$ satisfy ${{x}^{2}}+{{y}^{2}}=20$, then the maximum value of $xy+8x+y$ is ___          ___. -/
theorem algebra_12120 (x y : ℝ) (h : x^2 + y^2 = 20) :
    x * y + 8 * x + y ≤ 42 := by
  nlinarith [sq_nonneg (x - 4), sq_nonneg (y - 2),
          sq_nonneg (x + 4), sq_nonneg (y + 2),
          sq_nonneg (x * y - 8), sq_nonneg (x - y),
          sq_nonneg (x * y), sq_nonneg (y - 2),
          sq_nonneg (x - 2 * y), sq_nonneg (x * y - 4)]