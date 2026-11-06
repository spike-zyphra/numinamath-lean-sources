import Mathlib

/- Let $x$ and $y$ be positive reals such that \[ x^3 + y^3 + (x + y)^3 + 30xy = 2000. \] Show that $x + y = 10$. -/
theorem algebra_47550 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^3 + y^3 + (x + y)^3 + 30 * x * y = 2000) : x + y = 10 := by 
  nlinarith [sq_nonneg (x - y), mul_self_nonneg (x + y)]