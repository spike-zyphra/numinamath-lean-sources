import Mathlib

open Real Set
open scoped BigOperators

/- Let $x$, $y$ be real numbers, $2x+y\geqslant 1$, then the minimum value of the bivariate function $u={{x}^{2}}+4x+{{y}^{2}}-2y$ is ___          ___. -/
theorem algebra_10927 (x y : ℝ) (h : 2 * x + y ≥ 1) :
    x ^ 2 + 4 * x + y ^ 2 - 2 * y ≥ -9 / 5 := by

  nlinarith [sq_nonneg (x + 2 / 5), sq_nonneg (y - 9 / 5), 
      sq_nonneg (2 * x + y - 1), 
      sq_nonneg (x + 2 - (y - 1) * 2), 
      sq_nonneg (y - 1 - 2 * (x + 2)), 
      Real.sqrt_nonneg (0 : ℝ)
  ]