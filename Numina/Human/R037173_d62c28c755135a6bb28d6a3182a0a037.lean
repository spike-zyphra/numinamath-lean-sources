import Mathlib
/- What is the sum of the coefficients of the expansion $(x+2 y-1)^{6}$ ? -/
theorem algebra_610869 (f : ℝ → ℝ → ℝ) (hf : f = fun x y => (x + 2 * y - 1) ^ 6) : f 1 1 = 64:= by
  -- expand the expression
  simp [hf]
  -- evaluate the expression at (1, 1)
  linarith
