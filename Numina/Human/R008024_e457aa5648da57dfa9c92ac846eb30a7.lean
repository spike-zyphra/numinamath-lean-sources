import Mathlib

/- What is the integer value of $y$ in the arithmetic sequence $2^2, y, 2^4$? -/
theorem algebra_10568 (y : ℤ) (h : y - 2^2 = 2^4 - y) : y = 10 := by
  -- Omega can solve this problem.
  omega
