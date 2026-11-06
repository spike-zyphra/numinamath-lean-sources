import Mathlib

/- Find the $x$-intercept point of the line $3x+5y=20$. Provide your answer as an ordered pair.  Express the $x$ and $y$ coordinates as common fractions as needed. -/
theorem algebra_10662 (x y : ℝ) (h : 3 * x + 5 * y = 20) (hy : y = 0) :
    (x, y) = (20 / 3, 0) := by
  congr
  linarith
