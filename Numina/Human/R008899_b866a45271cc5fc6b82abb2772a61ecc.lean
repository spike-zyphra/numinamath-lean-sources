import Mathlib

/- A trapezoid has one base equal to twice its height, $x$, and the other base is three times as long as the height. Write the expression for the area of the trapezoid as a common fraction in terms of the height $x$. -/
theorem algebra_11367 (x : ℝ) (hx : x > 0) :
    (1 / 2) * x * (2 * x + 3 * x) = 5 * x ^ 2 / 2 := by
  field_simp
  ring