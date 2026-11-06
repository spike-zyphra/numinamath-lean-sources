import Mathlib

/- A trapezoid has one base equal to its height, $x$, and the other base is twice as long. Write the expression for the area of the trapezoid as a common fraction in terms of $x$. -/
theorem algebra_19967 (x : ℝ) (hx : x > 0) :
    (1 / 2) * (x + 2 * x) * x = 3 * x ^ 2 / 2 := by
        linarith