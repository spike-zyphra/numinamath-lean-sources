import Mathlib

/- A line segment begins at $(1, 3)$. It is 5 units long and ends at the point $(4, x)$ and $x > 0$. What is the value of $x$? -/
theorem algebra_14789 (x : ℝ) (hx : x > 0) (h : Real.sqrt ((4 - 1)^2 + (x - 3)^2) = 5) :
    x = 7 := by
  rw [Real.sqrt_eq_iff_sq_eq] at h <;> nlinarith