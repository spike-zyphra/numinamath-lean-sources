import Mathlib

/- A line segment begins at $(2, 5)$. It is 10 units long and ends at the point $(-6, y)$ where $y > 0$. What is the value of $y$? -/
theorem algebra_17190 (x1 x2 y1 y2 : ℝ) (h1 : x1 = 2) (h2 : x2 = -6) (h3 : y1 = 5)
    (h4 : y2 > 0) (h5 : Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2) = 10) :
    y2 = 11 := by
  rw [h1, h2, h3] at h5
  rw [Real.sqrt_eq_iff_sq_eq] at h5 <;> nlinarith