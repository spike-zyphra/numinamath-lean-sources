import Mathlib

/- A parabola with equation  $y = x^2 + bx + c$ passes through the points $(2,3)$ and $(4,3)$. What is $c$? -/
theorem algebra_12341 {b c : ℝ} (h : 3 = 2^2 + b * 2 + c) (h' : 3 = 4^2 + b * 4 + c) :
    c = 11 := by
  nlinarith