import Mathlib

/- The sum of the $x$-coordinates of the vertices of a triangle in the Cartesian plane equals $10$.  Find the sum of the $x$-coordinates of the midpoints of the sides of the triangle. -/
theorem algebra_17251 (A B C : ℝ × ℝ) (h₀ : A.1 + B.1 + C.1 = 10) :
    (A.1 + B.1) / 2 + (B.1 + C.1) / 2 + (C.1 + A.1) / 2 = 10 := by
  linarith