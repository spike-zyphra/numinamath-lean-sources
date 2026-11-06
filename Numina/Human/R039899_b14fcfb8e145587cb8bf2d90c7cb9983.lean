import Mathlib

/- An equilateral triangle has a side of length 12 inches. What is the area of the triangle, in square inches? Express your answer in simplest radical form. -/
theorem algebra_21375 (s : ℝ) (h : s = 12) :
    (s ^ 2 * Real.sqrt 3) / 4 = 36 * Real.sqrt 3 := by subst s; ring
