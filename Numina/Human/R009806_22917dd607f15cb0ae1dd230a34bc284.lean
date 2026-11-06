import Mathlib

/- Find the distance between the points $(2,2)$ and $(-1,-1)$. -/
theorem algebra_13734 (p1 p2 : ℝ × ℝ) (hp1 : p1 = (2, 2)) (hp2 : p2 = (-1, -1)) :
    Real.sqrt ((p1.1 - p2.1)^2 + (p1.2 - p2.2)^2) = 3 * Real.sqrt 2 := by
  rw [hp1, hp2]
  norm_num
  ring
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  ring
  norm_num