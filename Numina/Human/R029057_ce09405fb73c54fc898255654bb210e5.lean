import Mathlib

/- The equation of an ellipse is given $2x^2 - 8x + 3y^2 + 6y + 5 = 0.$  Find the maximum value of the $x$-coordinate of a point on this ellipse. -/
theorem algebra_21642 (x y : ℝ) (h : 2*x^2 - 8*x + 3*y^2 + 6*y + 5 = 0) :
    x ≤ 2 + Real.sqrt 3 := by
  -- Completing the square for x
  have h1 : (x - 2)^2 / 3 + (y + 1)^2 / 2 = (2*x^2 - 8*x + 3*y^2 + 6*y + 5 + 6) / 6 := by
    ring
  rw [h, zero_add, div_self (by exact Ne.symm (OfNat.zero_ne_ofNat 6))] at h1
  -- The maximum x-coordinate is the center x-coordinate plus the semi-major axis length
  have h2 : 0 ≤ (y + 1) ^ 2 / 2 := by
    nlinarith
  have h3 : (x - 2) ^ 2 ≤ 3 := by
    linarith
  apply le_add_of_sub_left_le
  exact Real.le_sqrt_of_sq_le h3