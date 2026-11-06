import Mathlib

theorem algebra_93076 {x y z r : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) (hge : r ≠ 0) (h : y * (z - x) = x * (y - z) * r)
    (h' : z * (x - y) = y * (z - x) * r) :
    r ^ 2 + r + 1 = 0 := by

  have eq1 : r = y * (z - x) / (x * (y - z)) := by 
    have h1 : x * (y - z) ≠ 0 := by
      apply mul_ne_zero
      exact hx
      intro h2
      apply hyz
      linarith
    field_simp [h1]
    nlinarith
  have eq2 : r = z * (x - y) / (y * (z - x)) := by
    have h2 : y * (z - x) ≠ 0 := by
      apply mul_ne_zero
      exact hy
      intro h3
      apply hzx
      linarith
    field_simp [h2]
    nlinarith
  have eq3 : y * (z - x) / (x * (y - z)) = z * (x - y) / (y * (z - x)) := by
    linarith [eq1, eq2]
  have eq4 : y * (z - x) * (y * (z - x)) = z * (x - y) * (x * (y - z)) := by
    have h1 : x * (y - z) ≠ 0 := by
      apply mul_ne_zero
      exact hx
      intro h2
      apply hyz
      linarith
    have h2 : y * (z - x) ≠ 0 := by
      apply mul_ne_zero
      exact hy
      intro h3
      apply hzx
      linarith
    field_simp [h1, h2] at eq3 ⊢
    nlinarith [eq3, sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show y ≠ 0 by exact hy), sq_pos_of_ne_zero (show z - x ≠ 0 by
      intro h
      apply hzx
      linarith
    ), sq_pos_of_ne_zero (show y - z ≠ 0 by
      intro h
      apply hyz
      linarith
    )]

  -- The equation multiplied out
  have eq5 : y ^ 2 * (z - x) ^ 2 = x * z * (y - z) * (x - y) := by
    nlinarith [eq4, sq_nonneg (y * (z - x)), sq_nonneg (x * (y - z)), sq_nonneg (y - z), sq_nonneg (x - y)]
  -- The final equation
  nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero (show y ≠ 0 by exact hy), sq_pos_of_ne_zero (show z - x ≠ 0 by
    intro h
    apply hzx
    linarith
  ), sq_pos_of_ne_zero (show y - z ≠ 0 by
    intro h
    apply hyz
    linarith
  ), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_pos_of_ne_zero (show r ≠ 0 by exact hge), pow_two_nonneg (r + 1), pow_two_nonneg (r - 1)]