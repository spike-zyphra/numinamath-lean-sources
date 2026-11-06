import Mathlib

theorem inequalities_327216 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt (x^2 + x * y + y^2) + Real.sqrt (x^2 + x * z + z^2) > Real.sqrt (y^2 + y * z + z^2) := by

  have h1 : 0 < x^2 + x * y + y^2 := by
    nlinarith [mul_pos hx hy, sq_pos_of_pos hx, sq_pos_of_pos hy]

  have h2 : 0 < x^2 + x * z + z^2 := by
    nlinarith [mul_pos hx hz, sq_pos_of_pos hx, sq_pos_of_pos hz]

  have h3 : 0 < y^2 + y * z + z^2 := by
    nlinarith [mul_pos hy hz, sq_pos_of_pos hy, sq_pos_of_pos hz]

  have h4 : Real.sqrt (x^2 + x * y + y^2) + Real.sqrt (x^2 + x * z + z^2) > 0 := by
    positivity

  have h5 : Real.sqrt (y^2 + y * z + z^2) > 0 := by
    positivity

  have h6 : (Real.sqrt (x^2 + x * y + y^2) + Real.sqrt (x^2 + x * z + z^2)) ^ 2 > (Real.sqrt (y^2 + y * z + z^2)) ^ 2 := by

    have h7 : (Real.sqrt (x^2 + x * y + y^2) + Real.sqrt (x^2 + x * z + z^2)) ^ 2 =
        (Real.sqrt (x^2 + x * y + y^2)) ^ 2 + (Real.sqrt (x^2 + x * z + z^2)) ^ 2 + 2 * (Real.sqrt (x^2 + x * y + y^2) * Real.sqrt (x^2 + x * z + z^2)) := by
      ring

    have h8 : (Real.sqrt (y^2 + y * z + z^2)) ^ 2 = y^2 + y * z + z^2 := by
      rw [Real.sq_sqrt]
      positivity

    have h9 : (Real.sqrt (x^2 + x * y + y^2)) ^ 2 = x^2 + x * y + y^2 := by
      rw [Real.sq_sqrt]
      positivity

    have h10 : (Real.sqrt (x^2 + x * z + z^2)) ^ 2 = x^2 + x * z + z^2 := by
      rw [Real.sq_sqrt]
      positivity

    rw [h7, h9, h10, h8]

    nlinarith [sq_nonneg (Real.sqrt (x^2 + x * y + y^2) - Real.sqrt (x^2 + x * z + z^2)), 
          sq_nonneg (Real.sqrt (x^2 + x * y + y^2) - Real.sqrt (y^2 + y * z + z^2)), 
          sq_nonneg (Real.sqrt (x^2 + x * z + z^2) - Real.sqrt (y^2 + y * z + z^2)), 
          Real.sqrt_nonneg (x^2 + x * y + y^2), 
          Real.sqrt_nonneg (x^2 + x * z + z^2), 
          Real.sqrt_nonneg (y^2 + y * z + z^2), 
          mul_pos hx hy, 
          mul_pos hx hz, 
          mul_pos hy hz, 
          mul_pos (show x^2 + x * y + y^2 > 0 by positivity) (show x^2 + x * z + z^2 > 0 by positivity), 
          Real.sq_sqrt (show x^2 + x * y + y^2 ≥ 0 by positivity), 
          Real.sq_sqrt (show x^2 + x * z + z^2 ≥ 0 by positivity), 
          Real.sq_sqrt (show y^2 + y * z + z^2 ≥ 0 by positivity), 
          mul_nonneg (Real.sqrt_nonneg (x^2 + x * y + y^2)) (Real.sqrt_nonneg (x^2 + x * z + z^2))
        ]

  nlinarith [h4, h5, h6]