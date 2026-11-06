import Mathlib

theorem inequalities_222698 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    1 / x + 1 / y + 1 / z ≥ 9 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  
  have h2 : 1 / x + 1 / y + 1 / z - 9 ≥ 0 := by
    have h3 : 0 < x * y * z := h1
    have h4 : (1 / x + 1 / y + 1 / z - 9) = (y * z + x * z + x * y - 9 * (x * y * z)) / (x * y * z) := by
      field_simp
      ring
  
    rw [h4] at *
  
    have h4 : 0 < x * y * z := h1
  
    have h5 : y * z + x * z + x * y ≥ 9 * (x * y * z) := by 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y + z - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
        hsum, 
        mul_pos hx (show 0 < y * z by nlinarith [mul_pos hy hz]), 
        mul_pos hy (show 0 < x * z by nlinarith [mul_pos hx hz]), 
        mul_pos hz (show 0 < x * y by nlinarith [mul_pos hx hy])
        ]

    have h6 : y * z + x * z + x * y - 9 * (x * y * z) ≥ 0 := by 
      linarith [h5]

    apply div_nonneg
    linarith
    all_goals
      nlinarith
  
  linarith [h2]