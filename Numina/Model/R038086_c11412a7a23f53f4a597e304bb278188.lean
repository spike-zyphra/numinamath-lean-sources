import Mathlib

open Real

theorem inequalities_147302 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 8) :
    (x + 1 / y) ^ 2 + (y + 1 / x) ^ 2 ≥ 289 / 8 := by

  have h3 : 0 < x * y := mul_pos hx hy
  have h4 : x + y = 8 := hxy

  have h5 : (x + 1 / y) ^ 2 + (y + 1 / x) ^ 2 - 289 / 8 ≥ 0 := by
    have pos1 : 0 < x * y := h3
    have pos2 : 0 < x ^ 2 * y ^ 2 := by positivity
    have h6 : (x + 1 / y) ^ 2 + (y + 1 / x) ^ 2 - 289 / 8 =
        (8 * x^4 * y^2 + 16 * x^3 * y + 8 * x^2 + 8 * x^2 * y^4 + 16 * x * y^3 + 8 * y^2 - 289 * x^2 * y^2) / (8 * x^2 * y^2) := by
      field_simp
      ring
    rw [h6]
    apply div_nonneg
    -- Show the numerator is non-negative
    have h7 : 8 * x^4 * y^2 + 16 * x^3 * y + 8 * x^2 + 8 * x^2 * y^4 + 16 * x * y^3 + 8 * y^2 - 289 * x^2 * y^2 ≥ 0 := by
      have h8 : y = 8 - x := by linarith
      rw [show y = 8 - x by linarith]
      nlinarith [sq_nonneg (x - 4), sq_nonneg ((8 - x) - 4), sq_nonneg (x * (8 - x) - 16), sq_nonneg (x - (8 - x)), 
          sq_nonneg (x * (x - 4)), sq_nonneg ((8 - x) * ((8 - x) - 4)), 
          mul_pos hx (show 0 < (8 - x : ℝ) by nlinarith), 
          sq_nonneg (x ^ 2 - (8 - x) ^ 2)
        ]
    linarith
    -- Show the denominator is positive
    all_goals positivity

  linarith [h5]