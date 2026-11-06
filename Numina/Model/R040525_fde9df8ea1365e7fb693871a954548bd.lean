import Mathlib

open Real

theorem inequalities_159432 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    ((1 / x ^ 2 + x) * (1 / y ^ 2 + y) * (1 / z ^ 2 + z)) ≥ (28 / 3) ^ 3 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : ((1 / x ^ 2 + x) * (1 / y ^ 2 + y) * (1 / z ^ 2 + z)) - (28 / 3) ^ 3 ≥ 0 := by
    have h3 : 0 < x * y * z := h1
    have h4 : ((1 / x ^ 2 + x) * (1 / y ^ 2 + y) * (1 / z ^ 2 + z)) - (28 / 3) ^ 3 =
        ((1 + x^3) * (1 + y^3) * (1 + z^3) - (28 / 3) ^ 3 * (x * y * z) ^ 2) / ((x^2 * y^2 * z^2)) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    -- Prove that the numerator is non-negative
    have h5 : ((1 + x^3) * (1 + y^3) * (1 + z^3)) ≥ (28 / 3) ^ 3 * (x * y * z) ^ 2 := by
      have h6 : z = 1 - x - y := by linarith 
      rw [h6]
      nlinarith [sq_nonneg (x * y - (1 - x - y) * y), sq_nonneg (y * (1 - x - y) - x * (1 - x - y)), sq_nonneg (x * y - y * (1 - x - y)), sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
                sq_nonneg (x * y * (1 - x - y) - 1 / 27), 
                mul_pos hx hy, mul_pos hy (show 0 < 1 - x - y by nlinarith), mul_pos (show 0 < 1 - x - y by nlinarith) hx, 
                mul_pos (show 0 < x * y by nlinarith) (show 0 < y * (1 - x - y) by nlinarith), 
                mul_pos (show 0 < y * (1 - x - y) by nlinarith) (show 0 < x * (1 - x - y) by nlinarith), 
                mul_pos (show 0 < x * (1 - x - y) by nlinarith) (show 0 < x * y by nlinarith)]
    linarith 
    all_goals 
      positivity 
  linarith