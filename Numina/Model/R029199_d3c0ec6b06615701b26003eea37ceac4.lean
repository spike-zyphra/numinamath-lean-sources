import Mathlib

open Real Set

theorem inequalities_598124 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    (28 / 3) ^ 3 ≤ (1 / x^2 + x) * (1 / y^2 + y) * (1 / z^2 + z) := by 
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hz1 : 0 < z := hz
  have h5 : (1 / x^2 + x) * (1 / y^2 + y) * (1 / z^2 + z) ≥ (28 / 3) ^ 3 := by 
    have hx2 : x > 0 := hx
    have hy2 : y > 0 := hy
    have hz2 : z > 0 := hz
    have h6 : (1 / x^2 + x) * (1 / y^2 + y) * (1 / z^2 + z) - (28 / 3) ^ 3 ≥ 0 := by 
      have h1' : 0 < x * y * z := by 
        positivity 
      have h7 : (1 / x^2 + x) * (1 / y^2 + y) * (1 / z^2 + z) - (28 / 3) ^ 3 = 
          ( (1 + x^3) * (1 + y^3) * (1 + z^3) - ( (28 / 3) ^ 3 ) * (x^2 * y^2 * z^2) ) / (x^2 * y^2 * z^2 ) := by 
          field_simp 
          ring 
      rw [h7] at *
      have h8 : ( (1 + x^3) * (1 + y^3) * (1 + z^3) - ( (28 / 3) ^ 3 ) * (x^2 * y^2 * z^2 ) ) ≥ 0 := by 
        have h51 : z = 1 - x - y := by linarith 
        rw [h51] 
        have hx3 : x > 0 := hx 
        have hy3 : y > 0 := hy 
        have h52 : (1 - x - y) > 0 := by 
          nlinarith 
        nlinarith [ sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
            sq_nonneg (x * y - x * (1 - x - y) ), sq_nonneg (y * x - y * (1 - x - y) ), sq_nonneg (x * (1 - x - y) - y * (1 - x - y) ), 
            mul_pos hx hy, mul_pos hx (show (1 - x - y) > 0 by nlinarith ), 
            mul_pos hy (show (1 - x - y) > 0 by nlinarith ), 
            sq_nonneg (x * y * (1 - x - y) - 1 / 27 ), 
            mul_pos (show 0 < x * y by nlinarith ) (show 0 < (1 - x - y) by nlinarith ) ]
      have h9 : 0 < x^2 * y^2 * z^2 := by 
        positivity 
      apply div_nonneg 
      linarith [h8] 
      all_goals positivity 
    linarith 
  linarith