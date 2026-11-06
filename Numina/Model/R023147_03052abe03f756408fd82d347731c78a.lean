import Mathlib

open Real
open scoped BigOperators

theorem algebra_280804 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hsum : x + y + z = 1) :
  x * (2 * y - z) / (1 + x + 3 * y) + y * (2 * z - x) / (1 + y + 3 * z) +
  z * (2 * x - y) / (1 + z + 3 * x) ≤ 1 / 7 := by

  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  have pos1 : 0 < 1 + x + 3 * y := by nlinarith
  have pos2 : 0 < 1 + y + 3 * (1 - x - y) := by nlinarith
  have pos3 : 0 < 1 + (1 - x - y) + 3 * x := by nlinarith
  have h2 : x * (2 * y - (1 - x - y)) / (1 + x + 3 * y) + y * (2 * (1 - x - y) - x) / (1 + y + 3 * (1 - x - y)) + (1 - x - y) * (2 * x - y) / (1 + (1 - x - y) + 3 * x) - 1 / 7 ≤ 0 := by
    have h3 : 0 < (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y)) * (1 + (1 - x - y) + 3 * x) := by positivity
    have h4 : x * (2 * y - (1 - x - y)) / (1 + x + 3 * y) + y * (2 * (1 - x - y) - x) / (1 + y + 3 * (1 - x - y)) + (1 - x - y) * (2 * x - y) / (1 + (1 - x - y) + 3 * x) - 1 / 7 =
        ( (x * (2 * y - (1 - x - y)) * (1 + y + 3 * (1 - x - y)) * (1 + (1 - x - y) + 3 * x) ) +
          (y * (2 * (1 - x - y) - x) * (1 + x + 3 * y) * (1 + (1 - x - y) + 3 * x) ) +
          ( (1 - x - y) * (2 * x - y) * (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y)) ) - (1 / 7) * (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y)) * (1 + (1 - x - y) + 3 * x) ) / ( (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y)) * (1 + (1 - x - y) + 3 * x) ) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Numerator is non-positive
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
        sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y) - 1 / 3), 
        mul_pos hx hy, mul_pos hy (show 0 < (1 - x - y) by nlinarith), 
        mul_pos hx (show 0 < (1 - x - y) by nlinarith) ]
    · -- Denominator is non-negative
      positivity
  linarith