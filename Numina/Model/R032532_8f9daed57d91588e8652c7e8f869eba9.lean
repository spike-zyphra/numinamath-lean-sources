import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_310749 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hsum : x + y + z = 1) :
  x * (2 * y - z) / (1 + x + 3 * y) +
  y * (2 * z - x) / (1 + y + 3 * z) +
  z * (2 * x - y) / (1 + z + 3 * x) ≤ 1 / 7 := by
  have h1 : z = 1 - x - y := by
    linarith
  rw [h1]
  have hx3 : 0 < 1 + x + 3 * y := by
    nlinarith
  have hx5 : 0 < 1 + y + 3 * (1 - x - y : ℝ) := by
    nlinarith
  have hx6 : 0 < 1 + (1 - x - y : ℝ) + 3 * x := by
    nlinarith
  have h3 : x * (2 * y - (1 - x - y : ℝ)) / (1 + x + 3 * y : ℝ) + y * (2 * (1 - x - y : ℝ) - x) / (1 + y + 3 * (1 - x - y : ℝ)) + (1 - x - y : ℝ) * (2 * x - y) / (1 + (1 - x - y : ℝ) + 3 * x) - 1 / 7 ≤ 0 := by
    have h4 : x * (2 * y - (1 - x - y : ℝ)) / (1 + x + 3 * y : ℝ) + y * (2 * (1 - x - y : ℝ) - x) / (1 + y + 3 * (1 - x - y : ℝ)) + (1 - x - y : ℝ) * (2 * x - y) / (1 + (1 - x - y : ℝ) + 3 * x) - 1 / 7 = (x * (2 * y - (1 - x - y : ℝ)) * (1 + y + 3 * (1 - x - y : ℝ)) * (1 + (1 - x - y : ℝ) + 3 * x) + y * (2 * (1 - x - y : ℝ) - x) * (1 + x + 3 * y) * (1 + (1 - x - y : ℝ) + 3 * x) + (1 - x - y : ℝ) * (2 * x - y) * (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y : ℝ)) - (1 / 7) * (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y : ℝ)) * (1 + (1 - x - y : ℝ) + 3 * x)) / ((1 + x + 3 * y : ℝ) * (1 + y + 3 * (1 - x - y : ℝ)) * (1 + (1 - x - y : ℝ) + 3 * x)) := by
      field_simp
      ring
    rw [h4] at *
    have hx10 : 0 < (1 + x + 3 * y : ℝ) * (1 + y + 3 * (1 - x - y : ℝ)) * (1 + (1 - x - y : ℝ) + 3 * x) := by
      positivity
    have hx11 : x * (2 * y - (1 - x - y : ℝ)) * (1 + y + 3 * (1 - x - y : ℝ)) * (1 + (1 - x - y : ℝ) + 3 * x) + y * (2 * (1 - x - y : ℝ) - x) * (1 + x + 3 * y) * (1 + (1 - x - y : ℝ) + 3 * x) + (1 - x - y : ℝ) * (2 * x - y) * (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y : ℝ)) - (1 / 7) * (1 + x + 3 * y) * (1 + y + 3 * (1 - x - y : ℝ)) * (1 + (1 - x - y : ℝ) + 3 * x) ≤ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y : ℝ)), sq_nonneg (y - (1 - x - y : ℝ)), 
                  mul_pos hx hy, mul_pos hx (show 0 < (1 - x - y : ℝ) by nlinarith), 
                  mul_pos hy (show 0 < (1 - x - y : ℝ) by nlinarith), 
                  sq_nonneg (x + y - (1 - x - y : ℝ)), 
                  sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y : ℝ) - 1 / 3)
                ]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith
    all_goals
      positivity
  linarith