import Mathlib

open Real Set

theorem algebra_154529 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 / (x + 3 * y) + 1 / (2 * x + y) = 1) :
    x + y ≥ (3 + 2 * √2) / 5 := by
  have h1 : 0 < x + 3 * y := by nlinarith [hx, hy]
  have h2 : 0 < 2 * x + y := by nlinarith [hx, hy]
  have h3 : (2 * x + y) + (x + 3 * y) = (x + 3 * y) * (2 * x + y) := by 
    field_simp [h1, h2] at h 
    nlinarith
  nlinarith [sq_nonneg (x + 3 * y - (1 + Real.sqrt 2)), 
          sq_nonneg (2 * x + y - (1 + Real.sqrt 2) / 2), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (2 : ℝ) ≥ 0), 
          mul_pos hx hy, 
          h3]