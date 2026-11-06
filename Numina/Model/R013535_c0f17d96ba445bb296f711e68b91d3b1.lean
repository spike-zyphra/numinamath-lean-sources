import Mathlib

open Real Set

theorem algebra_230536 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 19 / x + 98 / y = 1) :
    x + y ≥ 117 + 14 * √38 := by
  have h1 : 0 < x := hx
  have h2 : 0 < y := hy
  have h3 : 19 * y + 98 * x = x * y := by
    have hne1 : x ≠ 0 := by linarith
    have hne2 : y ≠ 0 := by linarith
    field_simp [hne1, hne2] at h
    nlinarith
  nlinarith [sq_nonneg (x - (19 + 7 * Real.sqrt 38)), sq_nonneg (y - (98 + 7 * Real.sqrt 38)), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 38 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (38 : ℝ) by norm_num), 
          Real.sqrt_nonneg 38, 
          mul_pos hx hy, 
          sq_nonneg (Real.sqrt 38), 
          Real.sqrt_nonneg 38, 
          mul_self_nonneg (x - (19 + 7 * Real.sqrt 38)), 
          mul_self_nonneg (y - (98 + 7 * Real.sqrt 38)), 
          Real.sqrt_nonneg 38
        ]