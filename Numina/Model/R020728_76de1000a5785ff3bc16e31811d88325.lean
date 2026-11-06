import Mathlib

theorem algebra_206566 (total_tangent : ℝ) (h : total_tangent = 3 * 120 + 9) :
    total_tangent * 0.8 ≤ 360 := by 
  rw [h]
  norm_num