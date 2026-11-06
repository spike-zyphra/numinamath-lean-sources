import Mathlib

theorem algebra_235190 (x : ℝ) (hx : x = 360) :
    (3 * 120 + 9) * 0.8 ≤ x := by 
  rw [hx]
  norm_num