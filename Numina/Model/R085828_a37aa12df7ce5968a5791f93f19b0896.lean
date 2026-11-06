import Mathlib

theorem algebra_243041 (length : ℝ) (hlength : length = 40) (mass : ℝ) (hm : mass = 26) :
    mass / length = 0.65 := by
  rw [hlength, hm]
  norm_num