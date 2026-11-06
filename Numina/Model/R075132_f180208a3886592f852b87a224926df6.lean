import Mathlib

theorem algebra_6486 {x y : ℝ} (h : (11, 8) = ((x, 4) + (-5, y)) / 2) : x + y = 39 := by
  simp [Prod.ext_iff] at h 
  linarith