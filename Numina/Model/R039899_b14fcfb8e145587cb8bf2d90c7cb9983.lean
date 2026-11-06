import Mathlib

theorem algebra_21375 (s : ℝ) (h : s = 12) :
    (s ^ 2 * Real.sqrt 3) / 4 = 36 * Real.sqrt 3 := by 
  rw [h]
  ring