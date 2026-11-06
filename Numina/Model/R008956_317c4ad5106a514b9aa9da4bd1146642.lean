import Mathlib

theorem algebra_9404 (d : ℝ) (h : d = 900) (l : ℝ) (hl : l = 0.45) :
    d / l = 2000 := by
  rw [h, hl]
  norm_num