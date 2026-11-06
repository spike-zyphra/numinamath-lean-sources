import Mathlib

theorem algebra_195554 (l t : ℝ) (hl : l = 18) (ht : t = 9) :
    t * (l + 36) / l = 27 := by
  rw [hl, ht]
  norm_num