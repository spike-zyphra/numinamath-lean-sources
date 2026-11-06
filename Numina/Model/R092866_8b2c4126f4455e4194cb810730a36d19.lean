import Mathlib

theorem algebra_20601 (l w : ℝ) (hl : l = 6) (hw : w = 10) (h : l * w = 60) :
    (9 * w) / l = 15 := by
  rw [hl, hw]
  norm_num