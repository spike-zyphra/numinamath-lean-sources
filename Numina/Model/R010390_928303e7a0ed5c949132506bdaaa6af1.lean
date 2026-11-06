import Mathlib

theorem algebra_14662 (a l t : ℝ)
    (ha : a = 3 / 8) (hl : l = 3 / 10) (ht : t = 1 - a - l) :
    t = 13 / 40 := by
  rw [ht, ha, hl]
  norm_num