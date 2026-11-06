import Mathlib

theorem algebra_269964 (r h : ℚ) (hr : r = 2 / 5) (hh : h = r / 2) :
    (1 - r - h) * 100 = 40 := by
  rw [hh, hr]
  norm_num