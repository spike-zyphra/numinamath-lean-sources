import Mathlib

theorem algebra_2590 (x : ℝ) (hx : x ≠ 0) (h : 2.5 = x * 1.25) :
    x = 2 := by
  have eq1 : x = (2.5 : ℝ) / 1.25 := by
    field_simp
    linarith
  rw [eq1]
  norm_num