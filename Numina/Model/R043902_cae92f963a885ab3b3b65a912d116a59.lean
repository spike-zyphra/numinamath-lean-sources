import Mathlib

theorem algebra_141293 (x : ℝ) (hx : x > 0) (h : 3 * 7000 = x * (1 + 20 / 100)) :
    x ≤ 140000 := by

  have eq1 : x = (3 * 7000) / ( (1 + (20 / 100 : ℝ) ) ) := by
    field_simp
    linarith 
  rw [eq1] 
  norm_num