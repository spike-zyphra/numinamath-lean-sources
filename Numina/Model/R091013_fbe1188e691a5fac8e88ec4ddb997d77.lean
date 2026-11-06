import Mathlib

theorem algebra_298593 (a : ℝ) (ha : 0 < a) (h : a + 2 * a + 4 * a = 1) :
    a * 700 + 2 * a * 560 + 4 * a * 420 = 500 := by 
  have ha_eq : a = 1 / 7 := by 
    linarith
  rw [ha_eq]
  norm_num