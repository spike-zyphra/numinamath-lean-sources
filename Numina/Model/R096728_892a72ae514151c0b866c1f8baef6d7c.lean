import Mathlib

theorem algebra_275499 (a b : ℝ) (ha : a = 1 / 2) (hb : b = 2 / 3) :
    (6 * a + 18 * b) / (12 * a + 6 * b) = 3 / 2 := by 
  rw [ha, hb]
  norm_num