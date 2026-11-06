import Mathlib

theorem algebra_21905 (a b : ℝ) (ha : a = 5) (hb : b = 7) :
    (a + 2 * 0.5) * (b + 2 * 0.5) - a * b = 13 := by 
  rw [ha, hb]
  norm_num