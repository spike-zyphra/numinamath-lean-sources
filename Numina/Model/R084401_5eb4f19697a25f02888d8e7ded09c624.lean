import Mathlib

theorem algebra_6537 {a b : ℝ} (ha : a + b = 9) (hb : a * b = 7) :
    a ^ 2 + b ^ 2 = 67 := by 
  have h : a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by 
    ring
  rw [h, ha, hb]
  norm_num