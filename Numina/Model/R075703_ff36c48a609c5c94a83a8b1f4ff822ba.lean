import Mathlib

theorem algebra_7095 {a b : ℤ} (ha : a = -105) (hb : b = 209) : 2*a^3 + 30*a^2 + 156*a + b^3 - 27*b^2 + 243*b - 449 = 5999400 := by 
  rw [ha, hb]
  norm_num