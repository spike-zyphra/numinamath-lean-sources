import Mathlib

theorem algebra_6215 (a b z : ℝ) (ha : 0 < a) (hb : 0 < b)
(hsum : a + b = z / 2) :
a * b ≤ z ^ 2 / 16 := by
  have h1 : b = z / 2 - a := by linarith
  rw [h1]
  have h3 : (a + (z / 2 - a)) ^ 2 / 4 ≥ a * (z / 2 - a) := by 
    nlinarith [sq_nonneg (a - (z / 2 - a))]
  have h4 : (a + (z / 2 - a)) ^ 2 / 4 = z ^ 2 / 16 := by 
    nlinarith
  nlinarith [h3, h4]