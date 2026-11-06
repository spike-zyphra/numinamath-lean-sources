import Mathlib

theorem algebra_2564 {a b : ℝ} (ha : a + b = 6) (hb : a^3 + b^3 = 72) :
    a^2 + b^2 = 20 := by 
  have h1 : a^3 + b^3 = (a + b) ^ 3 - 3 * a * b * (a + b) := by 
    ring
  rw [h1] at hb 
  rw [ha] at hb
  have h2 : a * b = 8 := by 
    nlinarith
  have h3 : a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by
    ring
  rw [ha, h2] at h3
  linarith [h3]