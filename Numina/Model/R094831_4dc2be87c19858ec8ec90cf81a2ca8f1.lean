import Mathlib

theorem algebra_297261 {a b : ℝ} (ha : a + b = 4) (hb : a^3 + b^3 = 28) :
    a^2 + b^2 = 10 := by 
  have h1 : a^3 + b^3 = (a + b) ^ 3 - 3 * a * b * (a + b) := by 
    ring 
  rw [h1, ha] at hb 
  have h2 : a * b = 3 := by 
    nlinarith 
  have h3 : a^2 + b^2 = (a + b)^2 - 2 * (a * b) := by 
    ring 
  rw [ha, h2] at h3 
  nlinarith