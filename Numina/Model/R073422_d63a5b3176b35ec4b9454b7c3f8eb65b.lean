import Mathlib

theorem algebra_5278 {a b : ℝ} (ha : a + b = 45) (hb : a^2 + b^2 = 2021) :
    a^3 + b^3 = 90855 := by
  have h1 : a * b = 2 := by
    have h2 : (a + b) ^ 2 = a^2 + b^2 + 2 * (a * b) := by ring
    rw [ha, hb] at h2
    nlinarith
  have h3 : a^3 + b^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by ring
  rw [h3, ha, h1]
  norm_num