import Mathlib

theorem algebra_206772 {a b : ℝ} (ha : a + b = 4) (hb : a^2 + b^2 = 14) :
    a^3 + b^3 = 52 := by
  have h1 : a * b = 1 := by
    have h2 : (a + b) ^ 2 = a^2 + b^2 + 2 * (a * b) := by 
      ring
    rw [ha, hb] at h2
    linarith
  have h3 : a^3 + b^3 = (a + b) * ((a^2 + b^2) - (a * b)) := by
    ring
  rw [h3, ha, hb, h1]
  norm_num