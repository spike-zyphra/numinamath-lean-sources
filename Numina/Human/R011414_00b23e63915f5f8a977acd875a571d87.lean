import Mathlib

theorem algebra_2564 {a b : ℝ} (ha : a + b = 6) (hb : a^3 + b^3 = 72) :
    a^2 + b^2 = 20 := by
  have h1 : a^3 + b^3 = (a + b) * (a^2 - a * b + b^2) := by ring_nf
  rw [h1] at hb
  rw [ha] at hb
  have h2 : a^2 - a * b + b^2 = 12 := by linarith
  have h3 : (a + b) ^ 2 = 36 := by
    rw [ha]
    norm_num
  have h4 : (a + b) ^ 2 = a^2 + 2 * a * b + b^2 := by ring
  rw [h4] at h3
  have hab : a * b = 8 := by linarith
  linarith