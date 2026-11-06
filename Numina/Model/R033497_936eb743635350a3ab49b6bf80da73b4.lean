import Mathlib

theorem algebra_176600 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a * 360 = b * 180 + c * 150) (h2 : b * 360 = c * 180 + a * 150)
    (h3 : b = 4 * a) :
    a * 90 = b * 45 := by
  rw [show b = 4 * a by linarith] at h1 h2
  nlinarith