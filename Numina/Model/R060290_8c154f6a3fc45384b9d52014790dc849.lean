import Mathlib

theorem algebra_199814 (m r : ℝ) (hm : m > 0) (hr : r > 0)
    (h1 : m / r = 3 / 2) (h2 : (m * 7 + r * 3) / (m + r) = 7 / 3)
    (h3 : (m * 4 + r) / m = 4 / 1) :
    (m * 8 + r * 5) / (m + r) = 9 / 8 := by
  field_simp [show m ≠ 0 by linarith] at h3
  nlinarith