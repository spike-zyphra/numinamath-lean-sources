import Mathlib

theorem algebra_6623 (d : ℝ) (h : d > 0) (h1 : 6 * (v + w) = d) (h2 : 8 * (v - w) = d)
    (h3 : v = 2) (h4 : w = 1) : d = 96 := by
  rw [h3, h4] at h1 h2
  linarith