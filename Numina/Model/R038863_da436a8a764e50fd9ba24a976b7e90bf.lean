import Mathlib

theorem algebra_93082 (a b c : ℝ) (ha : a ≠ 0) (h1 : 12 = a * (-1)^2 + b * (-1) + c)
    (h2 : 5 = c) (h3 : -3 = a * 2^2 + b * 2 + c) : a + b + c = 0 := by 
  have hc : c = 5 := by linarith 
  rw [hc] at h1 h3
  linarith