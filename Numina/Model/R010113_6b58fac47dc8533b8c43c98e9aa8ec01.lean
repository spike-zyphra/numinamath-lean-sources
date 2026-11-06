import Mathlib

theorem algebra_609630  (x : ℝ) (h : x > 0) (h' : (600 / 2) / 50 = (600 / 2) / x + 1) : x = 60 := by
  field_simp [(show x ≠ 0 by linarith)] at h' ⊢
  nlinarith