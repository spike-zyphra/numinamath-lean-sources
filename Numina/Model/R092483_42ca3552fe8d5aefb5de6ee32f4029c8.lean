import Mathlib

theorem algebra_290538 (d : ℝ) (h₀ : d > 0) (h₁ : 2 * 16 + 2.25 * 24 + d / 12 = 2 * 12 + 2.25 * 16 + d / 24) :
    d = 34 := by
  norm_num at h₁
  linarith