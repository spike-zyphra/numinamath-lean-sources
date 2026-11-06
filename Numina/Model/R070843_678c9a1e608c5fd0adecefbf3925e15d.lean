import Mathlib

theorem other_138589 (h : ℝ) (h₀ : h > 0) (h₁ : (1 - 1.33) * h = 52) :
    h = 39 := by
  norm_num at h₁
  linarith
  <;> norm_num <;> nlinarith