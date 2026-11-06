import Mathlib

theorem algebra_179926 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = d / (v + 2) + 10.56) (h₃ : d / v = d / (v + 2) + 12.20) :
    d / v = 10 := by 
  norm_num at h₂ h₃ 
  linarith