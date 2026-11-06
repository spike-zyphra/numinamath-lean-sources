import Mathlib

theorem algebra_197725 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = d / 40 + 15 / 60) (h₃ : d / v = d / 50 - 20 / 60) :
    d = 10 := by
  have h6 : d < 0 := by 
    have h8 : d / v = d / 40 + 15 / 60 := h₂
    have h9 : d / v = d / 50 - 20 / 60 := h₃
    have h10 : 0 < v := h₁
    field_simp [show 0 < v from h₁, show 0 < (40 : ℝ) by norm_num, show 0 < (50 : ℝ) by norm_num] at h8 h9 
    nlinarith
  linarith [h₀, h6]