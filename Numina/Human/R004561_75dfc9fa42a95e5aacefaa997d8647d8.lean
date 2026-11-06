import Mathlib

theorem algebra_284058 (v p c w : ℝ) (h₀ : v > 0) (h₁ : p > 0) (h₂ : c > 0)
    (h₃ : w > 0) (h₄ : 1 / v = 10 / 60) (h₅ : 2 / v = 15 / 60) (h₆ : 3 / v = 17.5 / 60)
    (h₇ : 1 / c = 10 / 60 + w / 60) (h₈ : 2 / c = 15 / 60 + w / 60) (h₉ : 3 / c = 17.5 / 60 + w / 60)
    (h₁₀ : w = 1 / 60) :
    6 / v = 25 / 60 := by 
  have h11 : v = 1 / (10 / 60 : ℝ) := by
    field_simp at h₄
    linarith
  have h12 : v = 2 / (15 / 60 : ℝ) := by
    field_simp at h₅
    linarith
  have h13 : v = 3 / (17.5 / 60 : ℝ) := by
    field_simp at h₆
    norm_num at *
    linarith
  rw [h11] at h12
  norm_num at h11 h12