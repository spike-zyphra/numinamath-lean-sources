import Mathlib

theorem algebra_2988 (h x b j s : ℝ)
    (h₀ : h + 2 * x + 3 * b + 6 * j + 7 * s = 6)
    (h₁ : 3 * h + 4 * x + 5 * b + 6 * j + 7 * s = 8)
    (h₂ : 3 * h + 4 * x + 7 * b + 8 * j + 9 * s = 4)
    (h₃ : 5 * h + 6 * x + 7 * j + 8 * s = 16) :
    h + x + b + j + s = 0 := by
  have h₄ : h + x + b = 1 := by 
    linarith
  have h₆ : x + 2 * b + 6 * j + 7 * s = 5 := by
    have h₀' : h + 2 * x + 3 * b + 6 * j + 7 * s = 6 := h₀
    have h₁' : h + x + b = 1 := h₄
    linarith
  have h₇ : x - 5 * b + 7 * j + 8 * s = 11 := by
    have h₃' : 5 * h + 6 * x + 7 * j + 8 * s = 16 := h₃
    have h₁' : h + x + b = 1 := h₄
    linarith
  have h₈ : j + s = 7 * b + 6 := by
    have h₇' : x - 5 * b + 7 * j + 8 * s = 11 := h₇
    have h₆' : x + 2 * b + 6 * j + 7 * s = 5 := h₆
    linarith
  have hb : b = -1 := by
    have h₁₁ : x - j + 67 * b = -53 := by 
      have h₂' : 3 * h + 4 * x + 7 * b + 8 * j + 9 * s = 4 := h₂
      have h₁' : h + x + b = 1 := h₄
      have h₈' : j + s = 7 * b + 6 := h₈
      linarith
    have h₁₂ : x - j + 51 * b = -37 := by 
      have h₇' : x - 5 * b + 7 * j + 8 * s = 11 := h₇
      have h₈' : j + s = 7 * b + 6 := h₈
      linarith
    linarith
  have h₁₄ : j + s = -1 := by 
    rw [hb] at h₈ 
    linarith
  linarith [h₄, h₁₄, hb]