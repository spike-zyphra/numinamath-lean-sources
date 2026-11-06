import Mathlib

theorem algebra_207004 (a b c d e : ℤ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : a ≠ e) (h₄ : b ≠ c) (h₅ : b ≠ d) (h₆ : b ≠ e) (h₇ : c ≠ d) (h₈ : c ≠ e)
    (h₉ : d ≠ e) (h₁₀ : a + b = -1) (h₁₁ : a + c = 2) (h₁₂ : a + d = 6) (h₁₃ : a + e = 7)
    (h₁₄ : b + c = 8) (h₁₅ : b + d = 11) (h₁₆ : b + e = 13) (h₁₇ : c + d = 14) (h₁₈ : c + e = 16)
    (h₁₉ : d + e = 20) :
    a * b * c * d * e = -2970 := by
  have h_a : a = -3 := by
    linarith
  have h_b : b = 2 := by
    linarith [h_a, h₁₀]
  have h_c : c = 5 := by
    linarith [h_a, h₁₁]
  have h_d : d = 9 := by
    linarith [h_a, h₁₂]
  have h_e : e = 11 := by 
    linarith [h_d, h₁₉]
  rw [h_a, h_b, h_c, h_d, h_e]
  norm_num