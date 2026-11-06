import Mathlib

theorem algebra_97896 (a b c d e : ℝ)
    (h₀ : a = 5) (h₁ : b = 5) (h₂ : c = 6) (h₃ : d = 8)
    (h₄ : e = 106) :
    (a + b + c + d + e) / 5 > (c : ℝ) ∧ (a + b + c + d + e) / 5 - c = 20 := by 
  rw [h₀, h₁, h₂, h₃, h₄]
  constructor
  · norm_num -- proves 26 > 6
  · norm_num -- proves 26 - 6 = 20