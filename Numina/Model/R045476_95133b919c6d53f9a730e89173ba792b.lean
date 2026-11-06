import Mathlib

theorem number_theory_111185 (a b c d e f g h : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : a ≠ e) (h₄ : a ≠ f) (h₅ : a ≠ g) (h₆ : a ≠ h) (h₇ : b ≠ c) (h₈ : b ≠ d)
    (h₉ : b ≠ e) (h₁₀ : b ≠ f) (h₁₁ : b ≠ g) (h₁₂ : b ≠ h) (h₁₃ : c ≠ d) (h₁₄ : c ≠ e)
    (h₁₅ : c ≠ f) (h₁₆ : c ≠ g) (h₁₇ : c ≠ h) (h₁₈ : d ≠ e) (h₁₉ : d ≠ f) (h₂₀ : d ≠ g)
    (h₂₁ : d ≠ h) (h₂₂ : e ≠ f) (h₂₃ : e ≠ g) (h₂₄ : e ≠ h) (h₂₅ : f ≠ g) (h₂₆ : f ≠ h)
    (h₂₇ : g ≠ h) (h₂₈ : a + b + c + d + e + f + g = 42) (h₂₉ : a + b + c + d + e + f + h = 47)
    (h₃₀ : a + b + c + d + e + g + h = 50) (h₃₁ : a + b + c + d + f + g + h = 52) (h₃₂ : a + b + c + e + f + g + h = 54)
    (h₃₃ : a + b + d + e + f + g + h = 55) (h₃₄ : a + c + d + e + f + g + h = 56) (h₃₅ : b + c + d + e + f + g + h = 57) :
    a = 2 ∧ b = 3 ∧ c = 4 ∧ d = 5 ∧ e = 7 ∧ f = 9 ∧ g = 12 ∧ h = 17 := by
  have h1 : a + b + c + d + e + f + g + h = 59 := by 
    omega
  have ha : a = 2 := by
    omega
  have hb : b = 3 := by
    omega
  have hc : c = 4 := by
    omega
  have hd : d = 5 := by
    omega
  have he : e = 7 := by 
    omega
  have hf : f = 9 := by 
    omega
  have hg : g = 12 := by 
    omega
  have hh : h = 17 := by 
    omega
  exact ⟨ha, hb, hc, hd, he, hf, hg, hh⟩