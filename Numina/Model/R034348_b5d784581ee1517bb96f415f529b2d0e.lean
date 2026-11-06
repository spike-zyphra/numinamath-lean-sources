import Mathlib

theorem algebra_239908 (a b c d e f : ℕ) (h₀ : a + b + c + d + e + f = 129)
    (h₁ : a - 6 = b - 11) (h₂ : b - 11 = c - 8) (h₃ : c - 8 = d - 10)
    (h₄ : d - 10 = e - 7) (h₅ : e - 7 = f - 9) :
    a = 19 ∧ b = 24 ∧ c = 21 ∧ d = 23 ∧ e = 20 ∧ f = 22 := by
  have h6 : a = 19 := by 
    omega
  have hb : b = 24 := by 
    omega
  have hc : c = 21 := by 
    omega
  have hd : d = 23 := by 
    omega
  have he : e = 20 := by 
    omega
  have hf : f = 22 := by 
    omega
  exact ⟨h6, hb, hc, hd, he, hf⟩