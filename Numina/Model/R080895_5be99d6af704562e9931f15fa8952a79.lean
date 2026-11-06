import Mathlib

theorem algebra_235132 (a b c d : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : b + c + d = 42)
    (h₂ : a + c + d = 40)
    (h₃ : a + b + d = 38)
    (h₄ : a + b + c = 36) :
    a = 10 ∧ b = 12 ∧ c = 14 ∧ d = 16 := by
  have h5 : a + b + c + d = 52 := by 
    linarith 
  have ha : a = 10 := by 
    linarith [h₁, h5]
  have hb : b = 12 := by 
    linarith [h₂, h5]
  have hc : c = 14 := by 
    linarith [h₃, h5]
  have hd : d = 16 := by 
    linarith [h₄, h5]
  exact ⟨ha, hb, hc, hd⟩