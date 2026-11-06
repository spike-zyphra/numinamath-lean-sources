import Mathlib

theorem algebra_275453 {a b c : ℕ} (h₀ : a * b = 48) (h₁ : a * c = 192) (h₂ : b * c = 36) :
    a = 16 ∧ b = 3 ∧ c = 12 := by 
  have ha : a = 16 := by 
    nlinarith [h₀, h₁, h₂]
  have hb : b = 3 := by 
    nlinarith [h₀, h₁, h₂]
  have hc : c = 12 := by 
    nlinarith [h₀, h₁, h₂]
  exact ⟨ha, hb, hc⟩