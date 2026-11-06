import Mathlib

theorem algebra_163305 (a b c : ℕ) (h₀ : a = b + 6) (h₁ : c = 2 * b)
    (h₂ : a + b + c = 66) :
    a = 21 ∧ b = 15 ∧ c = 30 := by 
  have hb : b = 15 := by 
    linarith [h₀, h₁, h₂]
  have ha : a = 21 := by 
    linarith [h₀, hb]
  have hc : c = 30 := by 
    linarith [h₁, hb]
  exact ⟨ha, hb, hc⟩