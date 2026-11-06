import Mathlib

theorem algebra_93690 (a b c : ℤ) (h₀ : a + b = 12) (h₁ : a + c = 17) (h₂ : b + c = 19) :
    b = 7 ∧ a < b ∧ b < c := by
  have h3 : a + b + c = 24 := by
    linarith
  have ha : a = 5 := by
    linarith
  have hb : b = 7 := by
    linarith
  have hc : c = 12 := by
    linarith
  have h4 : a < b := by
    linarith
  have h5 : b < c := by
    linarith
  exact ⟨hb, h4, h5⟩