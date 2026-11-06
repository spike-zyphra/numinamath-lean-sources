import Mathlib

theorem algebra_237138 (a b c d : ℝ) (h₀ : a + b + c + d = 89.6)
    (h₁ : (1 / 2) * a = (1 / 3) * b) (h₂ : (1 / 3) * b = (1 / 4) * c)
    (h₃ : (1 / 4) * c = (1 / 5) * d) :
    a = 12.8 ∧ b = 19.2 ∧ c = 25.6 ∧ d = 32 := by
  have ha : a = 12.8 := by
    ring_nf at *
    linarith
  have hb : b = 19.2 := by
    ring_nf at *
    linarith
  have hc : c = 25.6 := by
    ring_nf at *
    linarith
  have hd : d = 32 := by
    ring_nf at *
    linarith
  exact ⟨ha, hb, hc, hd⟩