import Mathlib

theorem inequalities_217395 (a b c d : ℝ) (h₀ : a + b + c ≥ d) (h₁ : a + b + d ≥ c)
    (h₂ : a + c + d ≥ b) (h₃ : b + c + d ≥ a) :
    ¬(c < 0 ∧ d < 0 ∧ a < 0 ∧ b < 0) := by 
  intro h
  have hc : c < 0 := h.1
  have hd : d < 0 := h.2.1
  have ha : a < 0 := h.2.2.1
  have hb : b < 0 := h.2.2.2

  have h4 : a + b + c + d < 0 := by linarith
  have h5 : (a + b + c) + (a + b + d) + (a + c + d) + (b + c + d) ≥ d + c + b + a := by 
    linarith [h₀, h₁, h₂, h₃]

  have h6 : (a + b + c) + (a + b + d) + (a + c + d) + (b + c + d) = 3 * (a + b + c + d) := by 
    ring

  linarith [h5, h6, h4]