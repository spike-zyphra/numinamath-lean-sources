import Mathlib

theorem number_theory_263812 (a b c : ℤ) (h₀ : a + b + c = 17 + 1967 + 1983) :
    (a = 3 ∧ b = 3 ∧ c = 5) ∨ ¬(a = 2 ∧ b = 2 ∧ c = 2) := by
  have h1 : a + b + c = 3967 := by 
    linarith
  by_cases h : a = 3 ∧ b = 3 ∧ c = 5
  · left
    exact h
  · right
    intro h2
    have ha2 : a = 2 := h2.1
    have hb2 : b = 2 := h2.2.1
    have hc2 : c = 2 := h2.2.2
    linarith