import Mathlib

theorem algebra_169456 :
    ∃ a b : ℝ, ∀ p q : ℝ, -(p / 2) ^ 2 + p * (p / 2) + q = (p / 2) ^ 2 → b = -a ^ 2 + p * a + q ∧ b = a ^ 2 := by 
  use 0, 0
  intro p q h
  have h1 : q = 0 := by 
    nlinarith 
  constructor
  · -- Show that 0 = -0 ^ 2 + p * 0 + q
    linarith [h1]
  · -- Show that 0 = (0) ^ 2
    nlinarith