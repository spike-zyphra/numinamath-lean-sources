import Mathlib

theorem number_theory_269648 (n dimes quarters : ℕ) (h₀ : dimes > quarters) (h₁ : n = dimes + quarters)
    (h₂ : 10 * dimes + 25 * quarters = 265) :
    n ≥ 16 := by
  omega