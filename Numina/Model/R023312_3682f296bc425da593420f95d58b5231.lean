import Mathlib

theorem algebra_285854 (p m : ℕ) (h₀ : p = m + 2) (h₁ : m = p - 2)
    (h₂ : p - 4 = m) (h₃ : m + 3 = p) (h₄ : m + 12 = p) :
    p = 7 ∧ m = 7 := by
  omega