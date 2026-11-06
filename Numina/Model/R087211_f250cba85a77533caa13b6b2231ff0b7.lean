import Mathlib

theorem algebra_190104 (x y : ℕ) (h₀ : x * 36 + y * 2 = 716) (h₁ : x * 6 + y * (2 * 36) = 716 - 4) :
    x = 8 ∧ y = 6 := by
  omega