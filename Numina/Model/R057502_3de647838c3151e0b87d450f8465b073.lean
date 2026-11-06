import Mathlib

theorem algebra_141113 (m : ℤ) (h₀ : m ≥ 10) (h₁ : (m + 10) * 2 = 22 * 3 + 32) (h₂ : (m - 8) * 2 = 22 * 3 + 32 - 16) :
    m = 20 := by
  omega -- This should solve the arithmetic constraints.