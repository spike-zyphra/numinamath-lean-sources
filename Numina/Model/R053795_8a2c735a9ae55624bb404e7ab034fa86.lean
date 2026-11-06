import Mathlib

theorem algebra_284298 (n m p : ℕ) (h₀ : n + m + p = 700)
    (h₁ : n * 7 = m * 4) (h₂ : n * 16 = m * 9 + p * 4) :
    p ≥ 75 := by
  omega