import Mathlib

theorem algebra_296931 (n m p : ℕ) (h₀ : n * 15000 + m * 10000 + p * 5000 = 1000000)
    (h₁ : p - n ≥ 93) (h₂ : p - n < 96) :
    n + m + p = 147 := by
  omega