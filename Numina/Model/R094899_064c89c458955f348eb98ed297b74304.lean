import Mathlib

theorem algebra_284199 (a b c d : ℕ) (h₀ : a + b + c + d = 2020)
    (h₁ : a ≥ 103) (h₂ : b ≥ 103) (h₃ : c ≥ 103) (h₄ : d ≥ 103)
    (h₅ : a > b) (h₆ : a > c) (h₇ : a > d) (h₈ : b + c = 1277) :
    a = 640 := by
  omega