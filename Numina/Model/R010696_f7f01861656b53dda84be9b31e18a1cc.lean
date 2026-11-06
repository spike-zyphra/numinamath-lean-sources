import Mathlib

theorem algebra_20040 (pence farthings shillings pounds : ℕ)
    (h₀ : 4 * farthings = 1 * pence) (h₁ : 12 * pence = 1 * shillings)
    (h₂ : 20 * shillings = 1 * pounds) :
    1 * pounds + 5 * pence = 980 * farthings := by

  omega