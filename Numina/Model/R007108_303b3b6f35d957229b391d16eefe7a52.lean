import Mathlib

theorem algebra_12409 (p n d q : ℕ) (h₀ : (p + n + d + q) * 20 = p * 1 + n * 5 + d * 10 + q * 25)
    (h₁ : (p + n + d + q + 1) * 21 = p * 1 + n * 5 + d * 10 + (q + 1) * 25) :
    d = 0 := by
  omega