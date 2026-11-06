import Mathlib

theorem algebra_244997 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (10 * n + 3) = 27 * (2 * n)) : n = 24 := by
  omega