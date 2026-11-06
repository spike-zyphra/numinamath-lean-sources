import Mathlib

theorem algebra_222100 (n : ℕ) (h₀ : n > 0) (h₁ : n + 32 = 2 * (n / 2)) :
    24 ≤ n ∧ n ≤ 64 := by 
  omega