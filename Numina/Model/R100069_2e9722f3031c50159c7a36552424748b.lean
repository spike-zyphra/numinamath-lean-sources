import Mathlib

theorem algebra_261297 (n m : ℕ) (h₀ : n + m = 9) (h₁ : (3 * n + 2 * m) / 9 = 3)
    (h₂ : (3 * n + 5 * m) / 9 = 2) :
    n ≤ 4 := by 
  omega