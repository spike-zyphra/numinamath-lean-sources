import Mathlib

theorem algebra_133417 (a m : ℕ) (h₀ : a - 6 = 5 * (m - 6)) (h₁ : a = 3 * m) :
    ∃ x, a + x = 2 * (m + x) := by 
  use m
  omega