import Mathlib

theorem number_theory_108320 (n : ℕ) (h₀ : n ≠ 0) (h₁ : 29 * n % 250 = 67) (h₂ : 23 * n % 200 = 29) :
    n % 1000 = 123 := by
  have h3 : n % 250 = 123 := by
    omega
  have h4 : n % 200 = 123 := by
    omega
  omega