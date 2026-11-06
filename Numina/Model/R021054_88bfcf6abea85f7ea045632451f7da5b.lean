import Mathlib

theorem number_theory_199882 (a b c d e f : ℕ) (h₀ : a ≠ 0) (h₁ : 37 ∣ (100 * a + 10 * b + c) + (100 * d + 10 * e + f)) :
    37 ∣ (100000 * a + 10000 * b + 1000 * c + 100 * d + 10 * e + f) := by 
  omega