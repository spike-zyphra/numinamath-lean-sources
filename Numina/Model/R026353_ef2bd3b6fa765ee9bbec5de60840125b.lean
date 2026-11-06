import Mathlib

theorem number_theory_204388 (A B C D E : ℕ) (h₀ : A ≠ 0) (h₁ : 41 ∣ (10000 * A + 1000 * B + 100 * C + 10 * D + E)) :
    41 ∣ (10000 * E + 1000 * A + 100 * B + 10 * C + D) := by
  omega