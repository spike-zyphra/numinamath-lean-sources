import Mathlib

theorem number_theory_203443 (A B C : ℕ) (h₀ : A ≠ 0) (h₁ : 37 ∣ 100 * A + 10 * B + C) :
    37 ∣ (100 * B + 10 * C + A) + (100 * C + 10 * A + B) := by 
  omega