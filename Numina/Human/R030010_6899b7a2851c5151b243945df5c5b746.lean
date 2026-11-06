import Mathlib

theorem number_theory_116544 (a b c d : ℕ) (h₀ : a ≠ 0) (h₁ : a ≤ 9) (h₂ : b ≤ 9)
    (h₃ : c ≤ 9) (h₄ : d ≤ 9) (h₅ : a + b + c + d = 27) :
    297 ∣ (1000 * a + 100 * b + 10 * c + d) + (1000 * d + 100 * c + 10 * b + a) := by 
  omega