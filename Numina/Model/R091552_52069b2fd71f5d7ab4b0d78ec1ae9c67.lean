import Mathlib

theorem number_theory_193555 (A B : ℕ) (h₀ : 0 < A) (h₁ : 0 < B)
    (h₂ : A < 10) (h₃ : B < 10) (h₄ : 210000000 + 100000 * A + 104 * 11 = 200000 * B + 8016 * 9) :
    A = 1 ∧ B = 5 := by
  interval_cases A <;> interval_cases B <;> omega