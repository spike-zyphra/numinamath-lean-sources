import Mathlib

theorem number_theory_167437 (A B C : ℕ) (h₀ : A > 0) (h₁ : A ≤ 9) (h₂ : B ≤ 9) (h₃ : C ≤ 9)
    (h₄ : 100 * A + 10 * B + C = B ^ C - A) : 100 * A + 10 * B + C = 127 := by 
  interval_cases A <;> interval_cases B <;> interval_cases C <;> omega