import Mathlib

theorem number_theory_9545 (A B : ℕ) (h₀ : A < 10) (h₁ : B < 10)
    (h₂ : 21 ∣ (4935200 + 100 * A + 10 * B + 610 + 200 + 10 * A + B + 620 + 20 + 2)) :
    A * B ≥ 4 := by 
  interval_cases A <;> interval_cases B <;> omega