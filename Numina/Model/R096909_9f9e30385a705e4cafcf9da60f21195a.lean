import Mathlib

theorem number_theory_319767 (a b c d e f : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9)
    (h₁ : 0 ≤ b ∧ b ≤ 9) (h₂ : 0 ≤ c ∧ c ≤ 9) (h₃ : 1 ≤ d ∧ d ≤ 9)
    (h₄ : 0 ≤ e ∧ e ≤ 9) (h₅ : 0 ≤ f ∧ f ≤ 9) (h₆ : 37 ∣ (a * 100 + b * 10 + c) +
    (d * 100 + e * 10 + f)) :
    37 ∣ (a * 100000 + b * 10000 + c * 1000 + d * 100 + e * 10 + f) := by 
  omega