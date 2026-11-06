import Mathlib

theorem number_theory_1079 (a b c : ℕ) (h₀ : 0 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9) (h₂ : 0 ≤ c ∧ c ≤ 9)
(h₃ : 11 ∣ (2010888000 + 100 * a + 10 * b + c)) :
100 * a + 10 * b + c ≤ 990 := by 
  omega