import Mathlib

theorem number_theory_233855 (a b : ℕ) (h₀ : 0 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9)
    (h₂ : 99 ∣ (20160000 + 1000 * a + 100 * b + 2017)) :
    a + b = 8 := by
  have h3 : a ≤ 9 := by 
    omega
  have h4 : b ≤ 9 := by 
    omega
  interval_cases a <;> interval_cases b <;> omega