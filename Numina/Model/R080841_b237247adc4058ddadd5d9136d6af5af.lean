import Mathlib

theorem number_theory_229743 (a b c : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : a ≠ b) (h₄ : a ≠ c) (h₅ : b ≠ c) (h₆ : a + b + c = 7) :
    a * b * c = 8 := by
  have h7 : a ≤ 7 := by omega
  have h8 : b ≤ 7 := by omega
  have h9 : c ≤ 7 := by omega
  interval_cases a <;> interval_cases b <;> omega