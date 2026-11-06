import Mathlib

theorem number_theory_238265 (a b c d e : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : a ≠ e) (h₄ : b ≠ c) (h₅ : b ≠ d) (h₆ : b ≠ e) (h₇ : c ≠ d) (h₈ : c ≠ e)
    (h₉ : d ≠ e) (h₁₀ : a + b + c = 10) (h₁₁ : a + b + d = 14) (h₁₂ : a + b + e = 15)
    (h₁₃ : a + c + d = 16) (h₁₄ : a + c + e = 17) (h₁₅ : a + d + e = 17) (h₁₆ : b + c + d = 18)
    (h₁₇ : b + c + e = 21) (h₁₈ : b + d + e = 22) (h₁₉ : c + d + e = 24) :
    a = 10 ∧ b = 9 ∧ c = 5 ∧ d = 3 ∧ e = 2 := by
  have h21 : a = 10 := by
    omega
  have h22 : b = 9 := by
    omega
  have h23 : c = 5 := by
    omega
  have h24 : d = 3 := by
    omega
  have h25 : e = 2 := by
    omega
  simp [h21, h22, h23, h24, h25]
  all_goals tauto