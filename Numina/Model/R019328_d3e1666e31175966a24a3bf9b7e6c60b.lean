import Mathlib

theorem algebra_175335 (a b c d : ℤ) (h₀ : |a - b| = 2) (h₁ : |b - c| = 3) (h₂ : |c - d| = 4) :
    |a - d| ≠ 7 := by
  by_contra h
  have h3 : a - b = 2 ∨ a - b = -2 := by 
    cases' eq_or_eq_neg_of_abs_eq h₀ with h4 h5
    · left
      linarith
    · right
      linarith
  have h4 : b - c = 3 ∨ b - c = -3 := by 
    cases' eq_or_eq_neg_of_abs_eq h₁ with h5 h6
    · left
      linarith
    · right
      linarith
  have h5 : c - d = 4 ∨ c - d = -4 := by 
    cases' eq_or_eq_neg_of_abs_eq h₂ with h6 h7
    · left
      linarith
    · right
      linarith
  have h6 : a - d = 7 ∨ a - d = -7 := by 
    cases' abs_cases (a - d) with h7 h7
    · omega
    · omega
  omega