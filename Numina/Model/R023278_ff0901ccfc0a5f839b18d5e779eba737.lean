import Mathlib

theorem algebra_179624 (a b c d : ℕ)
    (h₀ : a < 50) (h₁ : b < 50) (h₂ : c < 50) (h₃ : d < 50)
    (h₄ : (a + b + c + d) / 4 = 46)
    (h₅ : |(a : ℤ) - b| = 4)
    (h₆ : |(b : ℤ) - c| = 3)
    (h₇ : |(c : ℤ) - d| = 2)
    (h₈ : a > b ∧ a > c ∧ a > d) :
    a = 48 ∧ b = 44 ∧ c = 47 ∧ d = 45 := by
  have h9 : (a : ℤ) - b = 4 ∨ (a : ℤ) - b = -4 := by 
    cases' eq_or_eq_neg_of_abs_eq h₅ with h h
    · left
      linarith
    · right
      linarith
  have h9' : (a : ℤ) - b = 4 := by 
    omega
  have h10 : a = b + 4 := by 
    omega
  have h11 : (b : ℤ) - (c : ℤ) = 3 ∨ (b : ℤ) - (c : ℤ) = -3 := by 
    cases' eq_or_eq_neg_of_abs_eq h₆ with h h
    · left
      linarith
    · right
      linarith
  have h12 : (c : ℤ) - (d : ℤ) = 2 ∨ (c : ℤ) - (d : ℤ) = -2 := by 
    cases' eq_or_eq_neg_of_abs_eq h₇ with h h
    · left
      linarith
    · right
      linarith
  have h13 : a > b := h₈.1
  have h14 : a > c := h₈.2.1
  have h15 : a > d := h₈.2.2
  have h16 : b + 4 > c := by nlinarith [h10, h14]
  have h17 : b + 4 > d := by nlinarith [h10, h15]
  rcases h11 with h11 | h11
  · -- Case b - c = 3.
    have h18 : b = c + 3 := by
      omega
    rcases h12 with h12 | h12
    · -- Case b - c = 3 and c - d = 2.
      have h19 : c = d + 2 := by
        omega
      omega
    · -- Case b - c = 3 and c - d = -2.
      have h19 : d = c + 2 := by
        omega
      omega
  · -- Case b - c = -3.
    have h18 : c = b + 3 := by
      omega
    rcases h12 with h12 | h12
    · -- Case b - c = -3 and c - d = 2.
      have h19 : c = d + 2 := by
        omega
      omega
    · -- Case b - c = -3 and c - d = -2.
      have h19 : d = c + 2 := by
        omega
      omega