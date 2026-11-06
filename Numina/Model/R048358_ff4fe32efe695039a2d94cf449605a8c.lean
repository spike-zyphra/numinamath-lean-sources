import Mathlib

open Matrix Finset

theorem algebra_115995 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : |(36 * b - 81 * a)| = 3) :
    a = 7 ∧ b = 3 := by 
  have h1 : 36 * b - 81 * a = 3 ∨ 36 * b - 81 * a = -3 := by
    cases' eq_or_eq_neg_of_abs_eq h with h1 h1
    · -- Case where 36 * b - 81 * a = 3
      left
      linarith
    · -- Case where 36 * b - 81 * a = -3
      right
      linarith
  cases h1 with
  | inl h_eq_3 =>
    have h_eq_3 : 36 * b - 81 * a = 3 := h_eq_3
    omega
  | inr h_eq_neg3 =>
    have h_eq_neg3 : 36 * b - 81 * a = -3 := h_eq_neg3
    omega