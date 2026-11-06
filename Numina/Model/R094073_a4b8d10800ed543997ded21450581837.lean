import Mathlib

theorem algebra_249486 (a : ℝ) (ha : a < 0) (h : 3 * a ^ 2 + (2 * a) ^ 2 = 28) :
    a = -2 := by
  have h1 : 7 * a ^ 2 = 28 := by
    linarith
  have h2 : a ^ 2 = 4 := by
    nlinarith
  have h3 : a = 2 ∨ a = -2 := by
    have h4 : a^2 - (4 : ℝ) = 0 := by linarith
    have h5 : (a - 2) * (a + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case where a - 2 = 0, so a = 2
      left
      linarith
    · -- Case where a + 2 = 0, so a = -2
      right
      linarith
  cases h3 with
  | inl h4 =>
    linarith
  | inr h5 =>
    linarith