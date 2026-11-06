import Mathlib

theorem algebra_165540 (a b c : ℝ) (x : ℝ) :
    x^3 - (a + b + c)*x^2 + (a*b + a*c + b*c)*x - a*b*c = 0 ↔
    x = a ∨ x = b ∨ x = c := by
  constructor
  · -- Assume x^3 - (a + b + c)*x^2 + (a*b + a*c + b*c)*x - a*b*c = 0, prove x = a ∨ x = b ∨ x = c
    intro h
    have h1 : (x - a) * (x - b) * (x - c) = 0 := by
      nlinarith [sq_nonneg (x - a), sq_nonneg (x - b), sq_nonneg (x - c)]
    cases' (mul_eq_zero.mp h1) with h2 h3
    cases' mul_eq_zero.mp h2 with h4 h5
    · -- Case where x - a = 0
      left
      linarith
    · -- Case where x - b = 0
      right
      left
      linarith
    · -- Case where x - c = 0
      right
      right
      linarith
  · -- Assume x = a ∨ x = b ∨ x = c, prove x^3 - (a + b + c)*x^2 + (a*b + a*c + b*c)*x - a*b*c = 0
    rintro (h | h | h)
    · -- Case x = a
      rw [h]
      nlinarith
    · -- Case x = b
      rw [h]
      nlinarith
    · -- Case x = c
      rw [h]
      nlinarith