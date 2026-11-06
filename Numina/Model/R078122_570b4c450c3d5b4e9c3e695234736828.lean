import Mathlib

theorem algebra_109187 (x : ℤ) : x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3 ↔ x = 3 := by
  constructor
  · -- Assume x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3, prove x = 3
    intro h
    have h1 : x ^ 3 + (x + 1) ^ 3 + (x + 2) ^ 3 - (x + 3) ^ 3 = 0 := by
      linarith
    have h2 : (x - 3) * (x ^ 2 + 3 * x + 3) = 0 := by
      nlinarith [h1, sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (x + 3), sq_nonneg (x - 3)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where x - 3 = 0, so x = 3
      omega
    · -- Case where x^2 + 3x + 3 = 0
      have h5 : x ^ 2 + 3 * x + 3 = 0 := by
        nlinarith
      -- Proving that this is impossible by showing that the left side is positive.
      have h6 : x ^ 2 + 3 * x + 3 > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      -- Contradiction.
      linarith
  · -- Assume x = 3, prove x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3
    rintro rfl
    norm_num