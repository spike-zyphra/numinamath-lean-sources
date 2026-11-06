import Mathlib

theorem algebra_145261 (x : ℝ) :
    (x^2 + x + 3)^2 + 3 * (x^2 + x - 1) = 28 ↔ x = -2 ∨ x = 1 := by
  constructor
  · -- Assume the equation holds, prove x = -2 ∨ x = 1
    intro h
    have h1 : (x ^ 2 + x + 3) ^ 2 + 3 * (x ^ 2 + x - 1) - 28 = 0 := by linarith
    have h2 : (x - 1) * (x + 2) * (x^2 + x + 11) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 + x + 3), sq_nonneg (x ^ 2 + x - 1), sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x^2 + x + 11)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case where x - 1 = 0, so x = 1
      right
      linarith
    · -- Case where x + 2 = 0, so x = -2
      left
      linarith
    · -- Case where x^2 + x + 11 = 0
      have h7 : x^2 + x + 11 > 0 := by
        nlinarith [sq_nonneg (x + 1/2)]
      have h8 : x^2 + x + 11 ≠ 0 := by
        have h9 : x^2 + x + 11 > 0 := h7
        linarith
      contradiction
  · -- Assume x = -2 ∨ x = 1, prove the equation holds
    rintro (h | h)
    · -- Case where x = -2
      rw [h]
      norm_num
    · -- Case where x = 1
      rw [h]
      norm_num