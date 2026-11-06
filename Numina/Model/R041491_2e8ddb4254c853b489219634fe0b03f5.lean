import Mathlib

theorem algebra_327600 (a b : ℝ) (h : 4 * a ^ 2 + 16 * b ^ 2 - 16 * a * b + 13 * a - 26 * b + 3 = 0) :
    a ^ 2 + b ^ 2 ≥ 1 / 80 := by

  have h2 : 4 * (a - 2 * b) ^ 2 + 13 * a - 26 * b + 3 = 0 := by
    nlinarith

  have h3 : (a - 2 * b) = -1/4 ∨ (a - 2 * b) = -3 := by
    have h4 : 4 * (a - 2 * b) ^ 2 + 13 * a - 26 * b + 3 = 0 := h2
    have h6 : 4 * (a - 2 * b) ^ 2 + 13 * a - 26 * b + 3 = 4 * (a - 2 * b) ^ 2 + 13 * (a - 2 * b) + 3 := by
      nlinarith
    rw [h6] at h4
    have h7 : (a - 2 * b + 1/4) * (a - 2 * b + 3) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case where a - 2b = -1/4
      left
      linarith
    · -- Case where a - 2b = -3
      right
      linarith

  cases h3 with
  | inl h4 =>
    have h5 : a = 2 * b - 1/4 := by
      linarith
    have h6 : a ^ 2 + b ^ 2 = 5 * b ^ 2 - b + 1 / 16 := by
      rw [h5]
      nlinarith
    have h7 : a ^ 2 + b ^ 2 ≥ 1 / 80 := by
      rw [h6]
      nlinarith [sq_nonneg (b - 1 / 10)]
    exact h7
  | inr h4 =>
    have h5 : a = 2 * b - 3 := by
      linarith
    have h6 : a ^ 2 + b ^ 2 = 5 * b ^ 2 - 12 * b + 9 := by
      rw [h5]
      nlinarith
    have h7 : a ^ 2 + b ^ 2 ≥ 1 / 80 := by
      rw [h6]
      nlinarith [sq_nonneg (b - 6 / 5)]
    exact h7