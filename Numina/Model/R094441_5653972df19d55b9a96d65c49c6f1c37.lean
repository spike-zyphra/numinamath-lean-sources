import Mathlib

theorem algebra_199213 (x : ℝ) :
    4*x^4 + 12*x^3 + 5*x^2 - 6*x - 15 = 0 ↔ x = 1 ∨ x = -2.5 := by
  constructor
  · -- Assume 4*x^4 + 12*x^3 + 5*x^2 - 6*x - 15 = 0, prove x = 1 ∨ x = -2.5
    intro h
    have h1 : 4*x^4 + 12*x^3 + 5*x^2 - 6*x - 15 = (x - 1) * (2*x + 5) * (2*x^2 + 3*x + 3) := by ring
    rw [h1] at h
    cases' (mul_eq_zero.mp h) with h2 h3
    · -- Case where either (x - 1) = 0 or (2x + 5) = 0
      cases' (mul_eq_zero.mp h2) with h4 h5
      · -- Case x - 1 = 0
        left
        linarith
      · -- Case 2x + 5 = 0
        right
        have h6 : x = -5/2 := by linarith
        rw [h6]
        norm_num
    · -- Case where $2x^2 + 3x + 3 = 0$
      have : (2 : ℝ) * x ^ 2 + 3 * x + 3 = 0 := by linarith
      have h4 : (2 : ℝ) * (x + 3/4)^2 + 15/8 = 0 := by nlinarith
      have h5 : (2 : ℝ) * (x + 3/4)^2 ≥ 0 := by
        nlinarith [sq_nonneg (x + 3/4)]
      have h6 : (2 : ℝ) * (x + 3/4)^2 + 15/8 > (0 : ℝ) := by
        nlinarith [sq_nonneg (x + 3/4)]
      nlinarith
  · -- Assume x = 1 ∨ x = -2.5, prove 4*x^4 + 12*x^3 + 5*x^2 - 6*x - 15 = 0
    rintro (h | h)
    · -- Case x = 1
      rw [h]
      norm_num
    · -- Case x = -2.5
      rw [h]
      norm_num