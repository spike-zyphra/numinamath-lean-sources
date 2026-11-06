import Mathlib

theorem algebra_328022 {x : ℝ} (h : x = (x^2 + 3 * x - 2)^2 + 3 * (x^2 + 3 * x - 2) - 2) :
    x = -1 + Real.sqrt 3 ∨ x = -2 + Real.sqrt 2 ∨ x = -1 - Real.sqrt 3 ∨ x = -2 - Real.sqrt 2 := by
  have h1 : (x^2 + 4 * x + 2) * (x^2 + 2 * x - 2) = 0 := by
    nlinarith [sq_nonneg (x^2 + 3 * x - 2 + 1), sq_nonneg (x + 2), sq_nonneg (x + 1), sq_nonneg (x^2 + 3 * x - 2 - x), sq_nonneg (x + 1 - x^2 - 3 * x + 2)]
  cases' (mul_eq_zero.mp h1) with h2 h3
  · -- Case h2 : x^2 + 4 * x + 2 = 0
    have h4 : x^2 + 4 * x + 2 = 0 := h2
    have h5 : (x - (-2 + Real.sqrt 2)) * (x - (-2 - Real.sqrt 2)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- Case h6 : x - (-2 + Real.sqrt 2) = 0
      right
      left
      linarith
    · -- Case h7 : x - (-2 - Real.sqrt 2) = 0
      right
      right
      right
      linarith
  · -- Case h3 : x^2 + 2 * x - 2 = 0
    have h6 : x^2 + 2 * x - 2 = 0 := h3
    have h7 : (x - (-1 + Real.sqrt 3)) * (x - (-1 - Real.sqrt 3)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case h8 : x - (-1 + Real.sqrt 3) = 0
      left
      linarith
    · -- Case h9 : x - (-1 - Real.sqrt 3) = 0
      right
      right
      left
      linarith