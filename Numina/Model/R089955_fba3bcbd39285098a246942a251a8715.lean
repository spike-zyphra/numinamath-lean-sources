import Mathlib

theorem algebra_317777 (x : ℝ) :
    x ^ 4 - 6 * x ^ 3 + 10 * x ^ 2 - 4 * x = 0 ↔
    x = 2 + Real.sqrt 2 ∨ x = 2 - Real.sqrt 2 ∨ x = 0 ∨ x = 2 := by
  constructor
  · -- Assume polynomial equals zero, prove equivalence
    intro h
    have h1 : x * (x ^ 3 - 6 * x ^ 2 + 10 * x - 4) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 4 * x + 2), sq_nonneg (x - 2), sq_nonneg (x * (x - 2)), sq_nonneg (x * (x ^ 2 - 4 * x + 2)), sq_nonneg (x ^ 3 - 6 * x ^ 2 + 10 * x - 4)]
    cases' (mul_eq_zero.1 h1) with h2 h3
    · -- Case where x = 0
      right
      right
      left
      linarith
    · -- Case where x^3 - 6x^2 + 10 x - 4 = 0
      have h4 : (x - 2) * (x ^ 2 - 4 * x + 2) = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 4 * x + 2), sq_nonneg (x - 2), sq_nonneg (x * (x - 2)), sq_nonneg (x * (x ^ 2 - 4 * x + 2)), sq_nonneg (x ^ 3 - 6 * x ^ 2 + 10 * x - 4)]
      cases' (mul_eq_zero.1 h4) with h5 h6
      · -- Case where x - 2 = 0
        right
        right
        right
        linarith
      · -- Case where x^2 - 4 x + 2 = 0
        have h7 : x ^ 2 - 4 * x + 2 = 0 := h6
        have h8 : (x - (2 + Real.sqrt 2)) * (x - (2 - Real.sqrt 2)) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 2), sq_nonneg (x * (x - 2)), sq_nonneg ((x - 2) ^ 2 - 2)]
        cases' (mul_eq_zero.1 h8) with h9 h10
        · -- Case where x - (2 + Real.sqrt 2) = 0
          left
          linarith
        · -- Case where x - (2 - Real.sqrt 2) = 0
          right
          left
          linarith
  · -- Assume x equals one of the solutions, prove polynomial equals zero
    rintro (h | h | h | h)
    · -- When x = 2 + Real.sqrt 2
      rw [h]
      have h1 : (2 + Real.sqrt 2) ^ 2 - 4 * (2 + Real.sqrt 2) + 2 = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      nlinarith [sq_nonneg ((2 + Real.sqrt 2) ^ 2 - 4 * (2 + Real.sqrt 2) + 2), sq_nonneg ((2 + Real.sqrt 2) * ((2 + Real.sqrt 2) - 2)), sq_nonneg ((2 + Real.sqrt 2) - 2)]
    · -- When x = 2 - Real.sqrt 2
      rw [h]
      have h1 : (2 - Real.sqrt 2) ^ 2 - 4 * (2 - Real.sqrt 2) + 2 = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      nlinarith [sq_nonneg ((2 - Real.sqrt 2) ^ 2 - 4 * (2 - Real.sqrt 2) + 2), sq_nonneg ((2 - Real.sqrt 2) * ((2 - Real.sqrt 2) - 2)), sq_nonneg ((2 - Real.sqrt 2) - 2)]
    · -- When x = 0
      rw [h]
      norm_num
    · -- When x = 2
      rw [h]
      norm_num