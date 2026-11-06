import Mathlib

theorem algebra_187751 : Real.sqrt (6 + Real.sqrt 20) - Real.sqrt (6 - Real.sqrt 20) = 2 := by

  have h1 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h2 : Real.sqrt (6 + Real.sqrt 20) = 1 + Real.sqrt 5 := by
    rw [h1]
    have h3 : Real.sqrt (6 + 2 * Real.sqrt 5) = 1 + Real.sqrt 5 := by
      have h4 : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
      have h5 : Real.sqrt (6 + 2 * Real.sqrt 5) = Real.sqrt ((1 + Real.sqrt 5) ^ 2) := by
        rw [h4]
      rw [h5]
      have h6 : Real.sqrt ((1 + Real.sqrt 5) ^ 2) = 1 + Real.sqrt 5 := by
        rw [Real.sqrt_sq_eq_abs]
        have h7 : 0 ≤ (1 + Real.sqrt 5 : ℝ) := by
          have h8 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
          nlinarith [h8]
        rw [abs_of_nonneg h7]
      rw [h6]
    exact h3

  have h2' : Real.sqrt (6 - Real.sqrt 20) = Real.sqrt 5 - 1 := by
    rw [h1]
    have h3 : Real.sqrt (6 - 2 * Real.sqrt 5) = Real.sqrt 5 - 1 := by
      have h4 : (1 - Real.sqrt 5 : ℝ) ^ 2 = 6 - 2 * Real.sqrt 5 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
      have h5 : Real.sqrt (6 - 2 * Real.sqrt 5) = Real.sqrt ((1 - Real.sqrt 5) ^ 2) := by
        rw [h4]
      rw [h5]
      have h6 : Real.sqrt ((1 - Real.sqrt 5) ^ 2) = Real.sqrt 5 - 1 := by
        rw [Real.sqrt_sq_eq_abs]
        have h7 : (1 - Real.sqrt 5 : ℝ) < 0 := by
          have h8 : Real.sqrt 5 > 1 := by
            have h9 : Real.sqrt 5 > Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
            have h10 : Real.sqrt 1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
            linarith [h9, h10]
          nlinarith [Real.sqrt_nonneg 5]
        rw [abs_of_neg h7]
        all_goals
        nlinarith [Real.sqrt_nonneg 5]
      rw [h6]
    exact h3

  rw [h2, h2']
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]