import Mathlib

theorem algebra_12661 (x y : ℝ) (h : (x + 2) ^ 2 + y ^ 2 = 1) :
    y / x ≤ Real.sqrt 3 / 3 ∧ ∃ x y, (x + 2) ^ 2 + y ^ 2 = 1 ∧ y / x = Real.sqrt 3 / 3 := by

  have h1 : y / x ≤ Real.sqrt 3 / 3 := by
    by_cases h2 : x > 0
    · -- Assume x > 0
      have h3 : y ≤ Real.sqrt 3 / 3 * x := by
        nlinarith [sq_nonneg (y - Real.sqrt 3 / 2), sq_nonneg (x - (-3 / 2)), 
          sq_nonneg (y - Real.sqrt 3 / 3 * x), sq_nonneg (y + Real.sqrt 3 / 2), sq_nonneg (x + 3 / 2), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have h4 : y / x ≤ Real.sqrt 3 / 3 := by
        apply (div_le_iff₀ (by linarith)).mpr
        linarith
      linarith
    · -- Assume x ≤ 0
      by_cases h3 : x < 0
      · -- Assume x < 0
        have h30 : y ≥ Real.sqrt 3 / 3 * x := by
          nlinarith [sq_nonneg (y - Real.sqrt 3 / 2), sq_nonneg (x - (-3 / 2)), 
            sq_nonneg (y - Real.sqrt 3 / 3 * x), sq_nonneg (y + Real.sqrt 3 / 2), sq_nonneg (x + 3 / 2), 
            Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
        have h4 : y / x ≤ Real.sqrt 3 / 3 := by
          apply (div_le_iff_of_neg' (by linarith)).mpr
          nlinarith
        linarith
      · -- Assume x ≥ 0
        have h4 : x = 0 := by linarith
        rw [h4] at h
        have h5 : y ^ 2 ≤ 0 := by nlinarith
        have h6 : y = 0 := by
          nlinarith [sq_nonneg y]
        rw [h4, h6]
        norm_num
        all_goals
          linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  constructor
  · exact h1
  · -- Show the existence of a point
    use -3 / 2, -Real.sqrt 3 / 2
    constructor
    · -- Show $(-3/2+2) ^ 2 + (-\sqrt 3/2) ^ 2 = 1$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    · -- Show $ y/x = (\sqrt 3)/3 $
      field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      all_goals nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]