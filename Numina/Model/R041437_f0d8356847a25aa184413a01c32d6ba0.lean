import Mathlib

open Real

theorem inequalities_171216 (x : ℝ) :
    x^2 * (x + 3 * sqrt 5) + 5 * (3 * x + sqrt 5) > 0 ↔ x > -sqrt 5 := by
  constructor
  · -- Assume the inequality holds, prove x > -sqrt 5.
    intro h
    have h1 : x^2 * (x + 3 * sqrt 5) + 5 * (3 * x + sqrt 5) =
        (x + sqrt 5) * (x^2 + 2 * sqrt 5 * x + 5) := by 
      have h2 : (sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h3 : (sqrt 5 : ℝ) ^ 4 = 25 := by
        calc
          (sqrt 5 : ℝ) ^ 4 = ((sqrt 5 : ℝ) ^ 2) ^ 2 := by ring
          _ = 5^2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
          _ = 25 := by norm_num
      nlinarith [h2, h3, sq_nonneg (x * (sqrt 5)), sq_nonneg (x + sqrt 5), Real.sqrt_nonneg 5]
    have h2 : (x + sqrt 5) * (x^2 + 2 * sqrt 5 * x + 5) > 0 := by
      linarith [h1, h]
    -- Show quadratic factor is ≥ 0.
    have h3 : x^2 + 2 * sqrt 5 * x + 5 ≥ 0 := by 
      have h4 : x^2 + 2 * sqrt 5 * x + 5 = (x + sqrt 5) ^ 2 := by
        have h2 : (sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        have h3 : (sqrt 5 : ℝ) ^ 4 = 25 := by
          calc
            (sqrt 5 : ℝ) ^ 4 = ((sqrt 5 : ℝ) ^ 2) ^ 2 := by ring
            _ = 5^2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            _ = 25 := by norm_num
        nlinarith [h2, h3, sq_nonneg (x * (sqrt 5)), sq_nonneg (x + sqrt 5), Real.sqrt_nonneg 5]
      rw [h4]
      have h5 : (x + sqrt 5) ^ 2 ≥ 0 := by 
        positivity
      linarith
    -- Contradiction if x ≤ -sqrt 5.
    by_contra h4
    push_neg at h4
    -- Then x + sqrt 5 ≤ 0.
    have h5 : (x + sqrt 5) ≤ 0 := by 
      nlinarith [Real.sqrt_nonneg 5, h4, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    -- Product ≤ 0 contradicts h2 > 0.
    nlinarith [h2, h3, h5, Real.sqrt_nonneg 5, sq_nonneg (x + sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- Assume x > -sqrt 5, prove the inequality.
    intro h
    have h1 : x^2 * (x + 3 * sqrt 5) + 5 * (3 * x + sqrt 5) =
        (x + sqrt 5) * (x^2 + 2 * sqrt 5 * x + 5) := by
      have h2 : (sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      have h3 : (sqrt 5 : ℝ) ^ 4 = 25 := by
        calc
          (sqrt 5 : ℝ) ^ 4 = ((sqrt 5 : ℝ) ^ 2) ^ 2 := by ring
          _ = 5^2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
          _ = 25 := by norm_num
      nlinarith [h2, h3, sq_nonneg (x * (sqrt 5)), sq_nonneg (x + sqrt 5), Real.sqrt_nonneg 5]
    -- Show quadratic factor is > 0.
    have h3 : x^2 + 2 * sqrt 5 * x + 5 > 0 := by 
      have h4 : x^2 + 2 * sqrt 5 * x + 5 = (x + sqrt 5) ^ 2 := by
        have h2 : (sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        have h3 : (sqrt 5 : ℝ) ^ 4 = 25 := by
          calc
            (sqrt 5 : ℝ) ^ 4 = ((sqrt 5 : ℝ) ^ 2) ^ 2 := by ring
            _ = 5^2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            _ = 25 := by norm_num
        nlinarith [h2, h3, sq_nonneg (x * (sqrt 5)), sq_nonneg (x + sqrt 5), Real.sqrt_nonneg 5]
      rw [h4]
      have h6 : (x + sqrt 5) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        by_contra h7
        have h8 : x = -sqrt 5 := by 
          nlinarith [Real.sqrt_nonneg 5, h7, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        nlinarith [h, h8, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      linarith
    -- Given x > -sqrt 5 implies (x + sqrt 5) > 0.
    have h4 : (x + sqrt 5) > 0 := by 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), h, sq_nonneg (x * (sqrt 5)), sq_nonneg (x + sqrt 5), Real.sqrt_nonneg 5]
    -- Product of positive and positive is positive.
    have h6 : (x + sqrt 5) * (x^2 + 2 * sqrt 5 * x + 5) > 0 := by 
      apply mul_pos 
      all_goals linarith [h4, h3, Real.sqrt_nonneg 5]
    -- Substitute factored form into the goal and prove > 0.
    linarith [h1, h6, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]