import Mathlib

open Real

theorem inequalities_119257 : ∑ i ∈ Finset.range 11, (sqrt (122 + i) % 1) < 3 := by
  norm_num [Finset.sum_range_succ]
  all_goals
    nlinarith [Real.sqrt_nonneg 122, Real.sqrt_nonneg 123, Real.sqrt_nonneg 124, Real.sqrt_nonneg 125, Real.sqrt_nonneg 126, Real.sqrt_nonneg 127, Real.sqrt_nonneg 128, Real.sqrt_nonneg 129, Real.sqrt_nonneg 130, Real.sqrt_nonneg 131, Real.sqrt_nonneg 132, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (122 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (123 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (124 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (125 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (126 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (127 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (128 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (129 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (130 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (131 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (132 : ℝ) by norm_num),
        sq_nonneg (sqrt 122 - 11), sq_nonneg (sqrt 123 - 11), sq_nonneg (sqrt 124 - 11), sq_nonneg (sqrt 125 - 11), sq_nonneg (sqrt 126 - 11), sq_nonneg (sqrt 127 - 11), sq_nonneg (sqrt 128 - 11), sq_nonneg (sqrt 129 - 11), sq_nonneg (sqrt 130 - 11), sq_nonneg (sqrt 131 - 11), sq_nonneg (sqrt 132 - 11)
        ]