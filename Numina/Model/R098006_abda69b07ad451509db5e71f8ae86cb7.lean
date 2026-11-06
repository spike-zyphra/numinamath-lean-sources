import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_322765 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (h : logb 2 x + logb 2 y = 1) :
  x^2 + y^2 - 2 * (x + y) ≥ 4 - 4 * sqrt 2 ∧
  ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ logb 2 x + logb 2 y = 1 ∧
  x^2 + y^2 - 2 * (x + y) = 4 - 4 * sqrt 2 := by

  have h1 : x * y = 2 := by
    have h2 : logb 2 (x * y) = 1 := by
      have h0 : logb 2 (x * y) = logb 2 x + logb 2 y := by
        rw [logb_mul (by linarith) (by linarith)]
      rw [h0]
      all_goals linarith
    have h3 : x * y = (2 : ℝ) ^ (1 : ℝ) := by
      rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by nlinarith)] at h2
      · linarith
      all_goals linarith
    norm_num at h3 ⊢
    all_goals nlinarith

  have h3 : x^2 + y^2 - 2 * (x + y) = (x + y) ^ 2 - 2 * (x + y) - 4 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 2),
        Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
        h1]

  have h4 : x + y ≥ 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 2),
        Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
        Real.sqrt_nonneg (2 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num),
        sq_nonneg (x * y - 2), h1]

  have h5 : (x + y) ^ 2 - 2 * (x + y) - 4 ≥ 4 - 4 * Real.sqrt 2 := by
    nlinarith [sq_nonneg ((x + y) - 2 * Real.sqrt 2), sq_nonneg (x - y),
        Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num),
        Real.sqrt_nonneg (2 : ℝ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num),
        sq_nonneg (x * y - 2), h1]

  have h6 : x^2 + y^2 - 2 * (x + y) ≥ 4 - 4 * Real.sqrt 2 := by
    linarith [h3, h5]

  have h7 : ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ logb 2 x + logb 2 y = 1 ∧
    x^2 + y^2 - 2 * (x + y) = 4 - 4 * Real.sqrt 2 := by
    use Real.sqrt 2, Real.sqrt 2
    constructor
    · -- Show sqrt(2) > 0
      positivity
    constructor
    · -- Show sqrt(2) > 0
      positivity
    constructor
    · -- Show log_2(sqrt(2)) + log_2(sqrt(2)) = 1
      have h8 : logb 2 (Real.sqrt 2) = 1 / 2 := by
        rw [Real.sqrt_eq_rpow]
        simp [logb_rpow]
        all_goals norm_num
      rw [h8]
      all_goals linarith
    · -- Show (sqrt(2)) ^ 2 + (sqrt(2)) ^ 2 - 2 * (sqrt(2) + sqrt(2)) = 4 - 4 * sqrt(2)
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  constructor
  · linarith [h6]
  · exact h7