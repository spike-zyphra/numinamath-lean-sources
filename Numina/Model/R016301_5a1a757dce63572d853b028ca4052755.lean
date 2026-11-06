import Mathlib

open Real

theorem algebra_99256 {a b : ℝ}
    (ha : a = ⌊logb 2 (sqrt 5 + 1)⌋^3) (hb : b = 1 + logb 2 (sqrt 5 + 2)) :
    b > a := by

  have h1 : ⌊logb 2 (sqrt 5 + 1)⌋ = 1 := by
    have h2 : 1 < (Real.sqrt 5 + 1 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h3 : (Real.sqrt 5 + 1 : ℝ) < (4 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2 : ℝ)]
    have h4 : 1 < logb 2 (sqrt 5 + 1) := by
      have h5 : logb 2 (sqrt 5 + 1) > logb 2 (2 : ℝ) := by
        apply Real.logb_lt_logb
        all_goals
          nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h6 : logb 2 (2 : ℝ) = 1 := by
        rw [logb_self_eq_one]
        all_goals linarith
      linarith [h5, h6]
    have h5 : logb 2 (sqrt 5 + 1) < (2 : ℝ) := by
      have h6 : logb 2 (sqrt 5 + 1 : ℝ) < logb 2 (4 : ℝ) := by
        apply Real.logb_lt_logb
        all_goals
          nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h7 : logb 2 (4 : ℝ) = 2 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith [h6, h7]
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith [h4, h5]

  have ha1 : a = 1 := by
    rw [ha]
    rw [h1]
    norm_num
  have hb1 : b = 1 + logb 2 (sqrt 5 + 2) := by 
    linarith [hb]

  rw [hb1, ha1]

  have h6 : (sqrt 5 + 2 : ℝ) > (1 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h7 : logb 2 (sqrt 5 + 2) > 0 := by
    have h8 : logb 2 (sqrt 5 + 2) > logb 2 (1 : ℝ) := by
      apply Real.logb_lt_logb
      all_goals
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h9 : logb 2 (1 : ℝ) = 0 := by
      simp [logb_one]
    linarith [h8, h9]

  linarith [h7]