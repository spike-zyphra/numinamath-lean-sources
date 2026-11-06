import Mathlib

open Real

theorem algebra_293 {a b c : ℝ} (ha : a = sqrt 2 - 1) (hb : b = 2 * sqrt 2 - sqrt 6) (hc : c = sqrt 6 - 2) :
    b < a ∧ a < c := by 
  have h1 : b < a := by
    rw [hb, ha]
    have h3 : Real.sqrt 2 + 1 < Real.sqrt 6 := by 
      have h4 : (Real.sqrt 2 + 1 : ℝ) ^ 2 < (6 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
                  Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
                  Real.sqrt_nonneg 2, Real.sqrt_nonneg 6,
                  show Real.sqrt 2 < 3 / 2 by
                    have h6 : Real.sqrt 2 < (3 / 2 : ℝ) := by
                      rw [Real.sqrt_lt] <;> norm_num
                      <;> linarith
                    linarith]
      have h8 : (6 : ℝ) = (Real.sqrt 6) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h9 : Real.sqrt 2 + 1 < Real.sqrt 6 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, h8, h4, Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
      linarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h3, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
  have h2 : a < c := by 
    rw [ha, hc]
    have h3 : Real.sqrt 2 + 1 < Real.sqrt 6 := by 
      have h4 : (Real.sqrt 2 + 1 : ℝ) ^ 2 < (6 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
                  Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
                  Real.sqrt_nonneg 2, Real.sqrt_nonneg 6,
                  show Real.sqrt 2 < 3 / 2 by
                    have h6 : Real.sqrt 2 < (3 / 2 : ℝ) := by
                      rw [Real.sqrt_lt] <;> norm_num
                      <;> linarith
                    linarith]
      have h8 : (6 : ℝ) = (Real.sqrt 6) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h9 : Real.sqrt 2 + 1 < Real.sqrt 6 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, h8, h4, Real.sqrt_pos.mpr (show (6 : ℝ) > 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
      linarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h3, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num)]
  constructor
  · -- Show b < a
    linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h1]
  · -- Show a < c
    linarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, h2]