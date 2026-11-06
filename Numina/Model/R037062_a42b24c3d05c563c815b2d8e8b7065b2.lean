import Mathlib

open Real

theorem algebra_186632 : (arctan (2 + sqrt 5) + arctan (1 / (2 - sqrt 5))) < 5 * sqrt 7 / 4 := by
  have h1 : (2 - Real.sqrt 5) ≠ 0 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2)]
  have h2 : (1 / (2 - Real.sqrt 5) ) = - (2 + Real.sqrt 5) := by
    have h3 : (2 - Real.sqrt 5) ≠ 0 := h1
    field_simp [(show (2 - Real.sqrt 5) ≠ 0 by assumption)]
    <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt 5 - 2)]
  have h3 : arctan (1 / (2 - Real.sqrt 5)) = - (arctan (2 + Real.sqrt 5)) := by
    rw [h2]
    have : arctan (- (2 + Real.sqrt 5)) = - (arctan (2 + Real.sqrt 5)) := by 
      rw [show arctan (- (2 + Real.sqrt 5)) = - arctan (2 + Real.sqrt 5) by 
        rw [arctan_neg]
      ]
    linarith
  have h4 : arctan (2 + Real.sqrt 5) + arctan (1 / (2 - Real.sqrt 5)) = 0 := by
    linarith [h3]
  have h5 : (5 * Real.sqrt 7 / 4) > 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  linarith [h4, h5]