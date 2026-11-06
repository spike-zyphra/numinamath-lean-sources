import Mathlib

open Real

theorem algebra_3213 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 0 → f (x ^ 2) = 3 / x + 3)
    (hf' : ∀ x, x < 0 → f (x ^ 2) = 3 / (-x) + 3) :
    f ((3 - 2 * sqrt 2) / 2) = 9 + 3 * sqrt 2 := by

  have h5 : ((sqrt 2 - 1) / (sqrt 2)) ^ 2 = (3 - 2 * sqrt 2) / 2 := by
    have h6 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
    have h7 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [h6, h7]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  
  have h6 : (sqrt 2 - 1) / (sqrt 2) ≥ 0 := by
    have h8 : sqrt 2 > 1 := by
      have h9 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    have h10 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
    apply div_nonneg
    · linarith [h8, Real.sqrt_nonneg 2]
    all_goals linarith [Real.sqrt_nonneg 2, h10]

  have h7 : f ( ( (sqrt 2 - 1) / (sqrt 2) ) ^ 2 ) = 3 / ( (sqrt 2 - 1 ) / (sqrt 2) ) + 3 := hf ( (sqrt 2 - 1) / (sqrt 2) ) (by linarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 - 1.0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)] )
  
  have h8 : ( (sqrt 2 - 1) / (sqrt 2) ) ^ 2 = (3 - 2 * sqrt 2) / 2 := h5
  
  rw [show (3 - 2 * sqrt 2) / 2 = ( (sqrt 2 - 1) / (sqrt 2) ) ^ 2 by linarith [h8] ]
  rw [ h7 ]
  have h9 : sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h10 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [h9, h10, show (sqrt 2 - 1 : ℝ) ≠ 0 by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ] ]
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 - 1.0), sq_nonneg (sqrt 2 ^ 2 - 2) ]