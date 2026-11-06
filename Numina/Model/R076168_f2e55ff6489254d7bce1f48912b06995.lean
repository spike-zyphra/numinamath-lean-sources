import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_313413 (a : ℝ) (ha : 1 < a) :
    logb a 16 + 2 * logb 4 a ≥ 4 := by

  have h1 : logb a 16 = 4 / logb 2 a := by
    have h1 : logb a 16 = logb 2 16 / logb 2 a := by 
      field_simp [logb]
    have h2 : logb 2 16 = 4 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h1, h2]

  have h2 : 2 * logb 4 a = logb 2 a := by
    have h3 : logb 4 a = logb 2 a / logb 2 4 := by 
      field_simp [logb]
    have h4 : logb 2 4 = 2 := by 
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    rw [h3, h4]
    <;> ring
  
  have h3 : logb a 16 + 2 * logb 4 a = 4 / logb 2 a + logb 2 a := by 
    rw [h1, h2]
  
  have h4 : 0 < logb 2 a := by
    apply logb_pos
    all_goals linarith
  
  have h5 : 4 / logb 2 a + logb 2 a ≥ 4 := by
    have h6 : logb 2 a > 0 := h4
    have h7 : 4 / logb 2 a + logb 2 a - 4 ≥ 0 := by
      have h8 : logb 2 a > 0 := h4
      have h9 : (logb 2 a - 2) ^ 2 ≥ 0 := by
        exact sq_nonneg (logb 2 a - 2)
      have h10 : 4 / logb 2 a + logb 2 a - 4 = (logb 2 a - 2) ^ 2 / logb 2 a := by
        field_simp
        <;> ring
      rw [h10]
      apply div_nonneg
      linarith [h9]
      all_goals linarith [h4]
    linarith
  
  linarith [h3, h5]