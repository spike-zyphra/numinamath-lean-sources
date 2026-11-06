import Mathlib
open Real

theorem algebra_98389 (a b : ℝ) (ha : a = logb 10 2) (hb : b = logb 10 3) :
logb 5 12 = (2 * a + b) / (1 - a) := by 
  have h1 : logb 5 12 = logb 10 12 / logb 10 5 := by 
    field_simp [logb]
    all_goals linarith 
  have h2 : logb 10 12 = 2 * a + b := by
    have h5 : logb 10 12 = logb 10 4 + logb 10 3 := by 
      rw [show (12 : ℝ) = 4 * 3 by norm_num]
      rw [logb_mul (by norm_num) (by norm_num)]
    have h6 : logb 10 4 = 2 * logb 10 2 := by 
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      simp [logb_pow]
      all_goals norm_num
    rw [h5, h6]
    rw [ha, hb]
    all_goals norm_num
    <;> linarith
  have h3 : logb 10 5 = 1 - a := by
    have h4 : logb 10 5 = logb 10 (10 / 2) := by 
      norm_num
    rw [h4]
    rw [logb_div (by norm_num) (by norm_num)]
    simp [logb_self_eq_one, ha]
    all_goals norm_num
    <;> linarith
  rw [h1]
  rw [h2, h3]
  all_goals norm_num
  <;> field_simp [ha, hb]
  <;> ring