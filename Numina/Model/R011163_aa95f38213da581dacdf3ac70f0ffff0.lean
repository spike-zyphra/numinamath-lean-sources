import Mathlib

theorem algebra_16913 (x : ℝ) (hx : 3^(2*x) = Real.sqrt 27) :
    x = 3/4 := by
  have h1 : Real.sqrt 27 = (3 : ℝ) ^ (3 / 2 : ℝ) := by
    have h2 : Real.sqrt 27 = (27 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    have h3 : (27 : ℝ) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (3 / 2 : ℝ) := by
      have h4 : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
      rw [h4]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h2, h3]
  rw [h1] at hx
  have h2 : 2 * x = (3 / 2 : ℝ) := by
    apply_fun (Real.logb (3 : ℝ)) at hx
    have h3 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (2 * x : ℝ)) = (2 * x : ℝ) := by 
      rw [Real.logb_rpow]
      all_goals norm_num
    have h4 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (3 / 2 : ℝ)) = (3 / 2 : ℝ) := by 
      rw [Real.logb_rpow]
      all_goals norm_num
    rw [h3, h4] at hx
    all_goals linarith
  linarith