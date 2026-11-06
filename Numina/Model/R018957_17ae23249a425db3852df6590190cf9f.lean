import Mathlib

open Real

theorem algebra_10227 : logb 3 (1 / √3) = -1 / 2 := by
  have h1 : (1 / √3 : ℝ) = (3 : ℝ) ^ (-1 / 2 : ℝ) := by
    have h2 : √3 = (3 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h2]
    have h3 : (1 / ( (3 : ℝ) ^ (1 / 2 : ℝ) ) ) = (3 : ℝ) ^ (-1 / 2 : ℝ) := by
      have h4 : (3 : ℝ) ^ (-1 / 2 : ℝ) = ( (3 : ℝ) ^ (1 / 2 : ℝ) )⁻¹ := by
        rw [show (-1 / 2 : ℝ) = - (1 / 2 : ℝ) by ring]
        rw [Real.rpow_neg]
        all_goals norm_num
      rw [h4]
      field_simp
    linarith [h3]
  rw [h1]
  have h4 : logb (3 : ℝ) ((3 : ℝ) ^ (-1 / 2 : ℝ)) = -1 / 2 := by
    rw [logb_rpow]
    all_goals norm_num
  exact h4