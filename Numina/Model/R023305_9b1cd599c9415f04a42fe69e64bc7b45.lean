import Mathlib

open Real

theorem algebra_18915 {x : ℝ} (hx : x = 64 * sqrt 8) :
    logb (sqrt 8) x = 5 := by
  rw [hx]
  have h1 : sqrt 8 = (8 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have h2 : (64 * sqrt 8 : ℝ) = (8 : ℝ) ^ (5 / 2 : ℝ) := by
    have h3 : sqrt 8 = (8 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    have h4 : (64 * sqrt 8 : ℝ) = (8 : ℝ) ^ (2 : ℝ) * (8 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [h3]
      have h6 : (64 : ℝ) = (8 : ℝ) ^ (2 : ℝ) := by
        norm_num
      rw [h6]
      all_goals ring
    have h7 : (8 : ℝ) ^ (2 : ℝ) * (8 : ℝ) ^ (1 / 2 : ℝ) = (8 : ℝ) ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_add]
      norm_num
      all_goals norm_num
    linarith [h4, h7]
  rw [h2, h1]
  have h4 : logb ((8 : ℝ) ^ (1 / 2 : ℝ)) ((8 : ℝ) ^ (5 / 2 : ℝ)) =
    Real.log ((8 : ℝ) ^ (5 / 2 : ℝ)) / Real.log ((8 : ℝ) ^ (1 / 2 : ℝ)) := by
    field_simp [logb]
  rw [h4]
  have h5 : Real.log ((8 : ℝ) ^ (5 / 2 : ℝ)) = (5 / 2 : ℝ) * Real.log (8 : ℝ) := by
    rw [Real.log_rpow]
    all_goals norm_num
  have h6 : Real.log ((8 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log (8 : ℝ) := by
    rw [Real.log_rpow]
    all_goals norm_num
  rw [h5, h6]
  have h7 : Real.log (8 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h13 : Real.log (8 : ℝ) ≠ 0 := by linarith
  field_simp [h13]
  all_goals linarith