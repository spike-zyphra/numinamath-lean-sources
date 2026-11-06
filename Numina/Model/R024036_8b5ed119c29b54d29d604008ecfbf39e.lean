import Mathlib

theorem algebra_305091 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h₁ : (12 : ℝ)^x = 3) (h₂ : (12 : ℝ)^y = 2) :
    (8 : ℝ) ^ ((1 - 2 * x) / (1 - x + y)) = 4 / 3 := by

  have h3 : x = (Real.log 3) / (Real.log 12) := by
    have h4 : Real.log ((12 : ℝ) ^ x) = Real.log (3 : ℝ) := by
      rw [h₁]
    have h5 : Real.log ((12 : ℝ) ^ x) = x * Real.log 12 := by
      rw [Real.log_rpow]
      all_goals linarith
    rw [h5] at h4
    field_simp at *
    linarith
  have h4 : y = (Real.log 2) / (Real.log 12) := by
    have h5 : Real.log ((12 : ℝ) ^ y) = Real.log (2 : ℝ) := by
      rw [h₂]
    have h6 : Real.log ((12 : ℝ) ^ y) = y * Real.log 12 := by
      rw [Real.log_rpow]
      all_goals linarith
    rw [h6] at h5
    field_simp at *
    linarith
  have h5 : (1 - 2 * x) / (1 - x + y) = Real.logb (8 : ℝ) (4 / 3 : ℝ) := by
    rw [h3, h4]
    have h6 : Real.logb (8 : ℝ) (4 / 3 : ℝ) = (Real.log (4 / 3 : ℝ) ) / (Real.log (8 : ℝ) ) := by
      field_simp [Real.logb]
    rw [h6]
    have h7 : Real.log (4 / 3 : ℝ) = Real.log (4 : ℝ) - Real.log (3 : ℝ) := by 
      rw [Real.log_div (by norm_num) (by norm_num)]
    have h8 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      rw [show (4 : ℝ) = 2  ^ 2 by norm_num]
      simp [Real.log_pow]
    have h9 : Real.log (12 : ℝ) = 2 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
      calc 
        Real.log (12 : ℝ) = Real.log (4 * 3 : ℝ) := by norm_num
        _ = Real.log (4 : ℝ) + Real.log (3 : ℝ) := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 2 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by rw [h8] ; all_goals ring
    have h10 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
      calc 
        Real.log (8 : ℝ) = Real.log (2 ^ 3 : ℝ) := by norm_num
        _ = 3 * Real.log (2 : ℝ) := by simp [Real.log_pow]
    rw [h7, h8, h9, h10]
    field_simp
    <;> ring
  rw [h5]
  have h6 : (8 : ℝ) ^ (Real.logb (8 : ℝ) (4 / 3 : ℝ)) = (4 / 3 : ℝ) := by
    rw [Real.rpow_logb]
    all_goals norm_num
  exact h6