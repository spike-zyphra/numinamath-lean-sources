import Mathlib


theorem algebra_96491 {a : ℝ} (ha : 0 < a) (ha' : a ≠ 1) :
    1 / Real.logb 2 a + 1 / Real.logb 3 a + 1 / Real.logb 4 a = 1 ↔ a = 24 := by
  constructor
  · -- Assume the equation holds, prove a = 24
    intro h
    have h1 : Real.logb 2 a = Real.log a / Real.log 2 := by
      field_simp [Real.logb]
    have h2 : Real.logb 3 a = Real.log a / Real.log 3 := by
      field_simp [Real.logb]
    have h3 : Real.logb 4 a = Real.log a / Real.log 4 := by
      field_simp [Real.logb]
    rw [h1, h2, h3] at h
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by simp [Real.log_pow]
    rw [h4] at h
    have h5 : Real.log a ≠ 0 := by
      have h6 : a > 0 := ha
      have h7 : a ≠ 1 := ha'
      exact Real.log_ne_zero_of_pos_of_ne_one h6 h7
    have h7 : Real.log a = 3 * Real.log 2 + Real.log 3 := by
      field_simp [h5] at h
      nlinarith
    have h8 : Real.log a = Real.log (24 : ℝ) := by
      have h9 : Real.log (24 : ℝ) = 3 * Real.log 2 + Real.log 3 := by
        calc
          Real.log (24 : ℝ) = Real.log (8 * 3) := by norm_num
          _ = Real.log (8 : ℝ) + Real.log (3 : ℝ) := by rw [Real.log_mul (by norm_num) (by norm_num)]
          _ = Real.log (2 ^ 3 : ℝ) + Real.log 3 := by norm_num
          _ = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by simp [Real.log_pow]
          _ = 3 * Real.log 2 + Real.log 3 := by norm_num
      linarith [h7, h9]
    have h9 : a = (24 : ℝ) := by
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr (show (24 : ℝ) > 0 by norm_num)) h8
    linarith
  · -- Assume a = 24, prove the equation
    intro h
    rw [h]
    have h1 : Real.logb 2 (24 : ℝ) = Real.log (24 : ℝ) / Real.log (2 : ℝ) := by
      field_simp [Real.logb]
    have h2 : Real.logb 3 (24 : ℝ) = Real.log (24 : ℝ) / Real.log (3 : ℝ) := by
      field_simp [Real.logb]
    have h3 : Real.logb 4 (24 : ℝ) = Real.log (24 : ℝ) / Real.log (4 : ℝ) := by
      field_simp [Real.logb]
    rw [h1, h2, h3]
    have h4 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
      calc
        Real.log (4 : ℝ) = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
    have h5 : Real.log (24 : ℝ) = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by
      calc
        Real.log (24 : ℝ) = Real.log (8 * 3) := by norm_num
        _ = Real.log (8 : ℝ) + Real.log (3 : ℝ) := by rw [Real.log_mul (by norm_num) (by norm_num)]
        _  = Real.log (2 ^ 3 : ℝ) + Real.log (3 : ℝ) := by norm_num
        _ = 3 * Real.log (2 : ℝ) + Real.log (3 : ℝ) := by simp [Real.log_pow]
    rw [h4, h5]
    have h6 : Real.log (2 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals linarith
    have h7 : Real.log (3 : ℝ) > 0 := by
      apply Real.log_pos
      all_goals linarith
    field_simp [h6, h7]
    <;> nlinarith [Real.log_pos (show (3 : ℝ) > 1 by norm_num), Real.log_pos (show (2 : ℝ) > 1 by norm_num)]