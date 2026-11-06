import Mathlib

open Real

theorem algebra_327323 : logb 27 124 < 3 / 2 ∧ 3 / 2 < logb 16 82 := by
  have h1 : logb 27 124 = (log 124) / (log 27) := by
    field_simp [logb]

  have h2 : logb 16 82 = (log 82) / (log 16) := by
    field_simp [logb]

  have h3 : log 27 = 3 * (log 3) := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num]
    simp [log_pow]

  have h4 : log 16 = 4 * (log 2) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
    simp [log_pow]

  have h6 : 2 * (log 124) < 3 * (log 27) := by 
    have h7 : log (124 ^ 2) = 2 * (log 124) := by 
      simp [log_pow]
    have h8 : log (27 ^ 3) = 3 * (log 27) := by
      simp [log_pow]
    have h9 : log (124 ^ 2) < log (27 ^ 3) := by
      have h10 : (124 ^ 2 : ℝ) < (27 ^ 3 : ℝ) := by norm_num
      have h11 : log (124 ^ 2 : ℝ) < log (27 ^ 3 : ℝ) := by 
        have h10 : (124 ^ 2 : ℝ) < (27 ^ 3 : ℝ) := by norm_num
        have h13 : (124 ^ 2 : ℝ) > 0 := by norm_num
        have h14 : (27 ^ 3 : ℝ) > 0 := by norm_num
        apply Real.log_lt_log
        all_goals
          nlinarith
      linarith
    linarith [h9, h7, h8]

  have h7 : 3 * (log 16) < 2 * (log 82) := by 
    have h8 : log (16 ^ 3) = 3 * (log 16) := by 
      simp [log_pow]
    have h9 : log (82 ^ 2) = 2 * (log 82) := by 
      simp [log_pow]
    have h10 : log (16 ^ 3) < log (82 ^ 2) := by
      have h11 : (16 : ℝ) ^ 3 < (82 : ℝ) ^ 2 := by norm_num
      have h12 : log (16 ^ 3 : ℝ) < log (82 ^ 2 : ℝ) := by 
        have h11 : (16 : ℝ) ^ 3 < (82 : ℝ) ^ 2 := by norm_num
        have h13 : (16 ^ 3 : ℝ) > 0 := by norm_num
        have h14 : (82 ^ 2 : ℝ) > 0 := by norm_num
        apply Real.log_lt_log
        all_goals
          nlinarith
      linarith
    linarith [h10, h8, h9]

  have h8 : log 27 > 0 := by 
    have : log 27 > 0 := by
      apply log_pos 
      norm_num
    linarith

  have h9 : log 16 > 0 := by 
    have : log 16 > 0 := by 
      apply log_pos 
      norm_num 
    linarith

  constructor
  · -- Prove logb 27 124 < 3 / 2 
    rw [h1]
    have h10 : log 27 > 0 := h8 
    apply (div_lt_iff₀ (by linarith)).mpr
    nlinarith [h6, h3]

  · -- Prove 3 / 2 < logb 16 82 
    rw [h2]
    have h12 : log 16 > 0 := h9 
    apply (lt_div_iff₀ (by linarith)).mpr
    nlinarith [h7, h4]