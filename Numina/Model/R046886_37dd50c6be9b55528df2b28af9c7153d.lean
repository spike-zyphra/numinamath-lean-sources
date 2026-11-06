import Mathlib

open Real

lemma lemma_1 : logb 24 48 > 6 / 5 := by
  have h1 : logb 24 48 = log 48 / log 24 := by
    field_simp [logb]
  rw [h1]
  have h2 : log 48 > 0 := by
    apply log_pos
    all_goals
      norm_num
  have h3 : log 24 > 0 := by
    apply log_pos
    all_goals
      norm_num
  have h4 : 5 * log 48 > 6 * log 24 := by
    have h5 : 5 * log 48 = log (48 ^ 5) := by
      simp [log_pow]
    have h6 : 6 * log 24 = log (24 ^ 6) := by
      simp [log_pow]
    rw [h5, h6]
    have h7 : (48 : ℝ) ^ 5 > (24 : ℝ) ^ 6 := by
      norm_num
    have h8 : log ((48 : ℝ) ^ 5) > log ((24 : ℝ) ^ 6) := by
      apply Real.log_lt_log
      all_goals
        norm_num
    linarith
  have h5 : log 24 > 0 := by
    apply log_pos
    all_goals
      norm_num
  apply (div_lt_div_iff (by positivity) (by positivity)).mpr
  linarith

theorem inequalities_89085 : (logb 24 48)^2 + (logb 12 54)^2 > 4 := by
  have h3 : logb 12 54 > 8 / 5 := by
    have h1 : logb 12 54 = log 54 / log 12 := by
      field_simp [logb]
    rw [h1]
    have h2 : log 54 > 0 := by
      apply log_pos
      all_goals
        norm_num
    have h3 : log 12 > 0 := by
      apply log_pos
      all_goals
        norm_num
    have h4 : 5 * log 54 > 8 * log 12 := by
      have h5 : 5 * log 54 = log (54 ^ 5) := by
        simp [log_pow]
      have h6 : 8 * log 12 = log (12 ^ 8) := by
        simp [log_pow]
      rw [h5, h6]
      have h7 : (54 : ℝ) ^ 5 > (12 : ℝ) ^ 8 := by
        norm_num
      have h8 : log ((54 : ℝ) ^ 5) > log ((12 : ℝ) ^ 8) := by
        apply Real.log_lt_log
        all_goals
          norm_num
      linarith
    have h5 : log 12 > 0 := by
      apply log_pos
      all_goals
        norm_num
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    linarith
  have h4 : logb 24 48 > 6 / 5 := lemma_1
  have h6 : (logb 24 48) ^ 2 > (36 / 25 : ℝ) := by
    nlinarith [h4]
  have h7 : (logb 12 54) ^ 2 > (64 / 25 : ℝ) := by
    nlinarith [h3]
  linarith [h6, h7]