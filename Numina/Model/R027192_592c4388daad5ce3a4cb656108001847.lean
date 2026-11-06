import Mathlib

open Real

lemma lemma_1 : log 3 + log 5 < 2 * log 4 := by
  have h1 : log 3 + log 5 = log (3 * 5) := by
    rw [log_mul (by norm_num) (by norm_num)]
  have h2 : 2 * log 4 = log (4 ^ 2 : ℝ) := by
    simp [log_pow]
  have h3 : log (3 * 5 : ℝ) < log (4 ^ 2 : ℝ) := by
    apply Real.log_lt_log
    all_goals
    norm_num
  linarith [h1, h2, h3]


theorem algebra_246874 : Real.logb 3 4 > Real.logb 4 5 := by 
  have h1 : Real.logb 3 4 = (log 4) / (log 3) := by 
    field_simp [Real.logb]
  have h2 : Real.logb 4 5 = (log 5) / (log 4) := by 
    field_simp [Real.logb]
  have h3 : log 3 > 0 := by
    apply log_pos
    all_goals
    norm_num
  have h4 : log 4 > 0 := by
    apply log_pos
    all_goals
    norm_num
  have h5 : log 5 > 0 := by
    apply log_pos
    all_goals
    norm_num
  have h6 : (log 4) ^ 2 > (log 3) * (log 5) := by
    nlinarith [lemma_1, sq_nonneg (log 3 - log 4), sq_nonneg (log 4 - log 5), 
      Real.log_pos (show (3 : ℝ) > 1 by norm_num), 
      Real.log_pos (show (4 : ℝ) > 1 by norm_num), 
      Real.log_pos (show (5 : ℝ) > 1 by norm_num)]
  have h7 : (log 4) / (log 3) > (log 5) / (log 4) := by
    have h8 : 0 < log 3 := h3
    have h9 : 0 < log 4 := h4
    have h10 : (log 4) / (log 3) - (log 5) / (log 4) > 0 := by
      have h11 : (log 4) / (log 3) - (log 5) / (log 4) = ((log 4) ^ 2 - (log 3) * (log 5)) / (log 3 * log 4) := by
        field_simp
        ring
      rw [h11]
      have h12 : (log 4) ^ 2 - (log 3) * (log 5) > 0 := by
        linarith [h6]
      have h13 : log 3 * log 4 > 0 := by
        positivity
      apply div_pos
      all_goals
      linarith
    linarith
  linarith [h1, h2, h7]