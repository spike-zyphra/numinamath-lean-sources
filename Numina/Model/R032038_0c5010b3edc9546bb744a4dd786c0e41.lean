import Mathlib

open Real

theorem inequalities_228801 : 3 / 10 < logb 10 2 ∧ logb 10 2 < 1 / 3 := by
  have h1 : 3 / 10 < logb 10 2 := by
    have h2 : logb 10 2 = (log 2) / (log 10) := by
      field_simp [logb]
    rw [h2]
    have h3 : log 10 > 0 := by
      apply log_pos
      all_goals norm_num
    have h4 : 3 * log 10 < 10 * log 2 := by
      have h5 : log (10 ^ 3) = 3 * log 10 := by
        simp [log_pow]
        <;> ring_nf <;> simp [log_pow]
      have h6 : log (2 ^ 10) = 10 * log 2 := by
        simp [log_pow]
        <;> ring_nf <;> simp [log_pow]
      have h7 : log (10 ^ 3) < log (2 ^ 10) := by
        apply Real.log_lt_log
        all_goals norm_num
      have h8 : log (10 ^ 3) < log (2 ^ 10) := h7
      linarith [h8, h5, h6]
    have h5 : (3 / 10 : ℝ) < (log 2 ) / (log 10) := by
      apply (lt_div_iff₀ (by positivity)).mpr
      linarith [h4]
    linarith
  have h2 : logb 10 2 < (1 / 3 : ℝ) := by
    have h2 : logb 10 2 = (log 2) / (log 10) := by
      field_simp [logb]
    rw [h2]
    have h3 : log 10 > 0 := by
      apply log_pos
      all_goals norm_num
    have h4 : 3 * log 2 < log 10 := by
      have h5 : log (2 ^ 3) = 3 * log 2 := by
        simp [log_pow]
      have h6 : log (2 ^ 3) < log 10 := by
        apply Real.log_lt_log
        all_goals norm_num
      linarith [h5, h6]
    have h5 : (log 2 : ℝ) / (log 10) < (1 / 3 : ℝ) := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [h4]
    linarith
  constructor
  · exact h1
  · exact h2