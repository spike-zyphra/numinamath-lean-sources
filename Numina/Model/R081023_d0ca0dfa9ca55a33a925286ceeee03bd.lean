import Mathlib

open Real

theorem inequalities_204092 : (1 / logb 2 Real.pi) + (1 / logb 5 Real.pi) > 2 := by 
  have h1 : 1 / logb 2 Real.pi = (log 2) / (log Real.pi) := by
    field_simp [logb]
    all_goals linarith
  have h2 : 1 / logb 5 Real.pi = (log 5) / (log Real.pi) := by
    field_simp [logb]
    all_goals linarith
  rw [h1, h2]
  have h3 : log 2 + log 5 = log 10 := by
    calc 
      log 2 + log 5 = log (2 * 5) := by rw [log_mul (by norm_num) (by norm_num)]
      _ = log 10 := by norm_num
  have h4 : log Real.pi > 0 := by
    have h5 : Real.pi > 1 := by
      linarith [Real.pi_gt_three]
    have h6 : log Real.pi > 0 := by
      apply log_pos
      all_goals nlinarith
    linarith
  have h7 : Real.pi ^ 2 < (10 : ℝ) := by
    have hpi1 : Real.pi < (3.15 : ℝ) := by
      linarith [Real.pi_lt_315]
    nlinarith [Real.pi_gt_three, Real.pi_lt_315]
  have h8 : log 10 > 2 * log Real.pi := by
    have h9 : log (Real.pi ^ 2) = 2 * log Real.pi := by
      simp [log_pow]
    have h10 : Real.pi ^ 2 < (10 : ℝ) := h7
    have h11 : log (Real.pi ^ 2) < log 10 := by
      apply Real.log_lt_log
      all_goals nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h14 : log 10 > log (Real.pi ^ 2) := by linarith
    linarith [h9, h14]
  have h13 : (log 2 + log 5) / (log Real.pi) > (2 : ℝ) := by
    have h14 : log 2 + log 5 = log 10 := h3
    have h15 : log 10 > 2 * log Real.pi := h8
    have h16 : log Real.pi > 0 := h4
    have h17 : (log 2 + log 5) / (log Real.pi) = (log 10) / (log Real.pi) := by 
      rw [show log 10 = log 2 + log 5 by linarith [h3]]
      all_goals linarith
    rw [h17]
    apply (lt_div_iff₀' (by positivity : log Real.pi > 0)).mpr
    nlinarith
  have h18 : (log 2 / (log Real.pi) + log 5 / (log Real.pi)) = (log 2 + log 5) / (log Real.pi) := by 
    ring_nf
  linarith [h18, h13]
  all_goals linarith