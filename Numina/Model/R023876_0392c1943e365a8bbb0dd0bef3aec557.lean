import Mathlib

open Real

theorem inequalities_228794 : 2 < 1 / logb 2 (Real.pi) + 1 / logb 5 (Real.pi) := by
  have h1 : 1 / logb 2 Real.pi + 1 / logb 5 Real.pi = (log 2 + log 5) / log Real.pi := by
    have h2 : logb 2 Real.pi = log Real.pi / log (2 : ℝ) := by 
      field_simp [logb]
      all_goals linarith
    have h3 : logb 5 Real.pi = log Real.pi / log (5 : ℝ) := by
      field_simp [logb]
      all_goals linarith
    rw [h2, h3]
    field_simp
    <;> ring
  have h4 : log 2 + log 5 = log (10 : ℝ) := by 
    calc
      log 2 + log 5 = log (2 * (5 : ℝ)) := by rw [log_mul (by norm_num) (by norm_num)]
      _ = log (10 : ℝ) := by norm_num
  rw [h1, h4]
  have h5 : Real.pi ^ 2 < (10 : ℝ) := by 
    nlinarith [Real.pi_lt_31416, Real.pi_gt_31415]
  have h6 : 2 * log Real.pi < log (10 : ℝ) := by
    have h7 : log (Real.pi ^ 2) = 2 * log Real.pi := by 
      simp [log_pow]
      <;> ring
    have h8 : log (Real.pi ^ 2) < log (10 : ℝ) := by
      apply Real.log_lt_log
      all_goals 
        nlinarith [show Real.pi > 0 by linarith [Real.pi_gt_31415], h5]
    linarith [h7, h8]
  have h7 : log Real.pi > 0 := by 
    apply Real.log_pos
    linarith [Real.pi_gt_31415]
  have h8 : (log (10 : ℝ) : ℝ) / log Real.pi > (2 : ℝ) := by
    apply (lt_div_iff₀ h7).mpr 
    linarith 
  linarith [h8]