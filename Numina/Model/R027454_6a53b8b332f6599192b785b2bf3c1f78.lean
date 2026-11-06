import Mathlib

open Real

theorem inequalities_283846 : 1 / logb 2 (Real.pi) + 1 / logb 5 (Real.pi) > 2 := by
  have h1 : 1 / logb 2 Real.pi + 1 / logb 5 Real.pi = (log 2 + log 5) / log Real.pi := by
    have h2 : logb 2 Real.pi = (log Real.pi) / (log (2 : ℝ)) := by
      field_simp [logb]
    have h3 : logb 5 Real.pi = (log Real.pi) / (log (5 : ℝ)) := by
      field_simp [logb]
    rw [h2, h3]
    have h4 : 1 / ((log Real.pi) / (log (2 : ℝ))) = (log (2 : ℝ)) / (log Real.pi) := by
      field_simp
    have h5 : 1 / ((log Real.pi) / (log (5 : ℝ))) = (log (5 : ℝ)) / (log Real.pi) := by
      field_simp
    rw [h4, h5]
    have h6 : (log (2 : ℝ) / log Real.pi) + (log (5 : ℝ) / log Real.pi) = (log (2 : ℝ) + log (5 : ℝ)) / log Real.pi := by
      ring_nf
    linarith [h6]
  have h7 : log Real.pi > 0 := by
    apply log_pos
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h8 : log (2 : ℝ) + log (5 : ℝ) = log (10 : ℝ) := by
    calc
      log (2 : ℝ) + log (5 : ℝ) = log ((2 : ℝ) * (5 : ℝ)) := by rw [log_mul (by norm_num) (by norm_num)]
      _ = log (10 : ℝ) := by norm_num
  have h8' : log (10 : ℝ) > 2 * log Real.pi := by
    have h9 : 10 > Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
    have h10 : log (10 : ℝ) > log (Real.pi ^ 2) := by
      apply Real.log_lt_log
      all_goals nlinarith [Real.pi_gt_31415, Real.pi_lt_31416]
    have h11 : log (Real.pi ^ 2) = 2 * log Real.pi := by
      simp [log_pow]
    linarith [h10, h11]
  have h9 : (log (2 : ℝ) + log (5 : ℝ)) / log Real.pi > 2 := by
    have h11 : log Real.pi > 0 := h7
    rw [show log (2 : ℝ) + log (5 : ℝ) = log (10 : ℝ) by linarith [h8]]
    apply (lt_div_iff₀ h11).mpr
    linarith [h8']
  linarith [h1, h9]