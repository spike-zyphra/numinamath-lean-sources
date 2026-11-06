import Mathlib

open Real

theorem inequalities_81818 : 0.47 < logb 10 3 ∧ logb 10 3 < 0.482 := by
  have h1 : logb 10 15 < logb 10 16 := by 
    apply Real.logb_lt_logb
    all_goals norm_num
  have h1' : logb 10 15 = logb 10 3 + logb 10 5 := by
    rw [show (15 : ℝ) = 3 * 5 by norm_num]
    rw [logb_mul (by norm_num) (by norm_num)]
  have h1'' : logb 10 5 = 1 - logb 10 2 := by 
    have h4 : logb 10 2 + logb 10 5 = 1 := by 
      have h5 : logb 10 2 + logb 10 5 = logb 10 (2 * 5) := by 
        rw [logb_mul (by norm_num) (by norm_num)]
      rw [h5]
      norm_num [logb_eq_iff_rpow_eq]
    linarith
  have h1''' : logb 10 16 = 4 * logb 10 2 := by 
    calc 
      logb 10 16 = logb 10 (2 ^ 4) := by norm_num 
      _ = 4 * logb 10 2 := by simp [logb_pow]
  rw [h1', h1''] at h1
  rw [h1'''] at h1
  -- From $15 < 16$ we derive $1 - x + y < 4x$
  -- Finally we have $1 + y < 5x$.
  have h2 : logb 10 80 < logb 10 81 := by 
    apply Real.logb_lt_logb
    all_goals norm_num
  have h2' : logb 10 80 = 3 * logb 10 2 + 1 := by 
    calc 
      logb 10 80 = logb 10 (8 * 10) := by norm_num
      _ = logb 10 8 + logb 10 10 := by rw [logb_mul (by norm_num) (by norm_num)]
      _ = logb 10 (2 ^ 3) + logb 10 10 := by norm_num 
      _ = 3 * logb 10 2 + logb 10 10 := by simp [logb_pow]
      _ = 3 * logb 10 2 + (1 : ℝ) := by simp [logb_eq_iff_rpow_eq]
  have h2'' : logb 10 81 = 4 * logb 10 3 := by 
    calc 
      logb 10 81 = logb 10 (3 ^ 4) := by norm_num 
      _ = 4 * logb 10 3 := by simp [logb_pow]
  rw [h2', h2''] at h2
  -- From $80 < 81$ we derive $3x + 1 < 4y$
  have h3 : logb 10 243 < logb 10 250 := by 
    apply Real.logb_lt_logb
    all_goals norm_num
  have h3' : logb 10 243 = 5 * logb 10 3 := by 
    calc 
      logb 10 243 = logb 10 (3 ^ 5) := by norm_num 
      _ = 5 * logb 10 3 := by simp [logb_pow]
  have h3'' : logb 10 250 = 3 - 2 * logb 10 2 := by 
    calc 
      logb 10 250 = logb 10 (2.5 * (10 : ℝ) ^ 2) := by norm_num
      _ = logb 10 2.5 + logb 10 ((10 : ℝ) ^ 2) := by rw [logb_mul (by norm_num) (by norm_num)]
      _ = logb 10 (5 / 2) + logb 10 ((10 : ℝ) ^ 2) := by norm_num
      _ = (logb 10 5 - logb 10 2) + logb 10 ((10 : ℝ) ^ 2) := by rw [logb_div (by norm_num) (by norm_num)]
      _ = (1 - logb 10 2 - logb 10 2) + logb 10 ((10 : ℝ) ^ 2) := by 
        have h4 : logb 10 5 = 1 - logb 10 2 := by
          have h1 : logb 10 2 + logb 10 5 = 1 := by
            have h2 : logb 10 2 + logb 10 5 = logb 10 (2 * 5) := by
              rw [logb_mul (by norm_num) (by norm_num)]
            rw [h2]
            norm_num [logb_eq_iff_rpow_eq]
          linarith
        rw [h4]
        all_goals ring_nf <;> linarith
      _ = (1 - 2 * logb 10 2) + (2 : ℝ) := by 
        simp [logb_pow]
        all_goals ring
      _ = (3 - 2 * logb 10 2) := by 
        ring
  rw [h3', h3''] at h3
  -- From $243 < 250$ we get $5y < 3 - 2x$
  constructor
  · -- Show 0.47 < logb 10 3
    have h4 : logb 10 3 > (8 / 17 : ℝ) := by
      nlinarith
    norm_num at h4 ⊢
    linarith
  · -- Show logb 10 3 < 0.482
    have h5 : logb 10 3 < (13 / 27 : ℝ) := by
      nlinarith
    norm_num at h5 ⊢
    linarith