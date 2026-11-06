import Mathlib

open Real

theorem inequalities_278473 :
    (1 / logb 2 Real.pi + 1 / logb 5 Real.pi > 2) ∧
    (1 / logb 2 Real.pi + 1 / logb Real.pi 2 > 2) := by
  constructor
  · -- Prove that 1/logb 2 Real.pi + 1/logb 5 Real.pi > 2
    have h1 : 1 / logb 2 Real.pi + 1 / logb 5 Real.pi = (log 2 + log 5) / log Real.pi := by
      have h1 : logb 2 Real.pi = log Real.pi / log (2 : ℝ) := by
        field_simp [logb]
      have h2 : logb 5 Real.pi = log Real.pi / log (5 : ℝ) := by
        field_simp [logb]
      rw [h1, h2]
      field_simp
      <;> ring
    rw [h1]
    have h2 : log 10 = log 2 + log 5 := by
      calc
        log 10 = log (2 * 5) := by norm_num
        _ = log 2 + log 5 := by rw [log_mul (by norm_num) (by norm_num)]
    have h3 : log 2 + log 5 = log 10 := by
      linarith [h2]
    rw [h3]
    have h4 : (log (10 : ℝ) / log Real.pi) > 2 := by
      have h5 : log (10 : ℝ) > 2 * log Real.pi := by
        have h7 : log (10 : ℝ) > log (Real.pi ^ 2) := by
          apply Real.log_lt_log
          all_goals
            have h6 : (Real.pi : ℝ) ^ 2 < (10 : ℝ) := by
              nlinarith [Real.pi_gt_three, Real.pi_lt_31416]
            nlinarith [h6, Real.pi_pos]
        have h6 : 2 * log Real.pi = log (Real.pi ^ 2) := by
          simp [log_pow]
        linarith [h7, h6]
      have h8 : log Real.pi > 0 := by
        apply log_pos
        linarith [Real.pi_gt_three]
      apply (lt_div_iff' (by linarith)).mpr
      linarith
    linarith
  · -- Prove that 1/logb 2 Real.pi + 1/logb Real.pi 2 > 2
    have h1 : 1 / logb 2 Real.pi + 1 / logb Real.pi 2 = (log (2 : ℝ) / log Real.pi) + (log Real.pi / log (2 : ℝ)) := by
      have h1 : logb 2 Real.pi = log Real.pi / log (2 : ℝ) := by
        field_simp [logb]
      have h2 : logb Real.pi (2 : ℝ) = log (2 : ℝ) / log Real.pi := by
        field_simp [logb]
      rw [h1, h2]
      field_simp
      <;> ring
    rw [h1]
    have h4 : 0 < log (2 : ℝ) := by
      apply log_pos
      all_goals linarith
    have h5 : 0 < log Real.pi := by
      apply log_pos
      all_goals
        linarith [Real.pi_gt_three]
    have h6 : (log (2 : ℝ) / log Real.pi) + (log Real.pi / log (2 : ℝ)) > 2 := by
      have h7 : 0 < (log (2 : ℝ) * log Real.pi) := by
        positivity
      have h8 : (log (2 : ℝ) / log Real.pi + (log Real.pi / log (2 : ℝ))) - 2 > 0 := by
        have h9 : (log (2 : ℝ) / log Real.pi + (log Real.pi / log (2 : ℝ))) - 2 =
            (log (2 : ℝ) ^ 2 + log Real.pi ^ 2 - 2 * (log (2 : ℝ) * log Real.pi)) / (log (2 : ℝ) * log Real.pi) := by
          field_simp
          ring
        rw [h9]
        have h11 : log (2 : ℝ) ^ 2 + log Real.pi ^ 2 - 2 * (log (2 : ℝ) * log Real.pi) > 0 := by
          have h13 : log (2 : ℝ) ^ 2 + log Real.pi ^ 2 - 2 * (log (2 : ℝ) * log Real.pi) = (log (2 : ℝ) - log Real.pi) ^ 2 := by
            nlinarith
          rw [h13]
          have h14 : 0 < (log (2 : ℝ) - log Real.pi) ^ 2 := by
            apply pow_two_pos_of_ne_zero
            have h15 : log (2 : ℝ) < log Real.pi := by
              apply (log_lt_log_iff (by norm_num) (by linarith [Real.pi_gt_three])).mpr
              all_goals nlinarith [Real.pi_gt_three]
            linarith [h15]
          linarith
        apply div_pos
        linarith
        all_goals positivity
      linarith
    linarith