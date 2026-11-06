import Mathlib

open Real

theorem algebra_276199 :
    logb 3 (0.2) < 0 ∧ 0 < 1 ∧ 1 < logb (1 / 2) 0.3 := by
  have h1 : logb 3 (0.2) < 0 := by
    have h2 : logb 3 (0.2) = log (0.2) / log (3) := by 
      field_simp [logb]
    rw [h2]
    have h3 : log (0.2) < 0 := by
      have h4 : log (0.2) < log (1) := by 
        apply Real.log_lt_log
        all_goals norm_num
      have h5 : log (1) = 0 := by 
        simp [log_one]
      linarith [h4, h5]
    have h4 : log (3) > 0 := by
      have h5 : log (3) > log (1) := by 
        apply Real.log_lt_log
        all_goals norm_num
      have h6 : log (1) = 0 := by 
        simp [log_one]
      linarith [h5, h6]
    apply div_neg_of_neg_of_pos 
    · linarith
    · linarith
  constructor
  · exact h1
  constructor
  · norm_num
  · -- Show that 1 < logb (1 / 2) 0.3
    have h3 : logb (1 / 2) (0.3) = log (0.3) / log (1 / 2) := by 
      field_simp [logb]
    have h4 : log (1 / 2) = -log 2 := by 
      calc
        log (1 / 2) = log (1) - log (2) := by 
          rw [log_div (by norm_num) (by norm_num)]
        _ = 0 - log 2 := by 
          simp [log_one]
        _ = -log 2 := by 
          ring
    have h7 : log (0.3) + log 2 < 0 := by
      have h8 : log (0.3) + log 2 = log (0.3 * (2 : ℝ)) := by 
        rw [log_mul (by norm_num) (by norm_num)]
      rw [h8]
      have h9 : (0.3 * (2 : ℝ) ) = (0.6 : ℝ) := by norm_num
      rw [h9]
      have h10 : log (0.6 : ℝ) < (0 : ℝ) := by
        have h11 : log (0.6) < log (1 : ℝ) := by 
          apply Real.log_lt_log
          all_goals norm_num
        have h12 : log (1 : ℝ) = (0 : ℝ) := by 
          simp [log_one]
        linarith [h11, h12]
      linarith
    have h8 : logb (1 / 2) (0.3) > 1 := by
      rw [h3, h4]
      have h6' : log 2 > 0 := by 
        have h7 : log 2 > log 1 := by 
          apply Real.log_lt_log
          all_goals norm_num
        have h8 : log 1 = 0 := by 
          simp [log_one]
        linarith [h7, h8]
      have h9 : log (0.3) / (-log 2) > 1 := by
        have h7'' : log (0.3) < -log 2 := by linarith [h7]
        have h10 : -log 2 < 0 := by linarith [h6']
        apply (lt_div_iff_of_neg' (by linarith)).mpr
        linarith [h7'']
      linarith
    linarith [h8]