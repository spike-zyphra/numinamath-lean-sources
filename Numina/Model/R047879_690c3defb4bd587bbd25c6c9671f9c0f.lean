import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_119400 (a b c : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
  logb 2 a ^ 2 / (1 + logb 2 (b ^ 2)) +
  logb 2 b ^ 2 / (1 + logb 2 (c ^ 2)) +
  logb 2 c ^ 2 / (1 + logb 2 (a ^ 2)) ≥ 1 := by

  have h1 : logb 2 (b ^ 2) = 2 * logb 2 b := by 
    simp [logb_pow]

  have h2 : logb 2 (c ^ 2) = 2 * logb 2 c := by 
    simp [logb_pow]

  have h3 : logb 2 (a ^ 2) = 2 * logb 2 a := by 
    simp [logb_pow]

  have h4 : 0 ≤ logb 2 a - 1 := by 
    have h5 : logb 2 a ≥ 1 := by 
      have h6 : logb 2 a ≥ logb 2 (2 : ℝ) := by 
        apply logb_le_logb_of_le 
        all_goals nlinarith 
      have h7 : logb 2 (2 : ℝ) = 1 := by 
        rw [logb_eq_iff_rpow_eq] <;> (norm_num) 
      nlinarith 
    linarith

  have h5 : 0 ≤ logb 2 b - 1 := by 
    have h6 : logb 2 b ≥ 1 := by 
      have h7 : logb 2 b ≥ logb 2 (2 : ℝ) := by 
        apply logb_le_logb_of_le 
        all_goals nlinarith 
      have h8 : logb 2 (2 : ℝ) = 1 := by 
        rw [logb_eq_iff_rpow_eq] <;> (norm_num) 
      nlinarith 
    linarith 

  have h6 : 0 ≤ logb 2 c - 1 := by 
    have h7 : logb 2 c ≥ 1 := by 
      have h8 : logb 2 c ≥ logb 2 (2 : ℝ) := by 
        apply logb_le_logb_of_le 
        all_goals nlinarith 
      have h9 : logb 2 (2 : ℝ) = 1 := by 
        rw [logb_eq_iff_rpow_eq] <;> (norm_num) 
      nlinarith 
    linarith 

  have h4a : logb 2 a ≥ 1 := by 
    have h6 : logb 2 a ≥ logb 2 (2 : ℝ) := by 
      apply logb_le_logb_of_le 
      all_goals nlinarith 
    have h7 : logb 2 (2 : ℝ) = 1 := by 
      rw [logb_eq_iff_rpow_eq] <;> (norm_num) 
    nlinarith 

  have h4b : logb 2 b ≥ 1 := by 
    have h7 : logb 2 b ≥ logb 2 (2 : ℝ) := by 
      apply logb_le_logb_of_le 
      all_goals nlinarith 
    have h8 : logb 2 (2 : ℝ) = 1 := by 
      rw [logb_eq_iff_rpow_eq] <;> (norm_num) 
    nlinarith

  have h4c : logb 2 c ≥ 1 := by 
    have h8 : logb 2 c ≥ logb 2 (2 : ℝ) := by 
      apply logb_le_logb_of_le 
      all_goals nlinarith 
    have h9 : logb 2 (2 : ℝ) = 1 := by 
      rw [logb_eq_iff_rpow_eq] <;> (norm_num) 
    nlinarith

  have h10 : logb 2 a ^ 2 / (1 + logb 2 (b ^ 2)) + logb 2 b ^ 2 / (1 + logb 2 (c ^ 2)) + logb 2 c ^ 2 / (1 + logb 2 (a ^ 2)) - 1 ≥ 0 := by 
    have hx1 : logb 2 (b ^ 2) = 2 * logb 2 b := by 
      simp [logb_pow]
    have hx2 : logb 2 (c ^ 2) = 2 * logb 2 c := by 
      simp [logb_pow]
    have hx3 : logb 2 (a ^ 2) = 2 * logb 2 a := by 
      simp [logb_pow]
    have hx4 : logb 2 a ≥ 1 := h4a 
    have hx5 : logb 2 b ≥ 1 := h4b 
    have hx6 : logb 2 c ≥ 1 := h4c 
    have hx12 : logb 2 a ^ 2 / (1 + logb 2 (b ^ 2)) + logb 2 b ^ 2 / (1 + logb 2 (c ^ 2)) + logb 2 c ^ 2 / (1 + logb 2 (a ^ 2)) - 1 =
        (logb 2 a ^ 2 * (1 + 2 * logb 2 c) * (1 + 2 * logb 2 a) + logb 2 b ^ 2 * (1 + 2 * logb 2 a) * (1 + 2 * logb 2 b) + logb 2 c ^ 2 * (1 + 2 * logb 2 b) * (1 + 2 * logb 2 c) - (1 + 2 * logb 2 b) * (1 + 2 * logb 2 c) * (1 + 2 * logb 2 a)) / ((1 + 2 * logb 2 b) * (1 + 2 * logb 2 c) * (1 + 2 * logb 2 a)) := by 
      rw [hx1, hx2, hx3]
      field_simp 
      ring 
    rw [hx12] at *
    apply div_nonneg
    nlinarith [sq_nonneg (logb 2 a - 1), sq_nonneg (logb 2 b - 1), sq_nonneg (logb 2 c - 1),
             sq_nonneg (logb 2 a - logb 2 b), sq_nonneg (logb 2 b - logb 2 c), sq_nonneg (logb 2 c - logb 2 a),
             mul_nonneg (show 0 ≤ logb 2 a - 1 by linarith) (show 0 ≤ logb 2 b - 1 by linarith),
             mul_nonneg (show 0 ≤ logb 2 b - 1 by linarith) (show 0 ≤ logb 2 c - 1 by linarith),
             mul_nonneg (show 0 ≤ logb 2 c - 1 by linarith) (show 0 ≤ logb 2 a - 1 by linarith)
           ]
    positivity
  linarith
  all_goals linarith