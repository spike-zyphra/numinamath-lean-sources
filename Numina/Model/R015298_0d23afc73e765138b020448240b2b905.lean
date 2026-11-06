import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10471 {x : ℝ}
  (hx : x = 1 / logb (1 / 2) (1 / 3) + 1 / logb (1 / 5) (1 / 3)) :
  2 < x ∧ x < 3 := by

  have h1 : x = Real.logb 3 10 := by
    rw [hx]
    have h2 : logb (1 / 2) (1 / 3) = (log 3) / (log 2) := by 
      have h3 : logb (1 / 2) (1 / 3) = (log (1 / 3)) / (log (1 / 2 : ℝ)) := by 
        field_simp [logb]
      rw [h3]
      have h4 : log (1 / 3 : ℝ) = - log 3 := by 
        simp [log_div, log_one]
      have h5 : log (1 / 2 : ℝ) = - log 2 := by 
        simp [log_div, log_one]
      rw [h4, h5]
      <;> ring_nf
    have h6 : logb (1 / 5) (1 / 3) = (log 3) / (log 5) := by 
      have h3 : logb (1 / 5) (1 / 3) = (log (1 / 3 : ℝ)) / (log (1 / 5 : ℝ)) := by 
        field_simp [logb]
      rw [h3]
      have h4 : log (1 / 3 : ℝ) = - log 3 := by 
        simp [log_div, log_one]
      have h5 : log (1 / 5 : ℝ) = - log 5 := by 
        simp [log_div, log_one]
      rw [h4, h5]
      <;> ring_nf
    rw [h2, h6]
    have h7 : 1 / ((log 3) / (log 2)) = (log 2) / (log 3) := by 
      field_simp 
    have h8 : 1 / ((log 3) / (log 5)) = (log 5) / (log 3) := by 
      field_simp 
    rw [h7, h8]
    have h9 : (log 2 : ℝ) / (log 3) + (log 5 : ℝ) / (log 3) = (log 2 + log 5) / (log 3) := by 
      ring_nf
    rw [h9]
    have h10 : log 2 + log 5 = log 10 := by 
      calc 
        log 2 + log 5 = log (2 * 5) := by rw [log_mul (by norm_num) (by norm_num)]
        _ = log 10 := by norm_num 
    rw [h10]
    field_simp [logb]
  rw [h1]
  constructor
  · -- Show 2 < Real.logb 3 10
    have h31 : 2 < Real.logb 3 10 := by 
      have h311 : Real.logb 3 9 = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      have h312 : Real.logb 3 9 < Real.logb 3 10 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      linarith [h311, h312] 
    linarith 
  · -- Show Real.logb 3 10 < 3 
    have h32 : Real.logb 3 10 < 3 := by 
      have h321 : Real.logb 3 27 = 3 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      have h322 : Real.logb 3 10 < Real.logb 3 27 := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      linarith [h321, h322] 
    linarith