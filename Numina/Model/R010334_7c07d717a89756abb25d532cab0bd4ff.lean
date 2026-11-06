import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_254392 (x : ℝ) :
  x * logb (1 / 10) (x^2 + x + 1) > 0 ↔ x < -1 := by 
  have h1 : logb (1 / 10) (x^2 + x + 1) = -logb 10 (x^2 + x + 1) := by 
    have h2 : logb (1 / 10) (x^2 + x + 1) = logb 10 (x^2 + x + 1) / logb 10 (1 / 10) := by 
      field_simp [logb]
    have h3 : logb 10 (1 / 10) = -1 := by 
      rw [logb_eq_iff_rpow_eq] <;> norm_num 
    rw [h3] at h2 
    rw [h2]
    field_simp 
  rw [h1]
  constructor
  · -- Forward implication: If x * (-logb 10 (x^2 + x + 1)) > 0, then x < -1
    intro h
    have h2 : x * (-logb 10 (x^2 + x + 1)) > 0 := by 
      linarith 
    have h3 : x * logb 10 (x^2 + x + 1) < 0 := by 
      linarith 
    by_cases h4 : logb 10 (x^2 + x + 1) > 0 
    · -- logb 10 (x^2 + x + 1) > 0
      have h5 : x < 0 := by 
        nlinarith 
      have h6 : x^2 + x + 1 > (1 : ℝ) := by 
        have h7 : logb 10 (x^2 + x + 1) > 0 := h4 
        have h8 : x^2 + x + 1 > (1 : ℝ) := by 
          by_contra h'
          push_neg at h'
          have h9 : logb 10 (x^2 + x + 1) ≤ logb 10 (1 : ℝ) := by 
            apply Real.logb_le_logb_of_le 
            all_goals nlinarith 
          have h10 : logb 10 (1 : ℝ) = 0 := by 
            norm_num [logb_one] 
          rw [h10] at h9 
          linarith 
        linarith 
      nlinarith 
    · -- logb 10 (x^2 + x + 1) ≤ 0 
      by_cases h5 : logb 10 (x^2 + x + 1) < 0 
      · -- logb 10 (x^2 + x + 1) < 0 
        have h6 : x > 0 := by 
          nlinarith 
        have h7 : x^2 + x + 1 < (1 : ℝ) := by 
          have h8 : logb 10 (x^2 + x + 1) < 0 := h5 
          have h9 : x^2 + x + 1 < (1 : ℝ) := by 
            by_contra h'
            push_neg at h'
            have h10 : logb 10 (x^2 + x + 1) ≥ logb 10 (1 : ℝ) := by 
              apply Real.logb_le_logb_of_le 
              all_goals nlinarith 
            have h11 : logb 10 (1 : ℝ) = 0 := by 
              norm_num [logb_one] 
            rw [h11] at h10 
            linarith 
          linarith 
        nlinarith 
      · -- logb 10 (x^2 + x + 1) = 0 
        have h4' : logb 10 (x^2 + x + 1) = 0 := by linarith 
        have h5 : x^2 + x + 1 = (1 : ℝ) := by 
          have h6 : logb 10 (x^2 + x + 1) = 0 := h4' 
          rw [logb_eq_iff_rpow_eq] at h6 
          · -- logb 10 (x^2 + x + 1) = 0 
            nlinarith 
          all_goals nlinarith 
        nlinarith 
  · -- Backward implication: If x < -1, then x * (-logb 10 (x^2 + x + 1)) > 0 
    intro h
    have h1 : x < -1 := h
    have h3 : x < 0 := by linarith 
    have h4 : x^2 + x + 1 > (1 : ℝ) := by 
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h5 : logb 10 (x^2 + x + 1) > 0 := by 
      have h7 : x^2 + x + 1 > (1 : ℝ) := h4
      have h8 : logb 10 (x^2 + x + 1) > logb 10 (1 : ℝ) := by 
        apply Real.logb_lt_logb <;> (try norm_num) <;> nlinarith 
      have h9 : logb 10 (1 : ℝ) = 0 := by 
        norm_num [logb_one] 
      linarith 
    have h6 : -logb 10 (x^2 + x + 1) < 0 := by 
      linarith 
    have h7 : x * (-logb 10 (x^2 + x + 1)) > 0 := by 
      apply mul_pos_of_neg_of_neg 
      linarith 
      linarith 
    linarith