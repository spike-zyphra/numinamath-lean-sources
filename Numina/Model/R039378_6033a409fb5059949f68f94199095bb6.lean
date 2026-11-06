import Mathlib

open Real

theorem inequalities_307093 {x y : ℝ} (h : logb 2 3 ^ x - logb 5 3 ^ x ≥ logb 2 3 ^ (-y) - logb 5 3 ^ (-y)) :
    x + y ≥ 0 := by
  by_contra h1
  push_neg at h1
  have h2 : x < - y := by linarith 
  have h3 : logb 2 3 > 1 := by 
    have h1 : logb 2 3 > logb 2 2 := by
      apply Real.logb_lt_logb
      all_goals linarith
    have h2 : logb 2 2 = 1 := by 
      rw [logb_self_eq_one]
      all_goals linarith
    linarith [h1, h2]
  have h4 : 0 < logb 5 3 := by
    apply logb_pos
    all_goals linarith
  have h5 : logb 5 3 < 1 := by
    have h1 : logb 5 3 < logb 5 5 := by
      apply Real.logb_lt_logb
      all_goals linarith
    have h2 : logb 5 5 = 1 := by 
      rw [logb_self_eq_one]
      all_goals linarith
    linarith [h1, h2]
  have h6 : logb 2 3 ^ x < logb 2 3 ^ (- y) := by
    have h7 : logb 2 3 > (1 : ℝ) := h3
    have h8 : x < (- y) := by linarith [h2]
    have h9 : logb 2 3 ^ x < logb 2 3 ^ (- y) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals
        linarith
    linarith
  have h7 : logb 5 3 ^ x > logb 5 3 ^ (- y) := by
    have h7 : logb 5 3 < (1 : ℝ) := h5
    have h8 : logb 5 3 > (0 : ℝ) := h4
    have h9 : x < (- y) := by linarith [h2]
    have h10 : logb 5 3 ^ x > logb 5 3 ^ (- y) := by
      apply Real.rpow_lt_rpow_of_exponent_gt
      all_goals
        nlinarith
    linarith
  have h8 : logb 2 3 ^ x - logb 5 3 ^ x < logb 2 3 ^ (- y) - logb 5 3 ^ (- y) := by
    have h8 : logb 2 3 ^ x < logb 2 3 ^ (- y) := h6
    have h9 : logb 5 3 ^ x > logb 5 3 ^ (- y) := h7
    linarith
  linarith [h8, h]