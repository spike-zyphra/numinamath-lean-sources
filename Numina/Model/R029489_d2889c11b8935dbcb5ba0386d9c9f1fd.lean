import Mathlib

open Real

theorem inequalities_98684 {x y : ℝ}
    (h : (logb 2 3)^x - (logb 5 3)^x ≥ (logb 2 3)^(-y) - (logb 5 3)^(-y)) :
    x + y ≥ 0 := by
  by_contra h1
  push_neg at h1
  have h2 : logb 2 3 > 1 := by
    have h1 : logb 2 3 > logb 2 2 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h2 : logb 2 2 = 1 := by
      rw [logb_self_eq_one]
      all_goals norm_num
    linarith
  have h3 : logb 5 3 > 0 := by
    have h4 : logb 5 3 > 0 := by
      apply logb_pos
      all_goals norm_num
    linarith
  have h4 : logb 2 3 ^ x < logb 2 3 ^ (-y) := by
    have h5 : logb 2 3 > 1 := h2
    have h6 : x < -y := by linarith
    have h7 : logb 2 3 ^ x < logb 2 3 ^ (-y) := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      all_goals linarith
    linarith
  have h5 : logb 5 3 ^ x > logb 5 3 ^ (-y) := by
    have h34 : logb 5 3 > 0 := h3
    have h35 : logb 5 3 < 1 := by
      have h7 : logb 5 3 < logb 5 5 := by
        apply Real.logb_lt_logb
        all_goals norm_num
      have h8 : logb 5 5 = 1 := by
        rw [logb_self_eq_one]
        all_goals norm_num
      linarith
    have h6 : x < -y := by linarith
    have h9 : logb 5 3 ^ x > logb 5 3 ^ (-y) := by
      apply Real.rpow_lt_rpow_of_exponent_gt
      all_goals
      nlinarith
    linarith
  have h54 : (logb 2 3) ^ x - (logb 5 3) ^ x < (logb 2 3) ^ (-y) - (logb 5 3) ^ (-y) := by
    linarith [h4, h5]
  linarith