import Mathlib

open Real

theorem calculus_121027 : tan (Real.sqrt (5 * π)) - 1 > 0 := by
  have h1 : Real.sqrt (5 * π) > Real.pi := by
    have h2 : (Real.sqrt (5 * π))^2 > Real.pi ^ 2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 5 * π by positivity : (5 * π : ℝ) ≥ 0), Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg (5 * π)]
    nlinarith [Real.sqrt_nonneg (5 * π)]
  have h2 : Real.sqrt (5 * π) - Real.pi > 0 := by linarith
  have h3 : Real.sqrt (5 * π) = Real.pi + (Real.sqrt (5 * π) - Real.pi) := by linarith
  rw [h3]
  have htan : tan (Real.pi + (Real.sqrt (5 * π) - Real.pi)) = tan (Real.sqrt (5 * π) - Real.pi) := by
    rw [show Real.pi + (Real.sqrt (5 * π) - Real.pi) = Real.sqrt (5 * π) - Real.pi + Real.pi by ring]
    rw [tan_add_pi]
  rw [htan]
  have h4 : Real.sqrt (5 * π) - Real.pi > 0 := by linarith
  have h5 : Real.sqrt (5 * π) - Real.pi > Real.pi / 4 := by
    have h5 : Real.sqrt (5 * π) > Real.pi + Real.pi / 4 := by
      have h1 : Real.sqrt (5 * π) > Real.pi + Real.pi / 4 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ 5 * π by positivity : (5 * π : ℝ) ≥ 0), sq_nonneg (Real.sqrt (5 * π) - (Real.pi + Real.pi / 4)), sq_pos_of_pos (show 0 < Real.pi by positivity), sq_nonneg (Real.sqrt (5 * π) ^ 2 - (Real.pi + Real.pi / 4) ^ 2), Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg (5 * π)]
      linarith
    linarith
  have h7 : tan (Real.sqrt (5 * π) - Real.pi) > 1 := by
    have htan1 : tan (Real.pi / 4) = 1 := Real.tan_pi_div_four
    have htan2 : Real.sqrt (5 * π) - Real.pi > Real.pi / 4 := h5
    have h4_pos : 0 < Real.sqrt (5 * π) - Real.pi := by linarith [Real.sqrt_nonneg (5 * π), h4]
    have h7 : tan (Real.sqrt (5 * π) - Real.pi) > tan (Real.pi / 4) := by
      have h_pos : 0 < Real.sqrt (5 * π) - Real.pi := by linarith [Real.sqrt_nonneg (5 * π), h4]
      have h_lt : Real.sqrt (5 * π) - Real.pi < Real.pi / 2 := by
        by_contra h
        push_neg at h
        have h8 : Real.sqrt (5 * π) - Real.pi ≥ Real.pi / 2 := by linarith [h]
        have h9 : Real.sqrt (5 * π) ≥ Real.pi + Real.pi / 2 := by linarith [h8]
        have h10 : (Real.sqrt (5 * π)) ^ 2 ≥ (Real.pi + Real.pi / 2)^2 := by nlinarith [Real.sqrt_nonneg (5 * π), Real.sq_sqrt (show (0 : ℝ) ≤ 5 * π by positivity : (5 * π : ℝ) ≥ 0), sq_nonneg (Real.sqrt (5 * π) - (Real.pi + Real.pi / 2)), Real.pi_gt_31415, Real.pi_lt_31416]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 * π by positivity : (5 * π : ℝ) ≥ 0), Real.pi_gt_31415, Real.pi_lt_31416, Real.sqrt_nonneg (5 * π)]
      apply Real.tan_lt_tan_of_lt_of_lt_pi_div_two
      all_goals
      nlinarith [Real.sqrt_nonneg (5 * π), Real.pi_pos, sq_nonneg (Real.sqrt (5 * π) - Real.pi), Real.pi_gt_31415, Real.pi_lt_31416]
    have : tan (Real.pi / 4) = 1 := htan1
    have : tan (Real.sqrt (5 * π) - Real.pi) > tan (Real.pi / 4) := h7
    linarith
  linarith