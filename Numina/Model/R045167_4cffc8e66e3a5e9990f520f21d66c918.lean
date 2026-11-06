import Mathlib

open Real

theorem algebra_95090 {x : ℝ} (hx : 0 < x) :
abs (logb 6 x - logb 6 9) = 2 * abs (logb 6 10 - 1) ↔ x = 25 ∨ x = 81 / 25 := by
  constructor
  · -- Assume abs (logb 6 x - logb 6 9) = 2 * abs (logb 6 10 - 1), prove x = 25 ∨ x = 81 / 25
    intro h_eq
    have h1 : logb 6 10 - 1 = logb 6 (5 / 3) := by
      have h2 : logb 6 (5 / 3) = logb 6 10 - logb 6 6 := by
        rw [show (5 / 3 : ℝ) = (10 : ℝ) / (6 : ℝ) by norm_num]
        rw [logb_div (by norm_num) (by norm_num)]
      have h3 : logb 6 6 = 1 := by
        rw [logb_self_eq_one]
        all_goals norm_num
      linarith [h2, h3]
    have h1' : abs (logb 6 10 - 1) = abs (logb 6 (5 / 3)) := by
      rw [h1]
    have h2 : abs (logb 6 x - logb 6 9) = abs (logb 6 (x / 9)) := by
      have h3 : logb 6 x - logb 6 9 = logb 6 (x / 9) := by
        rw [← logb_div (by positivity) (by positivity)]
      rw [h3]
    rw [h2, h1'] at h_eq
    have h3 : abs (logb 6 (x / 9)) = 2 * abs (logb 6 (5 / 3)) := h_eq
    have h4 : logb 6 (5 / 3) > 0 := by
      apply logb_pos
      all_goals
        norm_num
    have h5 : abs (logb 6 (5 / 3)) = logb 6 (5 / 3) := by
      rw [abs_of_nonneg]
      linarith
    rw [h5] at h3
    cases abs_cases (logb 6 (x / 9)) with
    | inl h6 =>
      have h7 : logb 6 (x / 9) = 2 * (logb 6 (5 / 3)) := by linarith
      have h8 : logb 6 (x / 9) = logb 6 ((5 / 3) ^ 2) := by
        have h9 : logb 6 ((5 / 3) ^ 2) = 2 * logb 6 (5 / 3) := by
          simp [logb_pow]
        linarith [h7, h9]
      have h10 : x / 9 = (5 / 3) ^ 2 := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr (show 0 < x / 9 by positivity)) (Set.mem_Ioi.mpr (show 0 < (5 / 3 : ℝ) ^ 2 by positivity)) h8
      have h11 : x = 25 := by
        nlinarith
      left
      exact h11
    | inr h6 =>
      have h7 : logb 6 (x / 9) = -2 * (logb 6 (5 / 3)) := by linarith
      have h8 : logb 6 (x / 9) = logb 6 ((5 / 3) ^ (-2 : ℝ)) := by
        have h10 : logb 6 ((5 / 3) ^ (-2 : ℝ)) = -2 * logb 6 (5 / 3) := by
          rw [Real.logb_rpow_eq_mul_logb_of_pos]
          all_goals
            norm_num
        linarith [h7, h10]
      have h10 : x / 9 = (5 / 3) ^ (-2 : ℝ) := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr (show 0 < x / 9 by positivity)) (Set.mem_Ioi.mpr (show 0 < (5 / 3 : ℝ) ^ (-2 : ℝ) by positivity)) h8
      have h11 : x / 9 = (9 / 25 : ℝ) := by
        have h12 : (5 / 3 : ℝ) ^ (-2 : ℝ) = (9 / 25 : ℝ) := by
          norm_num [Real.rpow_neg, Real.rpow_natCast]
        rw [h12] at h10
        linarith
      have h13 : x = (81 / 25 : ℝ) := by
        nlinarith
      right
      exact h13
  · -- Assume x = 25 or x = 81/25, prove abs (logb 6 x - logb 6 9) = 2 * abs (logb 6 10 - 1)
    rintro (h_eq | h_eq)
    · -- case x = 25
      rw [h_eq]
      have h1 : logb 6 (25 : ℝ) - logb 6 9 = 2 * logb 6 (5 / 3 : ℝ) := by
        have h2 : logb 6 (25 : ℝ) - logb 6 9 = logb 6 ((25 / 9 : ℝ)) := by
          rw [← logb_div (by positivity) (by positivity)]
        have h3 : logb 6 (25 / 9 : ℝ) = 2 * logb 6 (5 / 3 : ℝ) := by
          have h4 : logb 6 (25 / 9 : ℝ) = logb 6 ((5 / 3 : ℝ) ^ 2) := by
            norm_num
          have h5 : logb 6 ((5 / 3 : ℝ) ^ 2) = 2 * logb 6 (5 / 3 : ℝ) := by
            simp [logb_pow]
          linarith [h4, h5]
        linarith [h2, h3]
      have h2 : logb 6 (10 : ℝ) - 1 = logb 6 (5 / 3 : ℝ) := by
        have h3 : logb 6 (10 : ℝ) - 1 = logb 6 (10 : ℝ) - logb 6 (6 : ℝ) := by
          have h5 : logb 6 (6 : ℝ) = 1 := by
            rw [logb_self_eq_one]
            all_goals norm_num
          linarith
        have h4 : logb 6 (10 : ℝ) - logb 6 (6 : ℝ) = logb 6 (10 / 6 : ℝ) := by
          rw [← logb_div (by positivity) (by positivity)]
        have h5 : logb 6 (10 / 6 : ℝ) = logb 6 (5 / 3 : ℝ) := by
          norm_num
        linarith [h3, h4, h5]
      rw [h1, h2]
      have h4 : logb 6 (5 / 3 : ℝ) > 0 := by
        apply logb_pos
        all_goals
          norm_num
      have h5 : abs (2 * logb 6 (5 / 3 : ℝ)) = 2 * abs (logb 6 (5 / 3 : ℝ)) := by
        have h6 : abs (logb 6 (5 / 3 : ℝ)) = logb 6 (5 / 3 : ℝ) := by
          rw [abs_of_pos h4]
        have h7 : abs (2 * logb 6 (5 / 3 : ℝ)) = 2 * (logb 6 (5 / 3 : ℝ)) := by
          have h8 : 2 * logb 6 (5 / 3 : ℝ) > 0 := by
            linarith
          rw [abs_of_pos h8]
        linarith [h7, h6]
      linarith [h5]
    · -- case x = 81/25
      rw [h_eq]
      have h1 : logb 6 (81 / 25 : ℝ) - logb 6 9 = -2 * logb 6 (5 / 3 : ℝ) := by
        have h2 : logb 6 (81 / 25 : ℝ) - logb 6 9 = logb 6 ((81 / 25 / 9 : ℝ)) := by
          rw [← logb_div (by positivity) (by positivity)]
        have h3 : logb 6 ((81 / 25 / 9 : ℝ)) = logb 6 (9 / 25 : ℝ) := by
          norm_num
        have h4 : logb 6 (9 / 25 : ℝ) = -2 * logb 6 (5 / 3 : ℝ) := by
          have h5 : logb 6 (9 / 25 : ℝ) = logb 6 ((3 / 5 : ℝ) ^ 2) := by
            norm_num
          have h6 : logb 6 ((3 / 5 : ℝ) ^ 2) = 2 * logb 6 (3 / 5 : ℝ) := by
            simp [logb_pow]
          have h7 : logb 6 (3 / 5 : ℝ) = - logb 6 (5 / 3 : ℝ) := by
            have h8 : logb 6 (3 / 5 : ℝ) + logb 6 (5 / 3 : ℝ) = 0 := by
              have h10 : logb 6 (3 / 5 : ℝ) + logb 6 (5 / 3 : ℝ) = logb 6 ((3 / 5 : ℝ) * (5 / 3 : ℝ)) := by
                rw [logb_mul (by positivity) (by positivity)]
              have h11 : logb 6 ((3 / 5 : ℝ) * (5 / 3 : ℝ)) = logb 6 (1 : ℝ) := by
                norm_num
              have h12 : logb 6 (1 : ℝ) = 0 := by
                simp
              linarith [h10, h11, h12]
            linarith
          linarith [h5, h6, h7]
        linarith [h2, h3, h4]
      have h2 : logb 6 (10 : ℝ) - 1 = logb 6 (5 / 3 : ℝ) := by
        have h3 : logb 6 (10 : ℝ) - 1 = logb 6 (10 : ℝ) - logb 6 (6 : ℝ) := by
          have h5 : logb 6 (6 : ℝ) = 1 := by
            rw [logb_self_eq_one]
            all_goals norm_num
          linarith
        have h4 : logb 6 (10 : ℝ) - logb 6 (6 : ℝ) = logb 6 (10 / 6 : ℝ) := by
          rw [← logb_div (by positivity) (by positivity)]
        have h5 : logb 6 (10 / 6 : ℝ) = logb 6 (5 / 3 : ℝ) := by
          norm_num
        linarith [h3, h4, h5]
      rw [h1, h2]
      have h4 : logb 6 (5 / 3 : ℝ) > 0 := by
        apply logb_pos
        all_goals
          norm_num
      have h5 : abs (-2 * logb 6 (5 / 3 : ℝ)) = 2 * abs (logb 6 (5 / 3 : ℝ)) := by
        have h6 : abs (logb 6 (5 / 3 : ℝ)) = logb 6 (5 / 3 : ℝ) := by
          rw [abs_of_pos h4]
        have h7 : abs (-2 * logb 6 (5 / 3 : ℝ)) = 2 * (logb 6 (5 / 3 : ℝ)) := by
          have h8 : abs (-2 * logb 6 (5 / 3 : ℝ)) = abs (-2 : ℝ) * abs (logb 6 (5 / 3 : ℝ) : ℝ) := by
            rw [abs_mul]
          have h9 : abs (-2 : ℝ) = 2 := by
            norm_num
          have h10 : abs (logb 6 (5 / 3 : ℝ) : ℝ) = logb 6 (5 / 3 : ℝ) := by
            apply abs_of_pos h4
          rw [h8, h9, h10]
          all_goals linarith
        linarith [h7, h6]
      linarith [h5]