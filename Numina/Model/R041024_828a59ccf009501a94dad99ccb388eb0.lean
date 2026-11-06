import Mathlib

theorem algebra_216091 (x : ℝ) :
    3 * 4 ^ x + (3 * x - 10) * 2 ^ x + 3 - x = 0 ↔ x = -Real.logb 2 3 ∨ x = 1 := by 
  constructor
  · -- First, solve the equation to get the two solutions.
    intro h 
    have h1 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring
      all_goals norm_num
    have h2 : (4 : ℝ) ^ x = ((2 : ℝ) ^ x) ^ 2 := by
      rw [h1]
      have h3 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by
        calc
          (2 : ℝ) ^ (2 * x) = (2 : ℝ) ^ (x + x) := by ring_nf
          _ = ((2 : ℝ) ^ x) * ((2 : ℝ) ^ x) := by rw [← Real.rpow_add]; ring_nf; all_goals norm_num
          _ = ((2 : ℝ) ^ x) ^ 2 := by ring
      rw [h3]
    rw [h2] at h
    have h3_pos : (2 : ℝ) ^ x > 0 := by positivity
    have h4 : 3 * ((2 : ℝ) ^ x) ^ 2 + (3 * x - 10) * ((2 : ℝ) ^ x) + (3 - x) = 0 := by 
      nlinarith
    have h5 : (3 * ((2 : ℝ) ^ x) - 1) * ((2 : ℝ) ^ x - (3 - x)) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h5) with h6 h7 
    · -- First case: 3 * (2 ^ x) - 1 = 0 
      have h_eq1 : (2 : ℝ) ^ x = 1 / 3 := by linarith 
      have hx1 : x = -Real.logb 2 3 := by
        have h8 : x = Real.logb 2 ((2 : ℝ) ^ x) := by 
          rw [Real.logb_rpow]
          all_goals norm_num 
        rw [h_eq1] at h8 
        have h9 : Real.logb 2 (1 / 3) = - Real.logb 2 3 := by 
          simp [Real.logb_div, Real.logb_one] 
        rw [h9] at h8 
        linarith 
      left 
      exact hx1 
    · -- Second case: (2 ^ x) - (3 - x) = 0 
      have h_eq2 : (2 : ℝ) ^ x = 3 - x := by linarith 
      have hx_eq1 : x = 1 := by 
        by_cases h2x1 : x < 1 
        · -- Assume x < 1 
          have h5 : (2 : ℝ) ^ x < (2 : ℝ) ^ (1 : ℝ) := by 
            apply Real.rpow_lt_rpow_of_exponent_lt 
            all_goals norm_num 
            all_goals linarith 
          have h6 : (3 - x : ℝ) > (2 : ℝ) := by linarith 
          nlinarith [h_eq2, h5, h6, Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x] 
        by_cases h2x2 : x > 1 
        · -- Assume x > 1 
          have h5 : (2 : ℝ) ^ x > (2 : ℝ) ^ (1 : ℝ) := by 
            apply Real.rpow_lt_rpow_of_exponent_lt 
            all_goals norm_num 
            all_goals linarith 
          have h6 : (3 - x : ℝ) < (2 : ℝ) := by linarith 
          nlinarith [h_eq2, h5, h6, Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) x] 
        linarith 
      right 
      exact hx_eq1 
  · -- Verify the solutions satisfy the equation. 
    rintro (h1 | h2) 
    · -- First case: x = - log_2 3 
      rw [h1] 
      have h1' : (2 : ℝ) ^ (-Real.logb 2 3 : ℝ) = 1 / 3 := by 
        have h2 : (2 : ℝ) ^ (-Real.logb 2 3 : ℝ) = ((2 : ℝ) ^ Real.logb 2 3)⁻¹ := by 
          rw [← Real.rpow_neg] 
          ring 
          all_goals linarith 
        have h3 : (2 : ℝ) ^ Real.logb 2 3 = 3 := by 
          rw [Real.rpow_logb] 
          all_goals norm_num 
        rw [h2, h3] 
        all_goals norm_num 
      have h2' : (4 : ℝ) ^ (-Real.logb 2 3 : ℝ) = 1 / 9 := by 
        have h41 : (4 : ℝ) ^ (-Real.logb 2 3 : ℝ) = (2 : ℝ) ^ (2 * (-Real.logb 2 3 : ℝ)) := by 
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num] 
          rw [← Real.rpow_mul] 
          ring 
          all_goals norm_num 
        have h42 : (2 : ℝ) ^ (2 * (-Real.logb 2 3 : ℝ)) = ((2 : ℝ) ^ (-Real.logb 2 3 : ℝ)) ^ 2 := by 
          calc 
            (2 : ℝ) ^ (2 * (-Real.logb 2 3 : ℝ)) = (2 : ℝ) ^ (2 * (-Real.logb 2 3 : ℝ)) := by ring_nf 
            _ = ((2 : ℝ) ^ (-Real.logb 2 3 : ℝ)) ^ 2 := by 
              rw [← Real.rpow_natCast, ← Real.rpow_mul] 
              ring 
              all_goals positivity 
        rw [h41, h42, h1'] 
        all_goals norm_num 
      rw [h2'] 
      field_simp [h1'] 
      <;> ring_nf 
    · -- Second case: x = 1 
      rw [h2] 
      norm_num