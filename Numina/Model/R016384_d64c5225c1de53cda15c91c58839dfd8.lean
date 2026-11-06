import Mathlib

theorem algebra_203148 : (11 : ℝ) ^ (Real.logb 10 121) > 10 * (10 ^ (Real.logb 10 11) ^ 2) + 11 := by 
  have h1 : Real.logb 10 121 = 2 * Real.logb 10 11 := by
    calc
      Real.logb 10 121 = Real.logb 10 (11 ^ 2) := by norm_num
      _ = 2 * Real.logb 10 11 := by simp [Real.logb_pow]
  have h2 : (11 : ℝ) ^ (Real.logb 10 121) = (11 : ℝ) ^ (2 * Real.logb 10 11) := by
    rw [h1]
  have h3 : (11 : ℝ) ^ (2 * Real.logb 10 11) = ((11 : ℝ) ^ (Real.logb 10 11)) ^ 2 := by
    calc
      (11 : ℝ) ^ (2 * Real.logb 10 11) = ((11 : ℝ) ^ (Real.logb 10 11 : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      _ = ((11 : ℝ) ^ (Real.logb 10 11)) ^ 2 := by norm_num
  have h7 : (11 : ℝ) ^ (Real.logb 10 121) = ((11 : ℝ) ^ (Real.logb 10 11)) ^ 2 := by
    rw [h2, h3]
  have h8 : (11 : ℝ) ^ (Real.logb 10 11) = (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) := by
    have h24 : Real.logb 10 ((11 : ℝ) ^ (Real.logb 10 11)) = Real.logb 10 ((10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11)) := by
      have h21 : Real.logb 10 ((11 : ℝ) ^ (Real.logb 10 11)) = (Real.logb 10 11) * (Real.logb 10 11) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals norm_num
        all_goals linarith
      have eq4 : Real.logb 10 ((10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11)) = (Real.logb 10 11 * Real.logb 10 11) * Real.logb 10 (10 : ℝ) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals norm_num
        all_goals linarith
      have h22 : Real.logb 10 ((10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11)) = (Real.logb 10 11) * (Real.logb 10 11) := by
        rw [eq4]
        have h16 : Real.logb 10 (10 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
        rw [h16]
        all_goals ring_nf
      linarith [h21, h22]
      all_goals norm_num
      all_goals linarith
      all_goals norm_num
      all_goals linarith
      all_goals norm_num
      all_goals linarith
    have h23 : (11 : ℝ) ^ (Real.logb 10 11) > 0 := by positivity
    have h25 : (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) > 0 := by positivity
    have h26 : (11 : ℝ) ^ (Real.logb 10 11) = (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) := by
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h24
      all_goals norm_num
      <;> norm_num
      <;> norm_num
      all_goals try { norm_num }
      all_goals try { positivity }
    exact h26
  have h11 : ( (11 : ℝ) ^ (Real.logb 10 121) ) - (10 * (10 ^ (Real.logb 10 11) ^ 2) + 11) > 0 := by
    have h17 : ( (11 : ℝ) ^ (Real.logb 10 121) ) - (10 * (10 ^ (Real.logb 10 11) ^ 2) + 11) =
        ( (11 : ℝ) ^ (Real.logb 10 11) ) ^ 2 - (10 * (10 ^ (Real.logb 10 11) ^ 2) + 11) := by
      rw [h7]

    rw [h17]
    have h20 : ( (11 : ℝ) ^ (Real.logb 10 11) ) ^ 2 - (10 * (10 ^ (Real.logb 10 11) ^ 2) + 11) > 0 := by
      have h24 : (11 : ℝ) ^ (Real.logb 10 11) = (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) := by
        linarith [h8]
      have h25 : (10 ^ (Real.logb 10 11) ^ 2 : ℝ) = (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) := by
        have h28 : (Real.logb 10 11 : ℝ) ^ 2 = (Real.logb 10 11 * Real.logb 10 11 : ℝ) := by
          ring
        rw [h28]
        all_goals norm_num
        all_goals try { norm_num }
        all_goals try { tauto }
        all_goals try { linarith }

      rw [h24, h25]
      -- Now the expression is (10^{val})^2 - (10 * 10^{val} + 11) > 0
      -- which is Y^2 - 10Y - 11 > 0, given h15: Y > 11
      have h16 : (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) > (11 : ℝ) := by
        have h31 : (11 : ℝ) ^ (Real.logb 10 11) = (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) := h8
        have h32 : (11 : ℝ) ^ (Real.logb 10 11) > (11 : ℝ) := by
          have h31' : Real.logb 10 11 > (1 : ℝ) := by
            have h32' : Real.logb 10 11 > Real.logb 10 10 := by
              apply Real.logb_lt_logb
              all_goals linarith
            have h33' : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
            linarith [h32', h33']
            all_goals norm_num
            all_goals norm_num
          have eq4 : (11 : ℝ) ^ (Real.logb 10 11) = (11 : ℝ) ^ (Real.logb 10 11 : ℝ) := by norm_num
          have h29 : (11 : ℝ) ^ (Real.logb 10 11 : ℝ) > (11 : ℝ) ^ (1 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals linarith
            all_goals linarith
          have eq5 : (11 : ℝ) ^ (1 : ℝ) = (11 : ℝ) := by norm_num
          nlinarith [eq4, h29, eq5]
        nlinarith
      have h17_pos : (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) > (0 : ℝ) := by
        have h14 : (10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) > (0 : ℝ) := by positivity
        linarith
      nlinarith [sq_nonneg ((10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) - 11), sq_nonneg ((10 : ℝ) ^ (Real.logb 10 11 * Real.logb 10 11) + 1), h16, h17_pos]

    linarith
  nlinarith [h11]
  all_goals norm_num
  all_goals try { norm_num }
  all_goals try { positivity }