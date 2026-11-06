import Mathlib

open Real

theorem algebra_247120 :
    {x : ℝ | 0 < x ∧ (3 / 4 : ℝ) ^ logb 10 x + (4 / 3 : ℝ) ^ logb 10 x = 25 / 12} = {1/10, 10} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x is a solution 
    rintro ⟨hx, heq⟩
    have h1 : (3 / 4 : ℝ) ^ logb 10 x + (4 / 3 : ℝ) ^ logb 10 x = 25 / 12 := heq 
    have h2 : (4 / 3 : ℝ) ^ logb 10 x = ((3 / 4 : ℝ) ^ logb 10 x)⁻¹ := by
      have h5 : (4 / 3 : ℝ) ^ logb 10 x = (3 / 4 : ℝ) ^ (- logb 10 x : ℝ) := by
        have h6 : (4 / 3 : ℝ) = (3 / 4 : ℝ) ^ (-1 : ℝ) := by 
          norm_num
        have h7 : (4 / 3 : ℝ) ^ logb 10 x = ((3 / 4 : ℝ) ^ (-1 : ℝ)) ^ logb 10 x := by 
          rw [show (4 / 3 : ℝ) = (3 / 4 : ℝ) ^ (-1 : ℝ) by norm_num] 
        have h8 : ((3 / 4 : ℝ) ^ (-1 : ℝ)) ^ logb 10 x = (3 / 4 : ℝ) ^ ( (-1 : ℝ) * (logb 10 x) ) := by 
          rw [← Real.rpow_mul]
          all_goals linarith
        have h9 : (3 / 4 : ℝ) ^ ( (-1 : ℝ) * (logb 10 x) ) = (3 / 4 : ℝ) ^ (- logb 10 x : ℝ) := by 
          ring_nf 
        rw [h7, h8, h9]
      have h7 : (3 / 4 : ℝ) ^ (- logb 10 x : ℝ) = ((3 / 4 : ℝ) ^ (logb 10 x : ℝ))⁻¹ := by 
        have h7' : (3 / 4 : ℝ) ^ (- logb 10 x : ℝ) = ((3 / 4 : ℝ) ^ (logb 10 x : ℝ))⁻¹ := by 
          rw [show (- logb 10 x : ℝ) = - (logb 10 x : ℝ) by ring]
          rw [Real.rpow_neg]
          all_goals linarith 
        exact h7'
      rw [h5, h7]
    rw [h2] at h1
    have h3 : ((3 / 4 : ℝ) ^ logb 10 x) + ((3 / 4 : ℝ) ^ logb 10 x)⁻¹ = 25 / 12 := h1 
    have h4 : ((3 / 4 : ℝ) ^ logb 10 x) ≠ 0 := by
      positivity 
    have h5 : ((3 / 4 : ℝ) ^ logb 10 x) ^ 2 + 1 = (25 / 12) * ((3 / 4 : ℝ) ^ logb 10 x) := by 
      have h6 : ((3 / 4 : ℝ) ^ logb 10 x) + ((3 / 4 : ℝ) ^ logb 10 x)⁻¹ = 25 / 12 := h3 
      field_simp [h4] at h6 ⊢ 
      nlinarith 
    have h6 : 12 * ((3 / 4 : ℝ) ^ logb 10 x) ^ 2 - 25 * ((3 / 4 : ℝ) ^ logb 10 x) + 12 = 0 := by 
      nlinarith 
    have h7 : ((3 / 4 : ℝ) ^ logb 10 x - 4 / 3) * ((3 / 4 : ℝ) ^ logb 10 x - 3 / 4) = 0 := by  nlinarith 
    cases' (mul_eq_zero.mp h7) with h8 h9 
    · -- Case 1: ((3 / 4 : ℝ) ^ logb 10 x) = 4 / 3 
      have ha1 : (3 / 4 : ℝ) ^ logb 10 x = 4 / 3 := by 
        linarith 
      have h8 : logb 10 x = -1 := by
        have h9 : log ((3 / 4 : ℝ) ^ logb 10 x) = log (4 / 3) := by 
          rw [ha1] 
        have h10 : log ((3 / 4 : ℝ) ^ logb 10 x) = logb 10 x * log (3 / 4) := by 
          rw [log_rpow] 
          all_goals norm_num 
        have h11 : log (4 / 3) = log 4 - log 3 := by 
          field_simp [log_div] 
        have h12 : log (3 / 4) = log 3 - log 4 := by 
          field_simp [log_div] 
        rw [h10, h11, h12] at h9 
        have h13 : log 3 - log 4 ≠ 0 := by 
          have h14 : log 3 > 0 := by 
            apply log_pos 
            all_goals norm_num 
          have h15 : log 4 > 0 := by 
            apply log_pos 
            all_goals norm_num 
          have h16 : log 3 ≠ log 4 := by 
            by_contra h
            have h17 : (3 : ℝ) = (4 : ℝ) := by 
              have h18 : log 3 = log 4 := by 
                linarith [h] 
              have h17 : (3 : ℝ) = (4 : ℝ) := by 
                have h18' : log 3 = log 4 := by linarith [h]
                have h19 : (3 : ℝ) = (4 : ℝ) := by 
                  exact log_injOn_pos (Set.mem_Ioi.mpr (show 0 < (3 : ℝ) by norm_num)) (Set.mem_Ioi.mpr (show 0 < (4 : ℝ) by norm_num)) h18'
                exact h19 
              exact h17
            all_goals linarith 
          intro h15 
          apply h16 
          linarith 
        have h14 : logb 10 x = -1 := by 
          apply (mul_left_inj' h13).mp 
          linarith 
        exact h14 
      have hx1 : x = 1 / 10 := by 
        have h1 : logb 10 x = -1 := h8 
        have h2 : x = (10 : ℝ) ^ (-1 : ℝ) := by 
          rw [logb_eq_iff_rpow_eq] at h1 
          · linarith 
          all_goals linarith 
        rw [h2] 
        norm_num 
      simp [hx1] 
    · -- Case 2: ((3 / 4 : ℝ) ^ logb 10 x) = 3 / 4 
      have ha1 : (3 / 4 : ℝ) ^ logb 10 x = 3 / 4 := by 
        linarith 
      have h8 : logb 10 x = 1 := by 
        have h9 : log ((3 / 4 : ℝ) ^ logb 10 x) = log (3 / 4) := by 
          rw [ha1] 
        have h10 : log ((3 / 4 : ℝ) ^ logb 10 x) = logb 10 x * log (3 / 4) := by 
          rw [log_rpow] 
          all_goals norm_num 
        have h11 : log (3 / 4) = log 3 - log 4 := by 
          field_simp [log_div] 
        rw [h10, h11] at h9 
        have h13 : log 3 - log 4 ≠ 0 := by 
          have h14 : log 3 > 0 := by 
            apply log_pos 
            all_goals norm_num 
          have h15 : log 4 > 0 := by 
            apply log_pos 
            all_goals norm_num 
          have h16 : log 3 ≠ log 4 := by 
            by_contra h
            have h17 : (3 : ℝ) = (4 : ℝ) := by 
              have h18 : log 3 = log 4 := by 
                linarith [h] 
              have h17 : (3 : ℝ) = (4 : ℝ) := by 
                have h18' : log 3 = log 4 := by linarith [h]
                have h19 : (3 : ℝ) = (4 : ℝ) := by 
                  exact log_injOn_pos (Set.mem_Ioi.mpr (show 0 < (3 : ℝ) by norm_num)) (Set.mem_Ioi.mpr (show 0 < (4 : ℝ) by norm_num)) h18'
                exact h19 
              exact h17 
            all_goals linarith 
          intro h15 
          apply h16 
          linarith 
        have h14 : logb 10 x = 1 := by 
          apply (mul_left_inj' h13).mp 
          linarith 
        exact h14 
      have hx1 : x = 10 := by 
        have h1 : logb 10 x = 1 := h8 
        have h2 : x = (10 : ℝ) ^ (1 : ℝ) := by 
          rw [logb_eq_iff_rpow_eq] at h1 
          · linarith 
          all_goals linarith 
        rw [h2] 
        norm_num 
      simp [hx1] 
  · -- Assume x is in {1/10, 10}, then it is a solution. 
    rintro (rfl | rfl)
    · -- Case x = 1/10 
      constructor 
      · norm_num 
      · -- Show the equation is satisfied 
        have h10 : logb 10 (1 / 10 : ℝ) = -1 := by 
          rw [logb_eq_iff_rpow_eq] <;> norm_num 
        rw [h10] 
        norm_num 
    · -- Case x = 10 
      constructor 
      · norm_num 
      · -- Show the equation is satisfied 
        have h10 : logb 10 (10 : ℝ) = 1 := by 
          rw [logb_eq_iff_rpow_eq] <;> norm_num 
        rw [h10] 
        norm_num