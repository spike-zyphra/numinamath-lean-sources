import Mathlib

theorem algebra_231855 :
    {x : ℝ | x > 0 ∧ (x / 2) ^ Real.logb 10 x = 40000} = {200, 1/100} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward implication: if x is a solution, then x ∈ {200, 1/100}
    intro h
    rcases h with ⟨hx_pos, heq⟩
    have h1 : Real.logb 10 ((x / 2) ^ Real.logb 10 x) = Real.logb 10 (40000 : ℝ) := by
      rw [heq]
    have h2 : Real.logb 10 ((x / 2) ^ Real.logb 10 x) = Real.logb 10 x * Real.logb 10 (x / 2 : ℝ) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
      have : x / 2 > 0 := by
        linarith
      all_goals nlinarith
    rw [h2] at h1
    have h3 : Real.logb 10 (x / 2 : ℝ) = Real.logb 10 x - Real.logb 10 (2 : ℝ) := by
      rw [Real.logb_div (by positivity) (by positivity)]
    rw [h3] at h1
    have h4 : Real.logb 10 (40000 : ℝ) = 2 * Real.logb 10 (2 : ℝ) + 4 := by
      calc
        Real.logb 10 (40000 : ℝ) = Real.logb 10 (4 * (10000 : ℝ)) := by norm_num
        _ = Real.logb 10 (4 : ℝ) + Real.logb 10 (10000 : ℝ) := by rw [Real.logb_mul (by norm_num) (by norm_num)]
        _ = Real.logb 10 (4 : ℝ) + Real.logb 10 ((10 : ℝ) ^ 4) := by norm_num
        _ = Real.logb 10 (4 : ℝ) + (4 : ℝ) := by 
          have h10 : Real.logb 10 ((10 : ℝ) ^ 4) = (4 : ℝ) := by 
            simp [Real.logb_pow]
          rw [h10]
        _ = (2 * Real.logb 10 (2 : ℝ) : ℝ) + (4 : ℝ) := by
          have h12 : Real.logb 10 (4 : ℝ) = 2 * Real.logb 10 (2 : ℝ) := by
            calc
              Real.logb 10 (4 : ℝ) = Real.logb 10 ((2 : ℝ) ^ 2) := by norm_num
              _ = 2 * Real.logb 10 (2 : ℝ) := by simp [Real.logb_pow]
          have h14 : Real.logb 10 (4 : ℝ) = 2 * Real.logb 10 (2 : ℝ) := h12
          linarith
        _ = (2 * Real.logb 10 (2 : ℝ) + 4 : ℝ) := by ring
    rw [h4] at h1
    have h5 : (Real.logb 10 x - (Real.logb 10 (2 : ℝ) + 2)) * (Real.logb 10 x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case h6
      have h8 : Real.logb 10 x = Real.logb 10 (200 : ℝ) := by
        have h9 : Real.logb 10 (200 : ℝ) = Real.logb 10 (2 : ℝ) + 2 := by
          calc
            Real.logb 10 (200 : ℝ) = Real.logb 10 (2 * (100 : ℝ)) := by norm_num
            _ = Real.logb 10 (2 : ℝ) + Real.logb 10 (100 : ℝ) := by rw [Real.logb_mul (by norm_num) (by norm_num)]
            _ = Real.logb 10 (2 : ℝ) + Real.logb 10 ((10 : ℝ) ^ 2) := by norm_num
            _ = Real.logb 10 (2 : ℝ) + (2 : ℝ) := by 
              have h10 : Real.logb 10 ((10 : ℝ) ^ 2) = (2 : ℝ) := by 
                simp [Real.logb_pow]
              rw [h10]
            _ = Real.logb 10 (2 : ℝ) + 2 := by ring
        have h12 : Real.logb 10 x = Real.logb 10 (2 : ℝ) + 2 := by
          linarith [h6, h9]
        linarith [h12, h9]
      have h11 : x = (200 : ℝ) := by
        apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr hx_pos) (Set.mem_Ioi.mpr (by norm_num)) h8
      left
      tauto
    · -- Case h7
      have h8 : Real.logb 10 x = Real.logb 10 (1/100 : ℝ) := by
        have h9 : Real.logb 10 (1/100 : ℝ) = -2 := by
          calc
            Real.logb 10 (1/100 : ℝ) = Real.logb 10 (1 : ℝ) - Real.logb 10 (100 : ℝ) := by field_simp [Real.logb_div]
            _ = 0 - Real.logb 10 (100 : ℝ) := by norm_num
            _ = - (Real.logb 10 (100 : ℝ) ) := by ring
            _ = - (Real.logb 10 ((10 : ℝ) ^ 2) ) := by norm_num
            _ = - (2 : ℝ) := by 
              have h10 : Real.logb 10 ((10 : ℝ) ^ 2) = (2 : ℝ) := by
                simp [Real.logb_pow]
              rw [h10]
            _ = -2 := by ring
        have h12 : Real.logb 10 x = -2 := by
          linarith [h7, h9]
        linarith [h12, h9]
      have h11 : x = (1/100 : ℝ) := by
        apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr hx_pos) (Set.mem_Ioi.mpr (by norm_num)) h8
      right
      tauto
  · -- Backward implication: if x ∈ {200, 1/100}, then x is a solution
    rintro (rfl | rfl)
    · -- When x = 200
      constructor
      · norm_num
      · -- Show that (200/2)^logb 10 200 = 40000
        have h1 : Real.logb 10 (200 : ℝ) = Real.logb 10 (2 : ℝ) + 2 := by
          calc
            Real.logb 10 (200 : ℝ) = Real.logb 10 (2 * (100 : ℝ)) := by norm_num
            _ = Real.logb 10 (2 : ℝ) + Real.logb 10 (100 : ℝ) := by rw [Real.logb_mul (by norm_num) (by norm_num)]
            _ = Real.logb 10 (2 : ℝ) + Real.logb 10 ((10 : ℝ) ^ 2) := by norm_num
            _ = Real.logb 10 (2 : ℝ) + (2 : ℝ) := by 
              have h10 : Real.logb 10 ((10 : ℝ) ^ 2) = (2 : ℝ) := by
                simp [Real.logb_pow]
              rw [h10]
            _ = Real.logb 10 (2 : ℝ) + 2 := by ring
        rw [h1]
        have h7 : ( (200 : ℝ) / 2 : ℝ ) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) = (40000 : ℝ) := by
          have h13 : ( (200 : ℝ) / 2 : ℝ ) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) = (100 : ℝ) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) := by
            norm_num
          rw [h13]
          have h17 : (100 : ℝ) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) = 40000 := by
            have h13 : (100 : ℝ) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) = (10 : ℝ) ^ (2 * (Real.logb 10 (2 : ℝ) + 2 : ℝ) : ℝ) := by
              have h14 : (100 : ℝ) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) = ((10 : ℝ) ^ (2 : ℝ)) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) := by
                norm_num
              have h15 : ((10 : ℝ) ^ (2 : ℝ)) ^ (Real.logb 10 (2 : ℝ) + 2 : ℝ) = (10 : ℝ) ^ (2 * (Real.logb 10 (2 : ℝ) + 2 : ℝ) : ℝ) := by
                rw [← Real.rpow_mul]
                ring
                all_goals norm_num
              rw [h14, h15]
            rw [h13]
            have h17 : (10 : ℝ) ^ (2 * (Real.logb 10 (2 : ℝ) + 2 : ℝ) : ℝ) = 40000 := by
              have h18 : 2 * (Real.logb 10 (2 : ℝ) + 2 : ℝ) = 4 + 2 * Real.logb 10 (2 : ℝ) := by
                ring
              rw [h18]
              have h19 : (10 : ℝ) ^ (4 + 2 * Real.logb 10 (2 : ℝ) : ℝ) = (10 : ℝ) ^ (4 : ℝ) * (10 : ℝ) ^ (2 * Real.logb 10 (2 : ℝ) : ℝ) := by
                rw [← Real.rpow_add]
                ring
                all_goals
                  norm_num
              rw [h19]
              have h20 : (10 : ℝ) ^ (2 * Real.logb 10 (2 : ℝ) : ℝ) = (4 : ℝ) := by
                have h22 : (10 : ℝ) ^ (2 * Real.logb 10 (2 : ℝ) : ℝ) = ((10 : ℝ) ^ Real.logb 10 (2 : ℝ)) ^ 2 := by
                  have h23 : (10 : ℝ) ^ (2 * Real.logb 10 (2 : ℝ) : ℝ) = ((10 : ℝ) ^ Real.logb 10 (2 : ℝ)) ^ 2 := by
                    rw [← Real.rpow_natCast, ← Real.rpow_mul]
                    ring
                    all_goals
                      norm_num
                  linarith [h23]
                have h24 : (10 : ℝ) ^ Real.logb 10 (2 : ℝ) = (2 : ℝ) := by
                  rw [Real.rpow_logb]
                  all_goals
                    norm_num
                rw [h24] at h22
                nlinarith
              have h230 : (10 : ℝ) ^ (4 : ℝ) = (10000 : ℝ) := by
                norm_num
              rw [h20, h230]
              all_goals
                nlinarith
            linarith [h17]
          linarith [h17]
        linarith [h7]
    · -- When x = 1/100
      constructor
      · norm_num
      · -- Show that (1/100/2)^logb 10 (1/100) = 40000
        have h1 : Real.logb 10 (1/100 : ℝ) = -2 := by
          calc
            Real.logb 10 (1/100 : ℝ) = Real.logb 10 (1 : ℝ) - Real.logb 10 (100 : ℝ) := by field_simp [Real.logb_div]
            _ = 0 - Real.logb 10 (100 : ℝ) := by norm_num
            _ = - (Real.logb 10 (100 : ℝ) ) := by ring
            _ = - (Real.logb 10 ((10 : ℝ) ^ 2) ) := by norm_num
            _ = - (2 : ℝ) := by 
              have h10 : Real.logb 10 ((10 : ℝ) ^ 2) = (2 : ℝ) := by
                simp [Real.logb_pow]
              rw [h10]
            _ = -2 := by ring
        rw [h1]
        have h100 : ((1/100 : ℝ) / 2 : ℝ) ^ (-2 : ℝ) = (40000 : ℝ) := by
          have h1000 : ((1/100 : ℝ) / 2 : ℝ) ^ (-2 : ℝ) = ((1/200 : ℝ) : ℝ) ^ (-2 : ℝ) := by
            norm_num
          rw [h1000]
          have h1100 : ( (1/200 : ℝ) : ℝ ) ^ (-2 : ℝ) = (40000 : ℝ) := by
            have h1200 : ( (1/200 : ℝ) : ℝ ) ^ (-2 : ℝ) = 1 / ( (1/200 : ℝ) ^ 2 ) := by
              norm_num [Real.rpow_neg]
            rw [h1200]
            norm_num
          linarith [h1100]
        linarith [h100]