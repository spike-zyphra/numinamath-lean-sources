import Mathlib

theorem algebra_257349 :
  {x : ℝ | 0 < x ∧ (x / 3) ^ (3 + Real.logb 10 x) = 30000} = {30, 1 / 10000} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x in the domain, need to prove it's in the set
    intro h
    rcases h with ⟨hx, heq⟩
    have h1 : 0 < x := hx
    have h2 : (x / 3) ^ (3 + Real.logb 10 x) = 30000 := heq

    have h3 : Real.logb 10 ((x / 3) ^ (3 + Real.logb 10 x)) = Real.logb 10 (30000) := by 
      rw [h2]

    have h4 : Real.logb 10 ((x / 3) ^ (3 + Real.logb 10 x)) = (3 + Real.logb 10 x) * Real.logb 10 (x / 3) := by 
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      have h5 : x / 3 > 0 := by 
        have h6 : x > 0 := hx 
        positivity 
      all_goals linarith 
    rw [h4] at h3

    have h5 : Real.logb 10 (x / 3) = Real.logb 10 x - Real.logb 10 (3 : ℝ) := by 
      rw [Real.logb_div (by linarith) (by norm_num)]

    rw [h5] at h3

    have h5' : Real.logb 10 (30000 : ℝ) = Real.logb 10 3 + 4 := by 
      calc 
        Real.logb 10 (30000 : ℝ) = Real.logb 10 (3 * ((10 : ℝ) ^ 4)) := by 
          norm_num 
        _ = Real.logb 10 3 + Real.logb 10 ((10 : ℝ) ^ 4) := by 
          rw [Real.logb_mul (by norm_num) (by norm_num)]
        _ = Real.logb 10 3 + 4 := by 
          simp [Real.logb_pow]

    rw [h5'] at h3
    have h7 : (3 + Real.logb 10 x) * (Real.logb 10 x - Real.logb 10 (3 : ℝ)) = Real.logb 10 3 + 4 := by 
      linarith

    have h9 : (Real.logb 10 x - (Real.logb 10 3 + 1)) * (Real.logb 10 x + 4) = 0 := by
      nlinarith [sq_nonneg (Real.logb 10 x - (Real.logb 10 3 + 1)), sq_nonneg (Real.logb 10 x + 4)]

    cases' (mul_eq_zero.mp h9) with h9 h10
    · -- Real.logb 10 x - (Real.logb 10 3 + 1) = 0
      have h11 : Real.logb 10 x = Real.logb 10 3 + 1 := by 
        linarith 
      have h12 : x = (30 : ℝ) := by 
        have h13 : Real.logb 10 x = Real.logb 10 (30 : ℝ) := by 
          have h14 : Real.logb 10 (30 : ℝ) = Real.logb 10 3 + 1 := by 
            calc 
              Real.logb 10 (30 : ℝ) = Real.logb 10 (3 * 10) := by norm_num 
              _ = Real.logb 10 3 + Real.logb 10 (10 : ℝ) := by 
                rw [Real.logb_mul (by norm_num) (by norm_num)]
              _ = Real.logb 10 3 + 1 := by 
                have h15 : Real.logb 10 (10 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
                linarith 
          linarith [h11, h14]
        have h16 : x = (30 : ℝ) := by 
          apply Real.logb_injOn_pos (by norm_num : (10 : ℝ) > 1) (Set.mem_Ioi.mpr (show 0 < x by linarith)) (Set.mem_Ioi.mpr (show 0 < (30 : ℝ) by norm_num)) h13 
        linarith 

      left 
      norm_num at h12 ⊢ 
      <;> linarith 
    · -- Real.logb 10 x + 4 = 0
      have h11 : Real.logb 10 x = -4 := by linarith 
      have h12 : x = (1 / 10000 : ℝ) := by 
        have h13 : x = (10 : ℝ) ^ (Real.logb 10 x : ℝ) := by 
          field_simp [Real.rpow_logb, hx]
        rw [h13, h11]
        norm_num 
      right 
      norm_num at h12 ⊢ 
      <;> linarith 
  · -- Show that if x is 30 or 1/10000, then it satisfies the equation
    rintro (h | h)
    · -- x = 30 
      rw [h]
      constructor 
      · norm_num 
      · -- Verify the equation 
        have h1 : (30 : ℝ) / 3 = (10 : ℝ) := by norm_num 
        have h2 : (10 : ℝ) ^ (3 + Real.logb 10 (30 : ℝ) : ℝ) = (30000 : ℝ) := by 
          have h3 : Real.logb 10 (30 : ℝ) = Real.logb 10 3 + 1 := by 
            calc 
              Real.logb 10 (30 : ℝ) = Real.logb 10 (3 * 10) := by norm_num 
              _ = Real.logb 10 3 + Real.logb 10 (10 : ℝ) := by 
                rw [Real.logb_mul (by norm_num) (by norm_num)]
              _ = Real.logb 10 3 + 1 := by 
                have h15 : Real.logb 10 (10 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
                linarith 
          have h4 : 3 + Real.logb 10 (30 : ℝ) = 4 + Real.logb 10 3 := by 
            linarith [h3]
          rw [h4]
          have h5 : (10 : ℝ) ^ (4 + Real.logb 10 3 : ℝ) = (10 : ℝ) ^ (4 : ℝ) * (10 : ℝ) ^ (Real.logb 10 3 : ℝ) := by 
            rw [← Real.rpow_add]
            ring_nf 
            all_goals linarith 
          rw [h5] 
          have h6 : (10 : ℝ) ^ (4 : ℝ) = (10000 : ℝ) := by norm_num 
          have h7 : (10 : ℝ) ^ (Real.logb 10 3 : ℝ) = (3 : ℝ) := by 
            rw [Real.rpow_logb]
            all_goals norm_num 
          rw [h6, h7]
          all_goals norm_num 
        rw [h1] 
        linarith [h2] 
    · -- x = 1 / 10000 
      rw [h]
      constructor 
      · norm_num 
      · -- Verify the equation 
        have h1 : (1 / 10000 : ℝ) / 3 = (1 / 30000 : ℝ) := by norm_num 
        have h2 : (1 / 30000 : ℝ) ^ (3 + Real.logb 10 (1 / 10000 : ℝ) : ℝ) = (30000 : ℝ) := by 
          have h3 : Real.logb 10 (1 / 10000 : ℝ) = -4 := by 
            calc 
              Real.logb 10 (1 / 10000 : ℝ) = Real.logb 10 ((10 : ℝ) ^ (-4 : ℝ)) := by norm_num 
              _ = -4 * Real.logb 10 (10 : ℝ) := by 
                rw [Real.logb_rpow_eq_mul_logb_of_pos]
                all_goals norm_num 
              _ = -4 * (1 : ℝ) := by 
                have h15 : Real.logb 10 (10 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
                rw [h15]
              _ = -4 := by ring 
          have h4 : 3 + Real.logb 10 (1 / 10000 : ℝ) = (-1 : ℝ) := by 
            linarith [h3]
          rw [h4]
          have h5 : (1 / 30000 : ℝ) ^ (-1 : ℝ) = (30000 : ℝ) := by 
            norm_num 
          linarith [h5] 
        rw [h1] 
        linarith [h2]