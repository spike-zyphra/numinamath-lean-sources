import Mathlib

open Real

theorem algebra_167038 {x : ℝ} (hx : x > 0) :
    logb 5 x + logb 25 x = logb (1 / 5) (sqrt 3) ↔
    x = 1 / (3 ^ ((1 : ℝ) / 3)) := by
  constructor
  · -- Assume logb 5 x + logb 25 x = logb (1 / 5) (sqrt 3) prove x = 1 / (3 ^ ((1 : ℝ) / 3))
    intro h_eq 
    have h1 : logb 25 x = (logb 5 x) / 2 := by 
      have h2 : logb 25 x = (logb 5 x) / (logb 5 (25 : ℝ)) := by 
        field_simp [logb]
      have h3 : logb 5 (25 : ℝ) = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h3] at h2 
      linarith 
    have h2' : logb (1 / 5) (sqrt 3) = - (logb 5 (sqrt 3)) := by 
      have h3 : logb (1 / 5) (sqrt 3) = (logb 5 (sqrt 3)) / (logb 5 (1 / 5 : ℝ)) := by 
        field_simp [logb]
      have h4 : logb 5 (1 / 5 : ℝ) = -1 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h4] at h3 
      field_simp at h3 ⊢ 
      <;> linarith 
    have h3' : logb 5 (sqrt 3) = (1 / 2 : ℝ) * (logb 5 (3 : ℝ)) := by 
      calc 
        logb 5 (sqrt 3) = logb 5 ((3 : ℝ) ^ (1 / 2 : ℝ)) := by 
          rw [Real.sqrt_eq_rpow] 
        _ = (1 / 2 : ℝ) * (logb 5 (3 : ℝ)) := by 
          rw [logb_rpow_eq_mul_logb_of_pos] 
          all_goals norm_num 
    rw [h1, h2', h3'] at h_eq 
    have h4 : 3 * (logb 5 x) = - (logb 5 (3 : ℝ)) := by 
      linarith 
    have h5_eq : logb 5 (x ^ 3) = logb 5 ((3 : ℝ) ^ (-1 : ℝ)) := by 
      have h6 : logb 5 (x ^ 3) = 3 * (logb 5 x) := by 
        simp [logb_pow] 
      have h7 : logb 5 ((3 : ℝ) ^ (-1 : ℝ)) = - (logb 5 (3 : ℝ)) := by 
        have h8 : logb 5 ((3 : ℝ) ^ (-1 : ℝ)) = (-1 : ℝ) * (logb 5 (3 : ℝ)) := by 
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals norm_num 
        linarith 
      rw [h6, h7] 
      linarith [h4] 
    have h5 : x ^ 3 = (3 : ℝ) ^ (-1 : ℝ) := by
      have h6_pos1 : x ^ 3 > 0 := by 
        positivity
      have h6_pos2 : (3 : ℝ) ^ (-1 : ℝ) > 0 := by 
        positivity 
      have h7 : logb 5 (x ^ 3) = logb 5 ((3 : ℝ) ^ (-1 : ℝ) ) := h5_eq 
      have h8 : x ^ 3 = (3 : ℝ) ^ (-1 : ℝ) := by 
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h6_pos1) (Set.mem_Ioi.mpr h6_pos2) h7 
      linarith 
    have hx_eq : x = ((3 : ℝ) ^ (-1 : ℝ)) ^ ((1 : ℝ) / 3) := by 
      have h9 : x ^ 3 = (3 : ℝ) ^ (-1 : ℝ) := h5 
      have h9_pos : x ^ 3 > 0 := by 
        positivity 
      have h9_eq : x = (x ^ 3) ^ ((1 : ℝ) / 3) := by 
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        field_simp 
        all_goals nlinarith 
      rw [h5] at h9_eq 
      linarith 
    have hx2 : ((3 : ℝ) ^ (-1 : ℝ)) ^ ((1 : ℝ) / 3) = (3 : ℝ) ^ (- (1 / 3 : ℝ)) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num 
    rw [hx2] at hx_eq 
    have h9 : (3 : ℝ) ^ (- (1 / 3 : ℝ)) = 1 / ((3 : ℝ) ^ ((1 : ℝ) / 3)) := by 
      rw [show - (1 / 3 : ℝ) = - ((1 / 3 : ℝ) ) by ring]
      rw [Real.rpow_neg]
      <;> norm_num 
    rw [h9] at hx_eq 
    linarith 
  · -- Assume x = 1 / (3 ^ ((1 : ℝ) / 3)) prove logb 5 x + logb 25 x = logb (1 / 5) (sqrt 3)
    intro h_eq 
    rw [h_eq] 
    have h1 : logb 25 (1 / (3 ^ ((1 : ℝ) / 3)) ) = (logb 5 (1 / (3 ^ ((1 : ℝ) / 3)) )) / 2 := by 
      have h2 : logb 25 (1 / (3 ^ ((1 : ℝ) / 3)) ) = (logb 5 (1 / (3 ^ ((1 : ℝ) / 3)) )) / (logb 5 (25 : ℝ)) := by 
        field_simp [logb]
      have h3 : logb 5 (25 : ℝ) = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h3] at h2 
      linarith 
    have h3_eq : logb 5 (1 / (3 ^ ((1 : ℝ) / 3)) ) = - (1 / 3 : ℝ) * (logb 5 (3 : ℝ)) := by
      calc 
        logb 5 (1 / (3 ^ ((1 : ℝ) / 3)) ) = logb 5 ((3 : ℝ) ^ (- (1 / 3 : ℝ)) ) := by 
          have h_eq2 : (1 / (3 ^ ((1 : ℝ) / 3)) : ℝ) = (3 : ℝ) ^ (- (1 / 3 : ℝ)) := by 
            have eq1a : (3 : ℝ) ^ (- (1 / 3 : ℝ)) = ((3 : ℝ) ^ ((1 / 3 : ℝ)) )⁻¹ := by 
              rw [show - (1 / 3 : ℝ) = - ( (1 / 3 : ℝ) ) by ring]
              rw [Real.rpow_neg]
              all_goals norm_num 
            have eq1b : ((3 : ℝ) ^ ((1 / 3 : ℝ)) )⁻¹ = 1 / (3 ^ ((1 : ℝ) / 3)) := by 
              field_simp [Real.rpow_pos_of_pos] 
            rw [eq1a, eq1b] 
          rw [h_eq2] 
        _ = - (1 / 3 : ℝ) * (logb 5 (3 : ℝ)) := by 
          have eq1 : logb 5 ((3 : ℝ) ^ (- (1 / 3 : ℝ)) ) = (- (1 / 3 : ℝ)) * (logb 5 (3 : ℝ)) := by 
            rw [logb_rpow_eq_mul_logb_of_pos]
            all_goals norm_num 
          linarith [eq1] 
    have h2' : logb (1 / 5) (sqrt 3) = - (logb 5 (sqrt 3)) := by
      have h3 : logb (1 / 5) (sqrt 3) = (logb 5 (sqrt 3)) / (logb 5 (1 / 5 : ℝ)) := by 
        field_simp [logb]
      have h4 : logb 5 (1 / 5 : ℝ) = -1 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      rw [h4] at h3 
      field_simp at h3 ⊢ 
      <;> linarith 
    have h3' : logb 5 (sqrt 3) = (1 / 2 : ℝ) * (logb 5 (3 : ℝ)) := by 
      calc 
        logb 5 (sqrt 3) = logb 5 ((3 : ℝ) ^ (1 / 2 : ℝ)) := by 
          rw [Real.sqrt_eq_rpow] 
        _ = (1 / 2 : ℝ) * (logb 5 (3 : ℝ)) := by 
          rw [logb_rpow_eq_mul_logb_of_pos] 
          all_goals norm_num 
    rw [h1, h3_eq, h2', h3']
    <;> nlinarith