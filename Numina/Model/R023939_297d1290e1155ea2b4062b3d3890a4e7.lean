import Mathlib

open Real

theorem algebra_97228 {x : ℝ} (hx : 0 ≤ x) :
    sqrt (x * sqrt (x * sqrt x)) = (x ^ 7) ^ ((1 : ℝ) / 8) := by 
  have h1 : sqrt x = (x) ^ ((1 : ℝ) / 2) := by 
    rw [Real.sqrt_eq_rpow]
  have h2 : sqrt (x * sqrt x) = (x * sqrt x) ^ ((1 : ℝ) / 2) := by 
    rw [Real.sqrt_eq_rpow]
  by_cases h : x = 0 
  · -- If x = 0, both sides are 0
    rw [h]
    norm_num
    all_goals norm_num
  · -- If x ≠ 0, then x > 0 
    have hx2 : x > 0 := by 
      by_contra h'
      push_neg at h'
      have h0 : x = 0 := by linarith 
      tauto 
    have h3 : sqrt (x * sqrt x) = (x) ^ (3 / 4 : ℝ) := by
      have h4 : sqrt x = (x) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      have h5 : x * sqrt x = (x) ^ (3 / 2 : ℝ) := by 
        rw [h4]
        have h7 : (x : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) ) = (x) ^ (3 / 2 : ℝ) := by
          have h8 : (x : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) ) = (x) ^ (1 : ℝ) * ((x) ^ (1 / 2 : ℝ) ) := by 
            simp 
          rw [h8]
          have h9 : (x : ℝ) ^ (1 : ℝ) * ((x : ℝ) ^ (1 / 2 : ℝ) ) = (x) ^ (1 + (1 / 2 : ℝ) ) := by 
            rw [← Real.rpow_add]
            all_goals norm_num at *
            all_goals linarith [show 0 < x by linarith]
          rw [h9]
          all_goals norm_num at *
          all_goals linarith 
        linarith [h7] 
      have h8 : sqrt (x * sqrt x) = ((x) ^ (3 / 2 : ℝ) ) ^ (1 / 2 : ℝ) := by 
        rw [h2, h5]
        all_goals norm_num at *
      have h9 : ((x : ℝ) ^ (3 / 2 : ℝ) ) ^ (1 / 2 : ℝ) = (x) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_mul]
        ring_nf 
        all_goals norm_num at *
        all_goals linarith [show 0 < x by linarith]
      rw [h8, h9]
    have h4 : sqrt (x * sqrt (x * sqrt x)) = (x) ^ (7 / 8 : ℝ) := by
      have h5 : x * sqrt (x * sqrt x) = (x) ^ (7 / 4 : ℝ) := by 
        have h8 : sqrt (x * sqrt x) = (x) ^ (3 / 4 : ℝ) := h3 
        have h9 : x * sqrt (x * sqrt x) = x * ((x) ^ (3 / 4 : ℝ) ) := by 
          rw [h8]
          all_goals norm_num 
        have h10 : x * ((x) ^ (3 / 4 : ℝ) ) = (x : ℝ) ^ (7 / 4 : ℝ) := by 
          have h11 : x * ((x : ℝ) ^ (3 / 4 : ℝ) ) = (x) ^ (1 : ℝ) * ((x) ^ (3 / 4 : ℝ) ) := by 
            simp 
          rw [h11]
          have h12 : (x : ℝ) ^ (1 : ℝ) * ((x : ℝ) ^ (3 / 4 : ℝ) ) = (x) ^ (1 + (3 / 4 : ℝ) ) := by 
            rw [← Real.rpow_add]
            all_goals norm_num at *
            all_goals linarith [show 0 < x by linarith]
          rw [h12]
          all_goals norm_num at *
          all_goals linarith 
        rw [h9, h10]
        all_goals norm_num at *
      rw [Real.sqrt_eq_rpow]
      rw [h5]
      have h6 : ((x) ^ (7 / 4 : ℝ) ) ^ (1 / 2 : ℝ) = (x) ^ (7 / 8 : ℝ) := by 
        rw [← Real.rpow_mul]
        ring_nf 
        all_goals norm_num at *
        all_goals linarith [show 0 < x by linarith]
      rw [h6]
    have h5 : (x ^ 7) ^ ((1 : ℝ) / 8) = (x) ^ (7 / 8 : ℝ) := by 
      have h6 : (x ^ 7: ℝ) ^ ((1 : ℝ) / 8) = (x) ^ (7 * (1 / 8 : ℝ) ) := by 
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        ring_nf 
        all_goals norm_num at *
        all_goals linarith [show 0 < x by linarith]
      rw [h6]
      ring_nf 
      all_goals norm_num at *
      all_goals linarith 
    rw [h4, h5]
    all_goals norm_num at *
    all_goals linarith