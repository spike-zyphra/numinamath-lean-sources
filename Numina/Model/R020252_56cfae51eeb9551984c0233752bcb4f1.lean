import Mathlib

theorem algebra_13105 (x : ℝ) : (2 : ℝ) ^ ((16 : ℝ) ^ x) = (16 : ℝ) ^ ((2 : ℝ) ^ x) ↔
    x = 2 / 3 := by
  constructor
  · -- Start by assuming the equation holds, proving x = 2/3.
    intro h_eq
    have h1 : (16 : ℝ) ^ ((2 : ℝ) ^ x) = (2 : ℝ) ^ (4 * ((2 : ℝ) ^ x)) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals
        norm_num
    rw [h1] at h_eq
    have h2 : (16 : ℝ) ^ x = 4 * ((2 : ℝ) ^ x) := by
      apply_fun (Real.logb (2 : ℝ)) at h_eq
      have h3 : Real.logb (2 : ℝ) ((2 : ℝ) ^ ((16 : ℝ) ^ x)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (4 * ((2 : ℝ) ^ x)) ) := by 
        linarith
      have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ ((16 : ℝ) ^ x)) = (16 : ℝ) ^ x := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (4 * ((2 : ℝ) ^ x)) ) = 4 * ((2 : ℝ) ^ x) := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h4, h5] at h3
      linarith
    have h3 : (16 : ℝ) ^ x = (2 : ℝ) ^ (4 * x : ℝ) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals 
        norm_num
    rw [h3] at h2
    have h4 : (2 : ℝ) ^ (4 * x : ℝ) = (2 : ℝ) ^ (2 + x : ℝ) := by
      have h5 : 4 * ((2 : ℝ) ^ (x : ℝ)) = (2 : ℝ) ^ (2 + x : ℝ) := by
        have h6 : (2 : ℝ) ^ (2 + x : ℝ) = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ (x : ℝ) := by
          rw [← Real.rpow_add]
          ring_nf
          all_goals 
            norm_num
        have h7 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by
          norm_num
        rw [h7] at h6
        linarith
      linarith [h2, h5]
    have h7 : 4 * x = 2 + x := by
      apply_fun (Real.logb (2 : ℝ)) at h4
      have h8 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (4 * x : ℝ)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 + x : ℝ)) := by 
        linarith
      have h9 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (4 * x : ℝ)) = 4 * x := by
        rw [Real.logb_rpow]
        all_goals 
          norm_num
      have h10 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 + x : ℝ)) = 2 + x := by
        rw [Real.logb_rpow]
        all_goals 
          norm_num
      rw [h9, h10] at h8
      linarith
    linarith
  · -- Assume x = 2/3, prove the equation.
    intro h_eq
    rw [show x = 2 / 3 by linarith [h_eq]]
    have h1 : (16 : ℝ) ^ ((2 : ℝ) ^ (2 / 3 : ℝ)) = (2 : ℝ) ^ (4 * ((2 : ℝ) ^ (2 / 3 : ℝ)) : ℝ) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals 
        norm_num
    have h4 : (16 : ℝ) ^ (2 / 3 : ℝ) = 4 * ((2 : ℝ) ^ (2 / 3 : ℝ)) := by
      have h3 : (16 : ℝ) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (8 / 3 : ℝ) := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals 
          norm_num
      rw [h3]
      have h6 : (2 : ℝ) ^ (8 / 3 : ℝ) = 4 * ((2 : ℝ) ^ (2 / 3 : ℝ)) := by
        have h7 : (2 : ℝ) ^ (8 / 3 : ℝ) = (2 : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) := by
          rw [← Real.rpow_add]
          ring_nf
          all_goals 
            norm_num
        have h8 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by
          norm_num
        rw [h8] at h7
        linarith
      linarith
    have h5 : (2 : ℝ) ^ ((16 : ℝ) ^ (2 / 3 : ℝ)) = (2 : ℝ) ^ (4 * ((2 : ℝ) ^ (2 / 3 : ℝ)) : ℝ) := by
      rw [h4]
    linarith [h1, h5]