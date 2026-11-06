import Mathlib

open Real

theorem algebra_160006 {x : ℝ} (hx : x > 0) :
    1984 ^ (logb 10 x) = 2 * 1984 ^ 2 - x ^ (logb 10 1984) ↔ x = 100 := by
  constructor
  · -- Assume the equation holds, prove x = 100
    intro h_eq
    have h1 : x ^ (logb 10 1984) = (1984 : ℝ) ^ (logb 10 x) := by
      have h4 : logb 10 (x ^ (logb 10 1984)) = logb 10 (1984 ^ (logb 10 x)) := by
        have h5 : logb 10 (x ^ (logb 10 1984)) = logb 10 1984 * logb 10 x := by
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals linarith
        have h6 : logb 10 (1984 ^ (logb 10 x)) = logb 10 x * logb 10 1984 := by
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals norm_num
        rw [h5, h6]
        <;> ring
      have h7 : x ^ (logb 10 1984) > 0 := by positivity
      have h8 : (1984 : ℝ) ^ (logb 10 x) > 0 := by positivity
      have h9 : x ^ (logb 10 1984) = (1984 : ℝ) ^ (logb 10 x) := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h7) (Set.mem_Ioi.mpr h8) h4
      linarith
    rw [h1] at h_eq
    have h10 : (1984 : ℝ) ^ (logb 10 x) = (1984 : ℝ) ^ (2 : ℝ) := by
      nlinarith [h_eq]
    have h13 : logb 10 x = (2 : ℝ) := by
      apply_fun (Real.logb (1984 : ℝ)) at h10
      have h14 : Real.logb (1984 : ℝ) ((1984 : ℝ) ^ (logb 10 x)) = logb 10 x := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h15 : Real.logb (1984 : ℝ) ((1984 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h14, h15] at h10
      linarith
    have h14 : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by
      rw [Real.rpow_logb]
      all_goals
        try linarith
    rw [h13] at h14
    norm_num at h14 ⊢
    linarith
  · -- Now prove the reverse direction: x = 100 implies the equation
    intro h_eq
    rw [h_eq]
    have h100 : logb 10 (100 : ℝ) = (2 : ℝ) := by 
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    have h1 : (100 : ℝ) ^ (logb 10 1984) = (1984 : ℝ) ^ (2 : ℝ) := by
      have h4 : logb 10 ((100 : ℝ) ^ (logb 10 1984)) = logb 10 ((1984 : ℝ) ^ (2 : ℝ)) := by 
        have h5 : logb 10 ((100 : ℝ) ^ (logb 10 1984)) = logb 10 1984 * logb 10 (100 : ℝ) := by 
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals norm_num
        have h6 : logb 10 ((1984 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) * logb 10 (1984 : ℝ) := by 
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals norm_num
        have h100' : logb 10 (100 : ℝ) = (2 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        rw [h5, h6, h100']
        <;> ring
      have h7 : (100 : ℝ) ^ (logb 10 1984) > 0 := by positivity
      have h8 : (1984 : ℝ) ^ (2 : ℝ) > 0 := by positivity
      have h9 : (100 : ℝ) ^ (logb 10 1984) = (1984 : ℝ) ^ (2 : ℝ) := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h7) (Set.mem_Ioi.mpr h8) h4
      linarith
    rw [h100] at *
    rw [h1]
    all_goals norm_num