import Mathlib

open Real

theorem algebra_255669 (x : ℝ) (hx : 0 < x) :
    4 ^ logb 10 x - 32 + x ^ logb 10 4 = 0 ↔ x = 100 := by
  constructor
  · -- Assume the equation holds, prove x = 100
    intro h
    have h1 : (4 : ℝ) ^ logb 10 x = x ^ logb 10 4 := by
      have h4 : logb 10 ((4 : ℝ) ^ logb 10 x) = logb 10 (x ^ logb 10 4) := by
        have h5 : logb 10 ((4 : ℝ) ^ logb 10 x) = logb 10 x * logb 10 (4 : ℝ) := by
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals norm_num
        have h6 : logb 10 (x ^ logb 10 4) = logb 10 4 * logb 10 x := by 
          rw [logb_rpow_eq_mul_logb_of_pos]
          all_goals nlinarith
        rw [h5, h6]
        all_goals ring
      have h8 : (4 : ℝ) ^ logb 10 x > 0 := by positivity
      have h9 : x ^ logb 10 4 > 0 := by positivity
      have h10 : (4 : ℝ) ^ logb 10 x = x ^ logb 10 4 := by
        apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h8) (Set.mem_Ioi.mpr h9) h4
      linarith
    have eq1 : (4 : ℝ) ^ logb 10 x = 16 := by
      have eq2 : (4 : ℝ) ^ logb 10 x + x ^ logb 10 4 = 32 := by 
        nlinarith
      have eq3 : (4 : ℝ) ^ logb 10 x = x ^ logb 10 4 := h1
      have eq5 : (4 : ℝ) ^ logb 10 x + (4 : ℝ) ^ logb 10 x = 32 := by 
        linarith [eq2, eq3]
      have eq7 : (4 : ℝ) ^ logb 10 x = 16 := by 
        nlinarith
      linarith
    have eq3 : logb 10 x = (2 : ℝ) := by 
      have eq4 : (4 : ℝ) ^ logb 10 x = (16 : ℝ) := eq1
      have eq5 : logb 10 ((4 : ℝ) ^ logb 10 x) = logb 10 (16 : ℝ) := by 
        rw [eq4]
      have eq6 : logb 10 ((4 : ℝ) ^ logb 10 x) = logb 10 x * logb 10 (4 : ℝ) := by 
        rw [logb_rpow_eq_mul_logb_of_pos]
        all_goals 
          norm_num
      have eq7 : logb 10 (16 : ℝ) = 2 * logb 10 (4 : ℝ) := by
        calc
          logb 10 (16 : ℝ) = logb 10 ((4 : ℝ) ^ (2 : ℝ)) := by norm_num
          _ = 2 * logb 10 (4 : ℝ) := by 
            simp [logb_pow]
      rw [eq6] at eq5
      rw [eq7] at eq5
      have h11 : logb 10 (4 : ℝ) ≠ 0 := by 
        have h12 : logb 10 (4 : ℝ) > 0 := by 
          apply logb_pos
          all_goals 
            norm_num
        nlinarith
      have h14 : logb 10 x = 2 := by 
        apply (mul_left_inj' h11).mp
        linarith
      linarith
    have hx100 : x = 100 := by 
      have hx_eq : x = (10 : ℝ) ^ (logb 10 x : ℝ) := by 
        rw [Real.rpow_logb]
        all_goals 
          try { linarith } 
          try { norm_num }
      rw [eq3] at hx_eq 
      norm_num at hx_eq ⊢
      linarith
    exact hx100
  · -- Assume x = 100, prove the equation
    intro h
    rw [h]
    have h3 : logb 10 (100 : ℝ) = 2 := by 
      calc
        logb 10 (100 : ℝ) = logb 10 (10 ^ 2 : ℝ) := by norm_num
        _ = 2 := by 
          simp [logb_pow]
    have h41 : (4 : ℝ) ^ logb 10 (100 : ℝ) = 16 := by
      rw [h3]
      norm_num
    have h42 : (100 : ℝ) ^ logb 10 (4 : ℝ) = 16 := by 
      have h43 : (100 : ℝ) ^ logb 10 (4 : ℝ) = ((10 : ℝ) ^ (2 : ℝ)) ^ logb 10 (4 : ℝ) := by 
        norm_num
      have h44 : ((10 : ℝ) ^ (2 : ℝ)) ^ logb 10 (4 : ℝ) = (10 : ℝ) ^ (2 * logb 10 (4 : ℝ) : ℝ) := by 
        rw [← Real.rpow_mul]
        ring
        all_goals 
          norm_num
      have h45 : (10 : ℝ) ^ (2 * logb 10 (4 : ℝ) : ℝ) = 16 := by 
        have h46 : (10 : ℝ) ^ (2 * logb 10 (4 : ℝ) : ℝ) = ((10 : ℝ) ^ (logb 10 (4 : ℝ) : ℝ)) ^ 2 := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring
          all_goals 
            norm_num
        have h47 : (10 : ℝ) ^ (logb 10 (4 : ℝ) : ℝ) = (4 : ℝ) := by 
          rw [Real.rpow_logb]
          all_goals 
            norm_num
        rw [h47] at h46
        norm_num at h46 ⊢
        linarith
      rw [h43, h44, h45]
    rw [h41, h42]
    all_goals norm_num