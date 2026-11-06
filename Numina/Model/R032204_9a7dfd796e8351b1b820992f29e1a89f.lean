import Mathlib

theorem algebra_106365 {x y : ℝ} (h1 : (4^x : ℝ) / 2^(x + y) = 8) (h2 : (9^(x + y) : ℝ) / 3^(5 * y) = 243) :
    x * y = 4 := by

  have eq1 : (4^x : ℝ) / 2^(x + y) = 2^(x - y) := by
    have h3 : (4^x : ℝ) = (2 : ℝ)^(2 * x) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h4 : (2^(x + y) : ℝ) = (2 : ℝ)^(x + y) := by
      norm_num
    rw [h3, h4]
    have h5 : ((2 : ℝ)^(2 * x) : ℝ) / ((2 : ℝ)^(x + y) : ℝ) = (2 : ℝ) ^ (2 * x - (x + y)) := by
      rw [← Real.rpow_sub]
      ring_nf
      all_goals norm_num
    have h6 : (2 * x - (x + y)) = x - y := by
      linarith
    rw [h5, h6]

  have eq1' : (x - y) = 3 := by
    rw [eq1] at h1
    have h4 : (2 : ℝ) ^ (x - y : ℝ) = (8 : ℝ) := by
      simpa using h1
    have h5 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) := by norm_num
    rw [h5] at h4
    have h6 : x - y = (3 : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h4
      have h7 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (x - y : ℝ)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 : ℝ)) := by
        simpa using h4
      have h8 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (x - y : ℝ)) = x - y := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h9 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (3 : ℝ)) = (3 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h8, h9] at h7
      linarith
    linarith

  have eq2 : (9^(x + y) : ℝ) / 3^(5 * y) = (3 : ℝ)^(2 * x - 3 * y) := by
    have h7 : (9^(x + y) : ℝ) = (3 : ℝ)^(2 * (x + y)) := by
      rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h8 : (3^(5 * y) : ℝ) = (3 : ℝ)^(5 * y) := by
      norm_num
    rw [h7, h8]
    have h5 : ((3 : ℝ) ^ (2 * (x + y) : ℝ) : ℝ) / ((3 : ℝ) ^ (5 * y : ℝ) : ℝ) = (3 : ℝ) ^ (2 * (x + y) - 5 * y : ℝ) := by
      rw [← Real.rpow_sub]
      ring_nf
      all_goals norm_num
    have h6 : (2 * (x + y) - 5 * y) = (2 * x - 3 * y) := by
      ring_nf
    rw [h5, h6]

  have eq2' : (2 * x - 3 * y) = 5 := by
    rw [eq2] at h2
    have h4 : (3 : ℝ) ^ (2 * x - 3 * y : ℝ) = (243 : ℝ) := by
      simpa using h2
    have h5 : (243 : ℝ) = (3 : ℝ) ^ (5 : ℝ) := by norm_num
    rw [h5] at h4
    have h6 : 2 * x - 3 * y = (5 : ℝ) := by
      apply_fun (Real.logb (3 : ℝ)) at h4
      have h7 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (2 * x - 3 * y : ℝ)) = Real.logb (3 : ℝ) ((3 : ℝ) ^ (5 : ℝ)) := by
        simpa using h4
      have h8 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (2 * x - 3 * y : ℝ)) = 2 * x - 3 * y := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h9 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (5 : ℝ)) = (5 : ℝ) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h8, h9] at h7
      linarith
    linarith

  have eq5 : y = 1 := by 
    nlinarith [eq1', eq2']

  have eq6 : x = 4 := by
    linarith [eq5, eq1']

  have eq7 : x * y = 4 := by
    rw [eq6, eq5]
    norm_num

  linarith [eq7]