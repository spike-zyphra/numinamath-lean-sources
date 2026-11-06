import Mathlib
open Real

theorem algebra_267470 :
    {(x, y) : ℝ × ℝ | x > 0 ∧ y > 0 ∧ x * y = 500 ∧ x ^ (Real.logb 10 y) = 25} =
    {(100, 5), (5, 100)} := by
  ext ⟨x, y⟩
  simp [-one_div]
  constructor
  · -- Assume (x,y) satisfies all conditions, prove (x,y) ∈ {(100,5),(5,100)}
    rintro ⟨hx, hy, hxy, h_eq⟩
    have eq1 : Real.logb 10 (x ^ (Real.logb 10 y)) = Real.logb 10 (25 : ℝ) := by 
      rw [h_eq]
    have eq2 : Real.logb 10 (x ^ (Real.logb 10 y)) = Real.logb 10 y * Real.logb 10 x := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos]
      all_goals
        try linarith
    rw [eq2] at eq1
    have eq3 : Real.logb 10 (25 : ℝ) = 2 * Real.logb 10 (5 : ℝ) := by
      calc 
        Real.logb 10 (25 : ℝ) = Real.logb 10 (5 ^ 2 : ℝ) := by norm_num
        _ = 2 * Real.logb 10 (5 : ℝ) := by simp [Real.logb_pow]
    rw [eq3] at eq1
    have eq4 : Real.logb 10 x + Real.logb 10 y = Real.logb 10 (5 : ℝ) + 2 := by
      have h1 : Real.logb 10 x + Real.logb 10 y = Real.logb 10 (x * y) := by
        rw [Real.logb_mul (by positivity) (by positivity)]
      have h2 : Real.logb 10 (x * y) = Real.logb 10 (500 : ℝ) := by
        rw [hxy]
      have h3 : Real.logb 10 (500 : ℝ) = Real.logb 10 (5 : ℝ) + 2 := by
        calc
          Real.logb 10 (500 : ℝ) = Real.logb 10 (5 * 100 : ℝ) := by norm_num
          _ = Real.logb 10 (5 : ℝ) + Real.logb 10 (100 : ℝ) := by rw [Real.logb_mul (by positivity) (by positivity)]
          _ = Real.logb 10 (5 : ℝ) + Real.logb 10 ((10 : ℝ) ^ 2 : ℝ) := by norm_num
          _ = Real.logb 10 (5 : ℝ) + (2 : ℝ) := by 
            have h4 : Real.logb 10 ((10 : ℝ) ^ 2 : ℝ) = (2 : ℝ) := by 
              simp [Real.logb_pow]
            linarith [h4]
          _ = Real.logb 10 (5 : ℝ) + 2 := by ring
      linarith [h1, h2, h3]
    have h5 : (Real.logb 10 x - Real.logb 10 (5 : ℝ)) * (Real.logb 10 x - (2 : ℝ)) = 0 := by
      have h6 : Real.logb 10 x + Real.logb 10 y = Real.logb 10 (5 : ℝ) + 2 := eq4
      have h7 : Real.logb 10 y * Real.logb 10 x = 2 * Real.logb 10 (5 : ℝ) := by
        linarith [eq1]
      have h8 : Real.logb 10 y = Real.logb 10 (5 : ℝ) + 2 - Real.logb 10 x := by
        linarith [h6]
      rw [h8] at h7
      nlinarith
    cases' (mul_eq_zero.1 h5) with h11 h12
    · 
      have hx1 : Real.logb 10 x = Real.logb 10 (5 : ℝ) := by
        linarith 
      have hx2 : x = (5 : ℝ) := by
        have : x = (5 : ℝ) := by
          apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (show (5 : ℝ) > 0 by norm_num)) hx1
        linarith
      have hy1 : y = (100 : ℝ) := by
        rw [show x = (5 : ℝ) by linarith [hx2]] at hxy
        nlinarith 
      simp [hx2, hy1]
    · 
      have hx1 : Real.logb 10 x = (2 : ℝ) := by 
        linarith 
      have hx2 : x = (100 : ℝ) := by
        have h121 : x = (100 : ℝ) := by
          have h122 : x = (10 ^ (2 : ℝ) : ℝ) := by
            rw [Real.logb_eq_iff_rpow_eq] at hx1
            · nlinarith 
            all_goals
              try linarith
          norm_num at h122 ⊢
          linarith 
        linarith 
      have hy1 : y = (5 : ℝ) := by
        rw [show x = (100 : ℝ) by linarith [hx2]] at hxy
        nlinarith 
      simp [hx2, hy1]
  · -- Assume (x,y) ∈ {(100,5),(5,100)}, prove it satisfies all conditions
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Prove the fourth condition
        have h1005 : (100 : ℝ) ^ Real.logb 10 (5 : ℝ) = 25 := by
          have h2 : (100 : ℝ) ^ Real.logb 10 (5 : ℝ) = (10 : ℝ) ^ (2 * Real.logb 10 (5 : ℝ) : ℝ) := by
            have h2 : (100 : ℝ) = (10 : ℝ) ^ (2 : ℝ) := by norm_num
            rw [h2]
            have h3 : ((10 : ℝ) ^ (2 : ℝ)) ^ Real.logb 10 (5 : ℝ) = (10 : ℝ) ^ (2 * Real.logb 10 (5 : ℝ) : ℝ) := by 
              rw [← Real.rpow_mul]
              ring_nf
              all_goals
                norm_num
            linarith [h3]
          have h4 : (10 : ℝ) ^ (2 * Real.logb 10 (5 : ℝ) : ℝ) = (25 : ℝ) := by
            have h6 : 2 * Real.logb 10 (5 : ℝ) = Real.logb 10 (25 : ℝ) := by
              calc 
                2 * Real.logb 10 (5 : ℝ) = Real.logb 10 (5 ^ 2 : ℝ) := by simp [Real.logb_pow]
                _ = Real.logb 10 (25 : ℝ) := by norm_num
            rw [h6]
            have h4 : (10 : ℝ) ^ (Real.logb 10 (25 : ℝ) : ℝ) = (25 : ℝ) := by
              rw [Real.rpow_logb]
              all_goals
                norm_num
            linarith [h4]
          linarith [h2, h4]
        norm_num at h1005 ⊢
        all_goals
          try linarith [h1005]
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · -- Prove the fourth condition
        have h1005 : (5 : ℝ) ^ Real.logb 10 (100 : ℝ) = 25 := by
          have h2 : Real.logb 10 (100 : ℝ) = (2 : ℝ) := by
            calc
              Real.logb 10 (100 : ℝ) = Real.logb 10 ((10 : ℝ) ^ 2) := by norm_num
              _ = 2 := by 
                simp [Real.logb_pow]
          rw [h2]
          norm_num
        norm_num at h1005 ⊢
        all_goals
          try linarith [h1005]