import Mathlib

 theorem algebra_21747 {F : ℝ → ℝ → ℝ → ℝ → ℝ} (hF : F = fun a b c d => a ^ b + 
    c ^ d) (b : ℝ) (hF1 : F 4 b 2 3 = 12) : b = 1 := by
  have eq1 : (4 : ℝ) ^ b + (2 : ℝ) ^ (3 : ℝ) = 12 := by
    rw [hF] at hF1
    simpa using hF1
  have eq2 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
    norm_num
  rw [eq2] at eq1
  -- Now we need to solve 4^b + 8 = 12, so 4^b = 4
  have eq3 : (4 : ℝ) ^ b = 4 := by 
    linarith
  -- Now we need to prove b = 1 from 4^b = 4
  have eq4 : b = 1 := by 
    apply_fun (Real.logb (4 : ℝ)) at eq3
    -- Real.logb 4 (4 ^ b) = Real.logb 4 4
    -- This simplifies to b = 1
    have h1 : Real.logb (4 : ℝ) ((4 : ℝ) ^ b) = b := by 
      rw [Real.logb_rpow]
      all_goals linarith
    -- Real.logb 4 4 = 1
    have h2 : Real.logb (4 : ℝ) (4 : ℝ) = 1 := by 
      norm_num [Real.logb_eq_iff_rpow_eq]
    rw [h1] at eq3
    rw [h2] at eq3 
    linarith 
  linarith