import Mathlib

theorem algebra_207509 {x y : ℝ} (h₀ : (x + y) / 2 = 8) (h₁ : Real.sqrt (x * y) = 2 * Real.sqrt 5) :
    x ^ 2 + y ^ 2 = 216 := by 
  have h2 : x + y = 16 := by 
    linarith
  have h3 : 0 ≤ x * y := by
    by_contra h
    push_neg at h
    have h4 : Real.sqrt (x * y) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      linarith
      all_goals linarith
    rw [h4] at h₁
    have h5 : Real.sqrt 5 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals norm_num
    have h6 : (2 * Real.sqrt 5) > 0 := by
      positivity
    nlinarith
  have h4 : (Real.sqrt (x * y)) ^ 2 = (2 * Real.sqrt 5) ^ 2 := by 
    rw [h₁]
  have h5 : (Real.sqrt (x * y)) ^ 2 = x * y := by 
    rw [Real.sq_sqrt]
    linarith
  have h6 : (2 * Real.sqrt 5) ^ 2 = 20 := by 
    calc
      (2 * Real.sqrt 5) ^ 2 = 4 * (Real.sqrt 5) ^ 2 := by ring
      _ = 4 * 5 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      _ = 20 := by norm_num
  have h7 : x * y = 20 := by
    nlinarith [h4, h5, h6]
  have h8 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    linarith
  rw [h8, h2, h7]
  all_goals norm_num