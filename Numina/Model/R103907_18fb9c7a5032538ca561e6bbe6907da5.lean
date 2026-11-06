import Mathlib

theorem algebra_296975 {a b : ℝ} (h : a + b = Real.sqrt 5) :
    (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 + a * b + b ^ 2) + 3 * a * b = 5 := by
  have h1 : (a + b) ^ 2 = 5 := by
    rw [h]
    calc
      (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      _ = 5 := by norm_num
  
  have h2 : a ^ 2 + a * b + b ^ 2 ≠ 0 := by
    by_contra h3
    have h4 : a + b > 0 := by
      have h5 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0)
      linarith [h, h5]
    
    have h6 : a ^ 2 + a * b + b ^ 2 > 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - (Real.sqrt 5)), sq_nonneg (a), sq_nonneg (b), Real.sqrt_pos.mpr (show (5:ℝ) > 0 by norm_num : (5 : ℝ) > 0)]
    
    linarith [h3, h6]

  have eq1 : (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) / (a ^ 2 + a * b + b ^ 2) = a ^ 2 + b ^ 2 - a * b := by
    field_simp [h2]
    ring

  rw [eq1]
  nlinarith [h1]