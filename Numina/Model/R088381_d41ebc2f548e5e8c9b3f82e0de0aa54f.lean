import Mathlib

theorem algebra_225100 {x : ℝ} (hx : x = √2 + √3) :
    x^4 - 10 * x^2 + 1 = 0 := by 
  rw [hx]
  have h1 : (√2 + √3) ^ 2 = 5 + 2 * √6 := by
    calc
      (√2 + √3) ^ 2 = (√2) ^ 2 + (√3) ^ 2 + 2 * (√2 * √3) := by ring
      _ = 2 + 3 + 2 * (√2 * √3) := by simp [Real.sq_sqrt]
      _ = 5 + 2 * (√2 * √3) := by ring
      _ = 5 + 2 * (√2 * √3) := by ring
      _ = 5 + 2 * √6 := by
        have h2 : √2 * √3 = √6 := by
          have h3 : √6 = √(2 * 3) := by norm_num [Real.sqrt_mul]
          rw [h3]
          rw [Real.sqrt_mul (by norm_num)]
          all_goals norm_num
          all_goals norm_num [Real.sqrt_mul]
        rw [h2]
  
  have h3 : (√2 + √3) ^ 4 = (5 + 2 * √6) ^ 2 := by 
    calc 
      (√2 + √3) ^ 4 = ((√2 + √3) ^ 2) ^ 2 := by ring
      _ = (5 + 2 * √6) ^ 2 := by rw [h1]
  
  have h4 : (√6) ^ 2 = 6 := by 
    rw [Real.sq_sqrt]
    norm_num
  
  nlinarith [h3, h1, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 6, h4, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]