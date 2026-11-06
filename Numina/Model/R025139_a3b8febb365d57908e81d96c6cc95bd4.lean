import Mathlib
open Real

theorem algebra_1448 {x : ℝ} (hx : x = √3 + √2) : 2*x^5+x^4-20*x^3-10*x^2+2*x+1 = 0 := by
  rw [hx]
  have h1 : (√3 : ℝ) ^ 2 = 3 := by
    exact sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h2 : (√2 : ℝ) ^ 2 = 2 := by
    exact sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h5 : (√3 + √2 : ℝ) ^ 2 = 5 + 2 * √6 := by 
    have h6' : (√3 : ℝ) * (√2 : ℝ) = √6 := by 
      have h6'' : (√3 : ℝ) * (√2 : ℝ) = √(3 * (2 : ℝ)) := by 
        rw [← Real.sqrt_mul (by norm_num)]
      have h7 : (3 * (2 : ℝ)) = (6 : ℝ) := by linarith 
      rw [h7] at h6'' 
      exact h6''
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 6, sq_nonneg (√3 - √2), h1, h2, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)]
  have h6 : (√3 + √2 : ℝ) ^ 4 = 49 + 20 * √6 := by
    calc 
      (√3 + √2 : ℝ) ^ 4 = ((√3 + √2 : ℝ) ^ 2) ^ 2 := by ring 
      _ = (5 + 2 * √6) ^ 2 := by rw [h5] 
      _ = 49 + 20 * √6 := by
        have eq12 : (√6 : ℝ) ^ 2 = 6 := by 
          rw [Real.sq_sqrt] 
          all_goals norm_num 
        nlinarith [Real.sqrt_nonneg 6, eq12, sq_nonneg (√6 - 3)]
  
  have eq8' : (√3 + √2 : ℝ) ^ 4 - 10 * ((√3 + √2 : ℝ) ^ 2) + 1 = 0 := by
    rw [show (√3 + √2 : ℝ) ^ 4 = 49 + 20 * √6 by linarith [h6], 
      show (√3 + √2 : ℝ) ^ 2 = 5 + 2 * √6 by linarith [h5]]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, h1, h2, sq_nonneg (√3 - √2), sq_nonneg (√3 + √2 - 2 * 1), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (√6 - 2)]
  
  have eq5 : (2 * (√3 + √2 : ℝ) ^ 5 + (√3 + √2 : ℝ) ^ 4 - 20 * (√3 + √2 : ℝ) ^ 3 - 10 * (√3 + √2 : ℝ) ^ 2 + 2 * (√3 + √2 : ℝ) + 1 : ℝ) = 0 := by
    have eq9 : (2 * (√3 + √2 : ℝ) ^ 5 + (√3 + √2 : ℝ) ^ 4 - 20 * (√3 + √2 : ℝ) ^ 3 - 10 * (√3 + √2 : ℝ) ^ 2 + 2 * (√3 + √2 : ℝ) + 1 : ℝ) = (2 * (√3 + √2 : ℝ) + 1) * ((√3 + √2 : ℝ) ^ 4 - 10 * ((√3 + √2 : ℝ) ^ 2) + 1) := by 
      ring_nf
      <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, h1, h2, sq_nonneg (√3 - √2), sq_nonneg (√3 + √2), Real.sqrt_nonneg 6, sq_nonneg (√6 - √2), sq_nonneg (√6 - √3)]
    rw [eq9]
    rw [eq8']
    all_goals norm_num
  
  linarith