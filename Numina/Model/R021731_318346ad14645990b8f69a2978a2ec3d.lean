import Mathlib

theorem algebra_5295 {K : ℝ} (hK : K ≥ 0) (h : Real.sqrt K = Real.sqrt (13 + Real.sqrt 69) - Real.sqrt (13 - Real.sqrt 69)) :
    K = 6 := by 
  have h1 : Real.sqrt K ≥ 0 := by apply Real.sqrt_nonneg
  have h2 : Real.sqrt (13 + Real.sqrt 69) ≥ 0 := by apply Real.sqrt_nonneg
  have h3 : Real.sqrt (13 - Real.sqrt 69) ≥ 0 := by apply Real.sqrt_nonneg
  have h4 : K = (Real.sqrt (13 + Real.sqrt 69) - Real.sqrt (13 - Real.sqrt 69)) ^ 2 := by 
    calc 
      K = (Real.sqrt K) ^ 2 := by rw [Real.sq_sqrt hK]
      _ = (Real.sqrt (13 + Real.sqrt 69) - Real.sqrt (13 - Real.sqrt 69)) ^ 2 := by rw [h]
  have h5 : (Real.sqrt (13 + Real.sqrt 69) - Real.sqrt (13 - Real.sqrt 69)) ^ 2
    = (Real.sqrt (13 + Real.sqrt 69)) ^ 2 + (Real.sqrt (13 - Real.sqrt 69)) ^ 2 - 2 * (Real.sqrt (13 + Real.sqrt 69) * Real.sqrt (13 - Real.sqrt 69)) := by ring 
  have h6 : (Real.sqrt (13 + Real.sqrt 69)) ^ 2 = 13 + Real.sqrt 69 := by 
    rw [Real.sq_sqrt]
    have h8 : 0 ≤ (13 + Real.sqrt 69 : ℝ) := by
      have h9 : 0 ≤ (Real.sqrt 69 : ℝ) := Real.sqrt_nonneg 69
      nlinarith [Real.sqrt_nonneg 69, show (69 : ℝ) ≥ 0 by norm_num]
    linarith 
  have h7 : (Real.sqrt (13 - Real.sqrt 69)) ^ 2 = 13 - Real.sqrt 69 := by 
    rw [Real.sq_sqrt]
    have h8 : 0 ≤ (13 - Real.sqrt 69 : ℝ) := by 
      have h5 : Real.sqrt 69 ≤ (13 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg 69, Real.sq_sqrt (show (0 : ℝ) ≤ (69 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_nonneg 69, Real.sq_sqrt (show (0 : ℝ) ≤ (69 : ℝ) by norm_num)]
    linarith 
  have h8 : Real.sqrt (13 + Real.sqrt 69) * Real.sqrt (13 - Real.sqrt 69) = (10 : ℝ) := by
    have h9 : Real.sqrt (13 + Real.sqrt 69) * Real.sqrt (13 - Real.sqrt 69) = Real.sqrt ((13 + Real.sqrt 69) * (13 - Real.sqrt 69)) := by
      rw [← Real.sqrt_mul (by
        have h8 : 0 ≤ (13 + Real.sqrt 69 : ℝ) := by
          have h9 : 0 ≤ (Real.sqrt 69 : ℝ) := Real.sqrt_nonneg 69
          nlinarith [Real.sqrt_nonneg 69, show (69 : ℝ) ≥ 0 by norm_num]
        have h9' : 0 ≤ (13 - Real.sqrt 69 : ℝ) := by 
          have h5 : Real.sqrt 69 ≤ (13 : ℝ) := by 
            nlinarith [Real.sqrt_nonneg 69, Real.sq_sqrt (show (0 : ℝ) ≤ (69 : ℝ) by norm_num)]
          nlinarith [Real.sqrt_nonneg 69, Real.sq_sqrt (show (0 : ℝ) ≤ (69 : ℝ) by norm_num)]
        nlinarith [Real.sqrt_nonneg 69, show (69 : ℝ) ≥ 0 by norm_num]
      )]
      all_goals norm_num [Real.sqrt_mul]
    have h10 : (13 + Real.sqrt 69) * (13 - Real.sqrt 69) = (100 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 69, Real.sq_sqrt (show (0 : ℝ) ≤ (69 : ℝ) by norm_num)]
    have h11 : Real.sqrt ((13 + Real.sqrt 69) * (13 - Real.sqrt 69)) = (10 : ℝ) := by
      rw [h10]
      have h12 : Real.sqrt ((100 : ℝ) : ℝ) = 10 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      exact h12 
    rw [h9, h11]
  have h13 : (Real.sqrt (13 + Real.sqrt 69) - Real.sqrt (13 - Real.sqrt 69)) ^ 2 = (6 : ℝ) := by
    rw [h5, h6, h7, h8]
    all_goals nlinarith [Real.sqrt_nonneg 69, Real.sq_sqrt (show (0 : ℝ) ≤ (69 : ℝ) by norm_num)]
  rw [h4, h13]
  all_goals nlinarith