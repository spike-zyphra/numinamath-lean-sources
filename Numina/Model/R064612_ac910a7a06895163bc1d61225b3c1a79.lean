import Mathlib

theorem algebra_112119 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h₀ : a > b)
    (h₁ : (a + b) / 2 = 2 * Real.sqrt 3) (h₂ : Real.sqrt (a * b) = Real.sqrt 3) :
    a - b = 6 := by
  have h3 : a + b = 4 * Real.sqrt 3 := by
    linarith
  
  have h4 : a * b = 3 := by 
    calc 
      a * b = (Real.sqrt (a * b)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (Real.sqrt 3) ^ 2 := by rw [h₂]
      _ = 3 := by 
        norm_num
  
  have h5 : (a + b) ^ 2 = 48 := by
    calc 
      (a + b) ^ 2 = (4 * Real.sqrt 3) ^ 2 := by rw [h3]
      _ = 16 * (Real.sqrt 3) ^ 2 := by ring
      _ = 16 * 3 := by 
        rw [Real.sq_sqrt]
        norm_num
      _ = 48 := by norm_num
  
  have h6 : (a - b) ^ 2 = 36 := by
    nlinarith [h5, h4]

  have h7 : a - b > 0 := by linarith [h₀]

  nlinarith [h6, h7]