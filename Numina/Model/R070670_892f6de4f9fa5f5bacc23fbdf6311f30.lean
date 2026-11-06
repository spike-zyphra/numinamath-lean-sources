import Mathlib

theorem algebra_2421 {a b : ℝ} (ha : a + b = Real.sqrt (Real.sqrt 1992 + Real.sqrt 1991))
    (hb : a - b = Real.sqrt (Real.sqrt 1992 - Real.sqrt 1991)) :
    a * b = Real.sqrt 1991 / 2 := by
  have eq1 : (a + b) ^ 2 = Real.sqrt 1992 + Real.sqrt 1991 := by 
    calc 
      (a + b) ^ 2 = (Real.sqrt (Real.sqrt 1992 + Real.sqrt 1991)) ^ 2 := by rw [ha]
      _ = Real.sqrt 1992 + Real.sqrt 1991 := by 
        rw [Real.sq_sqrt]
        positivity
  have eq2 : (a - b) ^ 2 = Real.sqrt 1992 - Real.sqrt 1991 := by
    calc 
      (a - b) ^ 2 = (Real.sqrt (Real.sqrt 1992 - Real.sqrt 1991)) ^ 2 := by rw [hb]
      _ = Real.sqrt 1992 - Real.sqrt 1991 := by 
        rw [Real.sq_sqrt]
        have h1 : Real.sqrt 1992 ≥ Real.sqrt 1991 := by 
          apply Real.sqrt_le_sqrt (by norm_num)
        have h2 : Real.sqrt 1992 - Real.sqrt 1991 ≥ 0 := by linarith
        linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), 
          Real.sqrt_nonneg (Real.sqrt 1992 + Real.sqrt 1991), 
          Real.sqrt_nonneg (Real.sqrt 1992 - Real.sqrt 1991), 
          Real.sqrt_nonneg (Real.sqrt 1992 : ℝ), Real.sqrt_nonneg (Real.sqrt 1991 : ℝ),
          Real.sq_sqrt (show 0 ≤ 1992 by norm_num), 
          Real.sq_sqrt (show 0 ≤ 1991 by norm_num),
          mul_nonneg (Real.sqrt_nonneg 1992) (Real.sqrt_nonneg 1991)
          ]