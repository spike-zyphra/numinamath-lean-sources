import Mathlib

open Real

theorem algebra_129467 : (1 / ((3 + sqrt 2) * (2 + sqrt 3) * (3 - sqrt 2) * (2 - sqrt 3))) = 1 / 7 := by
  have h1 : (3 + sqrt 2) * (3 - sqrt 2) = 7 := by
    have h2 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    nlinarith
  
  have h3 : (2 + sqrt 3) * (2 - sqrt 3) = 1 := by
    have h4 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    nlinarith
  
  have h5 : ((3 + sqrt 2) * (2 + sqrt 3) * (3 - sqrt 2) * (2 - sqrt 3)) = 7 := by
    calc
      ((3 + sqrt 2) * (2 + sqrt 3) * (3 - sqrt 2) * (2 - sqrt 3)) 
          = ((3 + sqrt 2) * (3 - sqrt 2)) * ((2 + sqrt 3) * (2 - sqrt 3)) := by ring
      _ = 7 * 1 := by rw [h1, h3]
      _ = 7 := by norm_num

  rw [h5]
  all_goals norm_num