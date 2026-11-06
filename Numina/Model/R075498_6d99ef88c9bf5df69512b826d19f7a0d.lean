import Mathlib

open Real Set
open scoped Real

theorem inequalities_188525 : (1 + sqrt 3) / 2 > 49 / 36 := by

  have h1 : sqrt 3 > 31 / 18 := by
    have h2 : (31 / 18 : ℝ) ^ 2 < (3 : ℝ) := by 
      norm_num
    have h3 : (31 / 18 : ℝ) < sqrt 3 := by
      apply Real.lt_sqrt_of_sq_lt 
      linarith 
    linarith 
  have h4 : (1 + sqrt 3) / 2 > (1 + (31 / 18 : ℝ)) / 2 := by 
    linarith [h1] 
  have h5 : (1 + (31 / 18 : ℝ)) / 2 = 49 / 36 := by 
    norm_num 
  linarith [h4, h5]
  all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
  all_goals norm_num
  all_goals nlinarith
  all_goals norm_num