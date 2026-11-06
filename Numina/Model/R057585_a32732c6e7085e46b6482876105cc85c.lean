import Mathlib

theorem algebra_145710 : ((Real.sqrt (Real.sqrt 2) ^ 2) ^ 2) = 2 := by
  have h1 : (Real.sqrt (Real.sqrt 2) ^ 2) = Real.sqrt 2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [h1]
  rw [Real.sq_sqrt]
  all_goals positivity