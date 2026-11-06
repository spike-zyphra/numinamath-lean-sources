import Mathlib

theorem algebra_148107 : (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by
  have h1 : Real.sqrt 2 ^ 2 = 2 := by
    exact Real.sq_sqrt (by norm_num)
  nlinarith [h1]