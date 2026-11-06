import Mathlib

theorem algebra_7364 : Real.sqrt 3 * 5 * Real.sqrt 5 * Real.sqrt 3 = 15 * Real.sqrt 5 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  calc
    Real.sqrt 3 * 5 * Real.sqrt 5 * Real.sqrt 3 
      = 5 * (Real.sqrt 3 * Real.sqrt 3) * Real.sqrt 5 := by 
        ring
    _ = 5 * 3 * Real.sqrt 5 := by
      rw [show Real.sqrt 3 * Real.sqrt 3 = 3 by
        nlinarith [h1]]
      all_goals nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5]
    _ = 15 * Real.sqrt 5 := by
      ring