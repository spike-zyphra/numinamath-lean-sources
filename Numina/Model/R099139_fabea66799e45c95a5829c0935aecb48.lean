import Mathlib

open Real

theorem inequalities_101127 (x y : ℝ) (hy : 5 ≤ y) :
    x^2 - 2 * x * sqrt (y - 5) + y^2 + y - 30 ≥ 0 := by
  have h1 : (sqrt (y - 5)) ^ 2 = y - 5 := by
    rw [Real.sq_sqrt]
    linarith
  have h2 : x^2 - 2 * x * sqrt (y - 5) + y^2 + y - 30 
    = (x - sqrt (y - 5)) ^ 2 + (y ^ 2 - 25) := by
    calc
      x^2 - 2 * x * sqrt (y - 5) + y^2 + y - 30 
        = (x - sqrt (y - 5)) ^ 2 - (sqrt (y - 5) ^ 2) + y^2 + y - 30 := by 
          ring
      _ = (x - sqrt (y - 5)) ^ 2 - (y - 5) + y^2 + y - 30 := by 
        rw [h1]
      _ = (x - sqrt (y - 5)) ^ 2 + (y ^ 2 - 25) := by 
        ring
  rw [h2]
  have h3 : (x - sqrt (y - 5)) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h4 : y ^ 2 - 25 ≥ 0 := by
    have h5 : (y - 5) * (y + 5) ≥ 0 := by
      apply mul_nonneg
      · linarith
      · linarith
    have h6 : y ^ 2 - 25 = (y - 5) * (y + 5) := by
      ring
    linarith [h6, h5]
  linarith [h3, h4]