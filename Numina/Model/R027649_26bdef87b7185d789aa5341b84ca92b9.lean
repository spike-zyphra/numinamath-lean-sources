import Mathlib

theorem algebra_157101 (k : ℝ) (h : k ≠ 0) (h1 : (1 / 2) * k * (5 / 100)^2 = 29.43) :
    ∃ x, (1 / 2) * k * (x / 100)^2 = 9.81 := by
  have hk : k = (23544 : ℝ) := by
    norm_num at h1 
    linarith
  use 100 * Real.sqrt (9.81 / (k : ℝ) * 2)
  rw [hk]
  have eq1 : (1 / 2) * (23544 : ℝ) * ( (100 * Real.sqrt (9.81 / (23544 : ℝ) * 2) ) / 100 )^2 = 9.81 := by
    have h2 : (Real.sqrt (9.81 / (23544 : ℝ) * 2) )^2 = 9.81 / (23544 : ℝ) * 2 := by 
      rw [Real.sq_sqrt]
      positivity
    calc 
      (1 / 2) * (23544 : ℝ) * ( (100 * Real.sqrt (9.81 / (23544 : ℝ) * 2) ) / 100 )^2 
          = (1 / 2) * (23544 : ℝ) * (Real.sqrt (9.81 / (23544 : ℝ) * 2) )^2 := by 
            ring_nf
      _ = (1 / 2) * (23544 : ℝ) * (9.81 / (23544 : ℝ) * 2) := by 
        rw [h2]
      _ = 9.81 := by
        norm_num
  linarith [eq1]