import Mathlib

theorem algebra_102928 (x : ℝ) (hx : x ≥ -56) (h : Real.sqrt (x + 77) = Real.sqrt (x + 56) + 1) :
    x = 44 := by
  have h2 : (Real.sqrt (x + 77)) ^ 2 = (Real.sqrt (x + 56) + 1) ^ 2 := by
    rw [h]
  have h3 : (Real.sqrt (x + 77)) ^ 2 = x + 77 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : (Real.sqrt (x + 56) + 1) ^ 2 = (Real.sqrt (x + 56)) ^ 2 + 2 * Real.sqrt (x + 56) + 1 := by ring
  have h5 : (Real.sqrt (x + 56)) ^ 2 = x + 56 := by
    rw [Real.sq_sqrt]
    linarith
  rw [h3, h4, h5] at h2
  have h6 : Real.sqrt (x + 56) = 10 := by
    nlinarith 
  have h7 : x + 56 = 100 := by
    calc
      x + 56 = (Real.sqrt (x + 56)) ^ 2 := by rw [Real.sq_sqrt]; linarith
      _ = 10 ^ 2 := by rw [h6]
      _ = 100 := by norm_num
  linarith
  all_goals linarith