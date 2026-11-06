import Mathlib

theorem algebra_244402 (A : ℝ × ℝ) (hA : A ≠ (3, 6)) (h : Real.sqrt (A.1^2 + A.2^2) = (Real.sqrt ((A.1 - 3)^2 + (A.2 - 6)^2)) / 2) :
    (A.1 + 1)^2 + (A.2 + 2)^2 = 20 := by
  have h1 : (Real.sqrt (A.1^2 + A.2^2)) ^ 2 = ((Real.sqrt ((A.1 - 3)^2 + (A.2 - 6)^2)) / 2) ^ 2 := by 
    rw [h]
  have h2 : (Real.sqrt (A.1^2 + A.2^2)) ^ 2 = A.1^2 + A.2^2 := by
    rw [Real.sq_sqrt]
    all_goals nlinarith
  have h3 : ((Real.sqrt ((A.1 - 3)^2 + (A.2 - 6)^2)) / 2) ^ 2 = ((Real.sqrt ((A.1 - 3)^2 + (A.2 - 6)^2)) ^ 2) / 4 := by 
    ring_nf
  have h4 : (Real.sqrt ((A.1 - 3)^2 + (A.2 - 6)^2)) ^ 2 = (A.1 - 3)^2 + (A.2 - 6)^2 := by 
    rw [Real.sq_sqrt]
    all_goals nlinarith
  rw [h2] at h1
  rw [h3, h4] at h1
  nlinarith [sq_nonneg (A.1 + 1), sq_nonneg (A.2 + 2)]