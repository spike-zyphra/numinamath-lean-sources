import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_16721 :
    {t : ℝ | (t - 1) ^ 2 + (t + 1) ^ 2 ≠ 0} = Set.univ := by 
  ext t 
  simp 
  have h : (t - 1 : ℝ) ^ 2 + (t + 1 : ℝ) ^ 2 > 0 := by 
    nlinarith [sq_nonneg (t : ℝ)]
  linarith