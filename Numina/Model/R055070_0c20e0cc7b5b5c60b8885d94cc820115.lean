import Mathlib

open Real
open scoped BigOperators

theorem algebra_3234 : ∑ n : ℕ in Finset.Icc 1 10, (1 / ((n+1)*(n+2)*(n+3)*(n+4) : ℝ)) = 5/364 := by 
  norm_num [Finset.sum_Icc_succ_top]