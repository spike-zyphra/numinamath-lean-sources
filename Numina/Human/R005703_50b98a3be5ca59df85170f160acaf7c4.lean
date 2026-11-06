import Mathlib

open Finset Real Nat
/- Let A denote the set of all integers n such that 1≤n≤10000, 
and moreover the sum of the decimal digits of n is 2. Find the sum of the squares of the elements of A -/
theorem algebra_609497:  ∑ i ∈  Finset.range 4, ∑ j ∈  Finset.Icc i 3, (10^i + 10^j)^2 =  7294927 := by
  simp [sum_range_succ]
  simp [Finset.sum_Icc_succ_top]
  