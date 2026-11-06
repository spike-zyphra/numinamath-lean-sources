import Mathlib

set_option maxRecDepth 10000

open Finset

/-
Problem: For a string of $P$'s and $Q$'s of length 2004, the value is defined to be the product of the positions of the $P$'s. A string is called antipalindromic if reversing it and swapping $P$'s with $Q$'s produces the original string. Find the sum of the reciprocals of the values of all antipalindromic strings of length 2004.
-/
theorem combinatorics_611278 
    (N : n = 1002) : 
    ∏ x ∈ range n , 
    (1 / (x + 1) + 1 / (2 * n - x) : ℝ) = 2005 ^ 1002 / (2004).factorial := by 

  have t₁ : ∏ x ∈ range n , 
  (1 / (x + 1) + 1 / (2 * n - x) : ℝ) = (2 * n + 1) ^ n / (2 * n).factorial := by 
    rw [N]
    norm_num [Finset.prod_range_succ, Nat.factorial]

  rw [t₁,N]
  
  norm_num
