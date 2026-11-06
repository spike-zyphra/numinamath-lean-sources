import Mathlib

open Finset

/-
Theorem: The number of ways to mark 5 stones out of 15 arranged in a line such that there are an odd number of stones between any two marked stones is 77.
-/
theorem combinatorics_608566 : 
    ∑ x ∈ range 2 , 
    Nat.choose (8 - x) 5 = 77 := by
    
  simp [Finset.sum_range_succ, Nat.choose_succ_succ, Nat.choose_succ_succ]