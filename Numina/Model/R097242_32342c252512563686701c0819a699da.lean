import Mathlib

open Finset Real Nat

theorem algebra_204769 : ∑ i ∈ Icc 3 2004, (i / ((i - 2) ! + (i - 1) ! + i !)) = 1 / 2 - 1 / 2004 ! := by 
  native_decide