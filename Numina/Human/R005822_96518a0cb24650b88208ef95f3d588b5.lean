import Mathlib

open Finset

/-Compute the sum of all positive integers n<2048 such that 
n has an even number of 1 's in its binary representation.-/

theorem combinatorics_610063 :
  ∑ n ∈ (Ico 1 2048).filter (fun n => Even ((List.range (Nat.digits 2 n).length).filter
    (fun i => (Nat.digits 2 n).get? i = some 1)).length), n = 1048064 := by

  native_decide