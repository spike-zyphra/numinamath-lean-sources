import Mathlib

open Finset Real Nat

/-Joana wrote positive integers on the blackboard and then erased all multiples of 7 and 11.
Determine the number that remained in the 61st position. Show the answer is 78.-/

theorem number_theory_640630: ((Icc 1 78).filter (fun x => x % 7 != 0 && x % 11 != 0)).card = 61 := by

  native_decide