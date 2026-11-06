import Mathlib

open Finset Nat

/-
How many positive integers less than 1998 are relatively prime to 1547 ? (Two integers are relatively prime if they have no common factors besides 1.)
-/
theorem number_theory_608373 : ((Icc 1 1997).filter (fun n => Nat.gcd n 1547 = 1)).card = 1487 := by
  native_decide