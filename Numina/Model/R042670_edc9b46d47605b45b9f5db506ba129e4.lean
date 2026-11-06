import Mathlib

open Finset Nat

theorem number_theory_608373 : ((Icc 1 1997).filter (fun n => Nat.gcd n 1547 = 1)).card = 1487 := by 
  native_decide