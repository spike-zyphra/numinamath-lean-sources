import Mathlib

open Nat

theorem number_theory_15038 : ((Nat.divisors (8 !)).filter fun n => 7 ! < n).card = 7 := by 
  native_decide