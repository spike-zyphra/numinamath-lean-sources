import Mathlib
/-
If no one shares an office, in how many ways can 3 people be assigned to 5 different offices? (Each person gets exactly one office).-/
open Nat

theorem algebra_3951 {n m : ℕ} (hn : n = 3) (hm : m = 5) :

    n ! * m.choose n = 60 := by 
  subst hn
  subst hm
  rfl