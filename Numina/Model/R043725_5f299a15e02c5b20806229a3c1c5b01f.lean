import Mathlib

open Finset

theorem number_theory_133428 : (Nat.digits 10 (∑ i ∈ Icc 1 2017, Nat.factorial i)).length > 1 ∧
    (Nat.digits 10 (∑ i ∈ Icc 1 2017, Nat.factorial i))[1]! = 1 := by
  constructor
  · -- Show that the length of the digits is greater than 1
    native_decide
  · -- Show that the tens digit is 1
    native_decide