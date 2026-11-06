import Mathlib

open Finset

theorem number_theory_133428 : (Nat.digits 10 (∑ i ∈ Icc 1 2017, Nat.factorial i)).length > 1 ∧
    (Nat.digits 10 (∑ i ∈ Icc 1 2017, Nat.factorial i))[1]! = 1 := by native_decide