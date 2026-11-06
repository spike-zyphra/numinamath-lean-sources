import Mathlib

open Finset

theorem number_theory_609109 :
    #{k ∈ Finset.Icc 1 2013 | k ^ k ≡ 1 [MOD 10]} = 202 := by
  native_decide