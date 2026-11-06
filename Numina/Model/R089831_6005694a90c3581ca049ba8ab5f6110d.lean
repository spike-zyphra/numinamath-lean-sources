import Mathlib

open Finset Real Nat

theorem algebra_185167 : ∑ i ∈ range 2001, (i + 1) / (i ! + (i + 1) ! + (i + 2) !) = 1 / 2 - 1 / 2001! := by
  native_decide