import Mathlib

open Finset Real Nat

theorem algebra_312075 : ∑ i ∈ range 2001, (i + 1) / (∑ j ∈ range 3, (i + j) !) = 1 / 2 - 1 / 2001 ! := by
  native_decide