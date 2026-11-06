import Mathlib

open Finset Real

theorem algebra_137042 : ∏ i ∈ Icc 2 200, ((i ^ 3 - 1) / (i ^ 3 + 1)) = 40201 / 60300 := by
  native_decide