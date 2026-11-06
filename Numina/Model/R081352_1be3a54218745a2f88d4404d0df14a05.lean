import Mathlib

open Finset Real

theorem algebra_136987 : ∏ i ∈ Icc 2 100, ((i - 1) * (i ^ 2 + i + 1)) / ((i + 1) * (i ^ 2 - i + 1)) = 3367 / 5050 := by
  native_decide