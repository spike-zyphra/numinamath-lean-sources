import Mathlib

open Finset Real

theorem algebra_117955 : ∑ i ∈ range 100, ((i + 1)^2 + (i + 2)^2) / ((i + 1) * (i + 2)) = 200 + 100 / 101 := by
  native_decide